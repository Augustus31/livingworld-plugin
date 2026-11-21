package plugin;

import com.comphenix.protocol.PacketType;
import com.comphenix.protocol.ProtocolLibrary;
import com.comphenix.protocol.ProtocolManager;
import com.comphenix.protocol.events.ListenerPriority;
import com.comphenix.protocol.events.PacketAdapter;
import com.comphenix.protocol.events.PacketContainer;
import com.comphenix.protocol.events.PacketEvent;
import com.destroystokyo.paper.event.server.ServerTickEndEvent;

import org.bukkit.Bukkit;
import org.bukkit.ChatColor;
import org.bukkit.Chunk;
import org.bukkit.GameMode;
import org.bukkit.Location;
import org.bukkit.Material;
import org.bukkit.Particle;
import org.bukkit.World;
import org.bukkit.block.Biome;
import org.bukkit.command.Command;
import org.bukkit.command.CommandExecutor;
import org.bukkit.command.CommandSender;
import org.bukkit.command.PluginCommand;
import org.bukkit.command.TabCompleter;
import org.bukkit.configuration.file.FileConfiguration;
import org.bukkit.entity.Player;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.HandlerList;
import org.bukkit.event.Listener;
import org.bukkit.event.player.PlayerChangedWorldEvent;
import org.bukkit.event.player.PlayerJoinEvent;
import org.bukkit.event.player.PlayerQuitEvent;
import org.bukkit.event.player.PlayerRespawnEvent;
import org.bukkit.event.player.PlayerTeleportEvent;
import org.bukkit.event.weather.LightningStrikeEvent;
import org.bukkit.event.weather.ThunderChangeEvent;
import org.bukkit.event.weather.WeatherChangeEvent;
import org.bukkit.event.world.WorldLoadEvent;
import org.bukkit.event.world.WorldUnloadEvent;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.scheduler.BukkitTask;
import org.spigotmc.event.player.PlayerSpawnLocationEvent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.atomic.AtomicBoolean;

/** Five-state server weather and per-player weather appearance for Paper 1.18.2. */
public final class Weather implements Listener, CommandExecutor, TabCompleter {
    private static final String PATH = "custom-weather.worlds.";
    private static final long STARTUP_CLEAR_TICKS = 3600L;
    private static final int VISUAL_TRANSITION_TICKS = 100;
    // Chance of at least one additional 1-in-5000 trial in a 20-tick interval.
    private static final double EXTRA_LIGHTNING_CHANCE = 1.0 - Math.pow(1.0 - 1.0 / 25_000.0, 20);
    private static volatile Weather activeWeather;
    private final JavaPlugin plugin;
    private final Map<UUID, Cycle> worlds = new HashMap<>();
    private final Map<UUID, VisualTransition> playerVisuals = new HashMap<>();
    private final Set<UUID> managedPlayers = ConcurrentHashMap.newKeySet();
    private final AtomicBoolean interceptionErrorLogged = new AtomicBoolean();
    private PacketBridge packets;
    private PacketAdapter weatherListener;
    private boolean registered;
    private BukkitTask task;
    private boolean applyingWeather;
    private int ticks;
    private long weatherTicks;
    private final Map<UUID, TridentOverride> tridents = new HashMap<>();
    private static final Set<UUID> tridentRainWorlds = ConcurrentHashMap.newKeySet();

    public static boolean tridentRainActive(World world) {
        return world != null && tridentRainWorlds.contains(world.getUID());
    }

    private void setTridentRain(World world, boolean active) {
        boolean changed =
                active
                        ? tridentRainWorlds.add(world.getUID())
                        : tridentRainWorlds.remove(world.getUID());
        if (changed) Seasons.tridentRainChanged(world, active);
    }

    private boolean packetErrorLogged;
    private boolean spawningExtraLightning;

    public Weather(JavaPlugin plugin) {
        this.plugin = plugin;
    }

    public void register() {
        if (registered) throw new IllegalStateException("Weather is already registered.");
        if (!"1.18.2".equals(plugin.getServer().getMinecraftVersion())) {
            throw new IllegalStateException(
                    "This Weather implementation requires Minecraft 1.18.2.");
        }
        PluginCommand command = plugin.getCommand("weather");
        if (command == null)
            throw new IllegalStateException("The weather command is missing from plugin.yml.");
        if (!Bukkit.getPluginManager().isPluginEnabled("ProtocolLib")) {
            throw new IllegalStateException(
                    "Weather requires ProtocolLib. Add depend: [ProtocolLib] to plugin.yml.");
        }
        packets = new PacketBridge(ProtocolLibrary.getProtocolManager());
        weatherListener =
                new PacketAdapter(
                        plugin,
                        ListenerPriority.HIGHEST,
                        PacketType.Play.Server.GAME_STATE_CHANGE) {
                    @Override
                    public void onPacketSending(PacketEvent event) {
                        interceptWeather(event);
                    }
                };
        packets.manager.addPacketListener(weatherListener);
        registered = true;
        activeWeather = this;
        try {
            command.setExecutor(this);
            command.setTabCompleter(this);
            PluginCommand trident = plugin.getCommand("trident");
            if (trident == null) throw new IllegalStateException("Add trident to plugin.yml.");
            trident.setExecutor(this);
            Bukkit.getPluginManager().registerEvents(this, plugin);
            for (World world : Bukkit.getWorlds()) loadWorld(world, true);
            for (Player player : Bukkit.getOnlinePlayers()) refreshPlayer(player);
            task = Bukkit.getScheduler().runTaskTimer(plugin, this::tick, 1L, 1L);
        } catch (RuntimeException exception) {
            packets.manager.removePacketListener(weatherListener);
            HandlerList.unregisterAll(this);
            managedPlayers.clear();
            playerVisuals.clear();
            registered = false;
            if (activeWeather == this) activeWeather = null;
            throw exception;
        }
    }

    private void interceptWeather(PacketEvent event) {
        if (event.isCancelled() || !managedPlayers.contains(event.getPlayer().getUniqueId()))
            return;
        try {
            int reason = event.getPacket().getGameStateIDs().read(0);
            if (isWeatherReason(reason)) event.setCancelled(true);
        } catch (RuntimeException exception) {
            if (interceptionErrorLogged.compareAndSet(false, true)) {
                plugin.getLogger()
                        .severe("Could not intercept vanilla weather packets: " + exception);
            }
        }
    }

    private static boolean isWeatherReason(int reason) {
        return reason == 1 || reason == 2 || reason == 7 || reason == 8;
    }

    public void shutdown() {
        if (!registered) return;
        for (World world : Bukkit.getWorlds()) restoreTrident(world);
        registered = false;
        if (activeWeather == this) activeWeather = null;
        if (task != null) task.cancel();
        HandlerList.unregisterAll(this);
        packets.manager.removePacketListener(weatherListener);
        managedPlayers.clear();
        playerVisuals.clear();
        for (World world : Bukkit.getWorlds()) {
            Cycle cycle = worlds.get(world.getUID());
            if (cycle != null) saveWorld(world, cycle);
        }
        plugin.saveConfig();
        for (Player player : Bukkit.getOnlinePlayers()) {
            if (worlds.containsKey(player.getWorld().getUID())) {
                sendVisual(
                        player,
                        player.getWorld().hasStorm() ? 1.0f : 0.0f,
                        player.getWorld().isThundering() ? 1.0f : 0.0f);
            }
        }
        worlds.clear();
    }

    @Override
    public boolean onCommand(CommandSender sender, Command command, String label, String[] args) {
        if (command.getName().equalsIgnoreCase("trident")) {
            if (args.length > 1) {
                sender.sendMessage("Usage: /trident [world]");
                return true;
            }
            World world =
                    args.length == 1
                            ? Bukkit.getWorld(args[0])
                            : sender instanceof Player player
                                    ? player.getWorld()
                                    : Bukkit.getWorlds().get(0);
            if (world == null || world.getEnvironment() != World.Environment.NORMAL) {
                sender.sendMessage("Choose a loaded Overworld-type world.");
                return true;
            }
            startTrident(world, true);
            sender.sendMessage("Temporary rain in " + world.getName() + ".");
            return true;
        }
        if (!command.getName().equalsIgnoreCase("weather")) return false;
        if (args.length < 1 || args.length > 3) {
            sender.sendMessage(
                    ChatColor.YELLOW
                            + "Usage: /weather <clear|drizzle|light_rain|rain|thunder|status>"
                            + " [world]");
            return true;
        }
        boolean spacedLightRain =
                args.length >= 2
                        && args[0].equalsIgnoreCase("light")
                        && args[1].equalsIgnoreCase("rain");
        int worldArg = spacedLightRain ? 2 : 1;
        if (args.length > worldArg + 1) {
            sender.sendMessage(
                    ChatColor.YELLOW
                            + "Usage: /weather <clear|drizzle|light_rain|rain|thunder|status>"
                            + " [world]");
            return true;
        }
        boolean status = args[0].equalsIgnoreCase("status");
        final State state;
        try {
            state =
                    status
                            ? null
                            : spacedLightRain
                                    ? State.LIGHT_RAIN
                                    : State.valueOf(args[0].toUpperCase(Locale.ROOT));
        } catch (IllegalArgumentException e) {
            sender.sendMessage(
                    ChatColor.RED + "Choose clear, drizzle, light_rain, rain, thunder, or status.");
            return true;
        }
        World world =
                args.length > worldArg
                        ? Bukkit.getWorld(args[worldArg])
                        : sender instanceof Player player
                                ? player.getWorld()
                                : Bukkit.getWorlds().get(0);
        if (world == null || world.getEnvironment() != World.Environment.NORMAL) {
            sender.sendMessage(ChatColor.RED + "Choose a loaded Overworld-type world.");
            return true;
        }
        Cycle cycle = worlds.get(world.getUID());
        if (cycle == null) {
            loadWorld(world);
            cycle = worlds.get(world.getUID());
        }
        if (status) {
            long remaining = Math.max(0L, cycle.deadline - weatherTicks);
            sender.sendMessage(
                    ChatColor.YELLOW
                            + "Weather in "
                            + world.getName()
                            + ": "
                            + cycle.state.name().toLowerCase(Locale.ROOT)
                            + (cycle.enhanced ? " (enhanced)" : "")
                            + "; target: "
                            + cycle.target.name().toLowerCase(Locale.ROOT)
                            + "; remaining: "
                            + remaining
                            + " ticks.");
            sender.sendMessage(
                    "Backend: rain="
                            + world.hasStorm()
                            + ", thunder="
                            + world.isThundering()
                            + ". Strikes observed this/last storm: natural="
                            + cycle.naturalStrikes
                            + ", extra="
                            + cycle.extraStrikes
                            + ", cancelled="
                            + cycle.cancelledStrikes
                            + ".");
            sender.sendMessage(
                    "Natural lightning settings: disable-thunder="
                            + naturalThunderDisabled(world)
                            + ", thunder-chance="
                            + naturalThunderChance(world)
                            + " (a larger number means fewer strikes).");
            return true;
        }
        setManual(world, cycle, state);
        sender.sendMessage(
                ChatColor.GREEN
                        + "Weather in "
                        + world.getName()
                        + " set to "
                        + state.name().toLowerCase(Locale.ROOT).replace('_', ' ')
                        + (cycle.enhanced ? " (enhanced)" : "")
                        + ".");
        return true;
    }

    @Override
    public List<String> onTabComplete(
            CommandSender sender, Command command, String alias, String[] args) {
        List<String> result = new ArrayList<>();
        if (args.length == 1) {
            String prefix = args[0].toLowerCase(Locale.ROOT);
            if ("status".startsWith(prefix)) result.add("status");
            for (State state : State.values()) {
                String name = state.name().toLowerCase(Locale.ROOT);
                if (name.startsWith(prefix)) result.add(name);
            }
        } else if (args.length == 2) {
            if (args[0].equalsIgnoreCase("light")) {
                if ("rain".startsWith(args[1].toLowerCase(Locale.ROOT))) result.add("rain");
                return result;
            }
            String prefix = args[1].toLowerCase(Locale.ROOT);
            for (World world : Bukkit.getWorlds()) {
                if (world.getEnvironment() == World.Environment.NORMAL
                        && world.getName().toLowerCase(Locale.ROOT).startsWith(prefix))
                    result.add(world.getName());
            }
        } else if (args.length == 3
                && args[0].equalsIgnoreCase("light")
                && args[1].equalsIgnoreCase("rain")) {
            String prefix = args[2].toLowerCase(Locale.ROOT);
            for (World world : Bukkit.getWorlds()) {
                if (world.getEnvironment() == World.Environment.NORMAL
                        && world.getName().toLowerCase(Locale.ROOT).startsWith(prefix))
                    result.add(world.getName());
            }
        }
        return result;
    }

    @EventHandler
    public void onWorldLoad(WorldLoadEvent event) {
        loadWorld(event.getWorld());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onWorldUnload(WorldUnloadEvent event) {
        restoreTrident(event.getWorld());
        Cycle cycle = worlds.remove(event.getWorld().getUID());
        if (cycle != null) {
            saveWorld(event.getWorld(), cycle);
            plugin.saveConfig();
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onWeatherChange(WeatherChangeEvent event) {
        Cycle cycle = worlds.get(event.getWorld().getUID());
        if (!applyingWeather && cycle != null && event.toWeatherState() != cycle.state.rain) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onThunderChange(ThunderChangeEvent event) {
        Cycle cycle = worlds.get(event.getWorld().getUID());
        if (!applyingWeather
                && cycle != null
                && event.toThunderState() != (cycle.state == State.THUNDER)) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onLightningStrike(LightningStrikeEvent event) {
        Cycle cycle = worlds.get(event.getWorld().getUID());
        if (cycle == null || cycle.state != State.THUNDER) return;
        if (event.isCancelled()) cycle.cancelledStrikes++;
        else if (spawningExtraLightning) cycle.extraStrikes++;
        else if (event.getCause() == LightningStrikeEvent.Cause.WEATHER) cycle.naturalStrikes++;
    }

    private void tick() {
        weatherTicks++;
        Set<UUID> heldWorlds = new HashSet<>();
        for (Player player : Bukkit.getOnlinePlayers()) {
            if (player.getInventory().getItemInMainHand().getType() == Material.TRIDENT
                    || player.getInventory().getItemInOffHand().getType() == Material.TRIDENT)
                heldWorlds.add(player.getWorld().getUID());
        }
        for (World world : Bukkit.getWorlds()) {
            Cycle cycle = worlds.get(world.getUID());
            if (cycle == null) continue;
            boolean holding = heldWorlds.contains(world.getUID());
            if (holding) startTrident(world, false);
            TridentOverride override = tridents.get(world.getUID());
            if (override != null) override.holding = holding;
            advance(world, cycle);
        }
        if (++ticks >= 20) {
            ticks = 0;
            for (World world : Bukkit.getWorlds()) {
                Cycle cycle = worlds.get(world.getUID());
                if (cycle != null && cycle.state == State.THUNDER)
                    extraLightning(world, cycle.enhanced);
            }
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onTickEnd(ServerTickEndEvent event) {
        if (!registered) return;
        for (Player player : Bukkit.getOnlinePlayers()) {
            UUID worldId = player.getWorld().getUID();
            Cycle cycle = worlds.get(worldId);
            if (cycle == null) {
                playerVisuals.remove(player.getUniqueId());
                managedPlayers.remove(player.getUniqueId());
                continue;
            }
            managedPlayers.add(player.getUniqueId());
            boolean dry =
                    isDesertOrBadlands(player.getLocation().getBlock().getBiome())
                            && !Seasons.tridentRainApplies(player.getWorld())
                            && !Seasons.winterSnowAt(player.getLocation());
            Visual target = visualFor(cycle.state, dry);
            VisualTransition transition = playerVisuals.get(player.getUniqueId());
            if (transition == null || !transition.worldId.equals(worldId)) {
                transition = new VisualTransition(worldId, target);
                playerVisuals.put(player.getUniqueId(), transition);
            }
            Visual visual = transition.advance(target);
            sendChangedVisual(player, transition, visual);
            if (dry && cycle.state == State.RAIN && ticks % 5 == 0) {
                showDryBiomeDrizzle(player);
            }
        }
    }

    @EventHandler
    public void onPlayerQuit(PlayerQuitEvent event) {
        playerVisuals.remove(event.getPlayer().getUniqueId());
        managedPlayers.remove(event.getPlayer().getUniqueId());
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerJoin(PlayerJoinEvent event) {
        refreshPlayer(event.getPlayer());
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerSpawnLocation(PlayerSpawnLocationEvent event) {
        updateManagedPlayer(event.getPlayer(), event.getSpawnLocation().getWorld());
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerChangedWorld(PlayerChangedWorldEvent event) {
        refreshPlayer(event.getPlayer());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onPlayerTeleport(PlayerTeleportEvent event) {
        Location to = event.getTo();
        if (to != null && !event.getFrom().getWorld().equals(to.getWorld())) {
            // Protect entry packets before Bukkit fires PlayerChangedWorldEvent.
            updateManagedPlayer(event.getPlayer(), to.getWorld());
        }
    }

    private void updateManagedPlayer(Player player, World destination) {
        if (worlds.containsKey(destination.getUID())) managedPlayers.add(player.getUniqueId());
        else managedPlayers.remove(player.getUniqueId());
    }

    private void refreshPlayer(Player player) {
        updateManagedPlayer(player, player.getWorld());
        playerVisuals.remove(player.getUniqueId());
        Cycle cycle = worlds.get(player.getWorld().getUID());
        if (cycle == null) return;
        Visual visual =
                visualFor(
                        cycle.state,
                        isDesertOrBadlands(player.getLocation().getBlock().getBiome())
                                && !Seasons.tridentRainApplies(player.getWorld())
                                && !Seasons.winterSnowAt(player.getLocation()));
        VisualTransition transition = new VisualTransition(player.getWorld().getUID(), visual);
        playerVisuals.put(player.getUniqueId(), transition);
        sendChangedVisual(player, transition, visual);
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerRespawn(PlayerRespawnEvent event) {
        // Bukkit resets the player after this event; the next tick sends fresh levels.
        updateManagedPlayer(event.getPlayer(), event.getRespawnLocation().getWorld());
        playerVisuals.remove(event.getPlayer().getUniqueId());
    }

    private void loadWorld(World world) {
        loadWorld(world, false);
    }

    private void loadWorld(World world, boolean startup) {
        if (world.getEnvironment() != World.Environment.NORMAL
                || worlds.containsKey(world.getUID())) return;
        String base = PATH + world.getUID();
        Cycle cycle;
        if (startup) {
            cycle = startupCycle(weatherTicks);
        } else {
            try {
                String savedState = plugin.getConfig().getString(base + ".state");
                String savedTarget = plugin.getConfig().getString(base + ".target");
                if (savedState == null || savedTarget == null)
                    throw new IllegalArgumentException("not saved");
                State state = parseSavedState(savedState);
                int schema = plugin.getConfig().getInt(base + ".schema", 1);
                long deadline = plugin.getConfig().getLong(base + ".deadline", -1L);
                if (schema < 3) {
                    boolean enhanced = state == State.THUNDER && rollEnhanced();
                    cycle =
                            new Cycle(
                                    state,
                                    chooseTarget(state),
                                    weatherTicks + durationTicks(state),
                                    enhanced);
                } else {
                    State target = parseSavedState(savedTarget);
                    if (deadline < 0 || state == target)
                        throw new IllegalArgumentException("invalid cycle");
                    boolean enhanced =
                            state == State.THUNDER
                                    && plugin.getConfig().getBoolean(base + ".enhanced", false);
                    cycle = new Cycle(state, target, deadline, enhanced);
                }
            } catch (IllegalArgumentException ignored) {
                State state =
                        world.hasStorm()
                                ? (world.isThundering() ? State.THUNDER : State.RAIN)
                                : State.CLEAR;
                cycle =
                        new Cycle(
                                state,
                                chooseTarget(state),
                                weatherTicks + durationTicks(state),
                                state == State.THUNDER && rollEnhanced());
            }
        }
        // Keep the requested 3600 clear ticks on startup. Seasons independently finishes
        // any remaining accumulation minute, including when the actual storm was cleared.
        long seasonalUntil = plugin.getConfig().getLong(base + ".seasonal-thunder-until", 0L);
        if (!startup && seasonalUntil > System.currentTimeMillis()) {
            enterState(cycle, State.THUNDER);
            cycle.target = State.CLEAR;
            cycle.seasonalThunderUntil =
                    Math.min(seasonalUntil, System.currentTimeMillis() + 60_000L);
        }
        worlds.put(world.getUID(), cycle);
        advance(world, cycle);
        applyBackend(world, cycle);
        saveWorld(world, cycle);
        plugin.saveConfig();
    }

    private static Cycle startupCycle(long now) {
        return new Cycle(State.CLEAR, chooseTarget(State.CLEAR), now + STARTUP_CLEAR_TICKS, false);
    }

    private void restoreTrident(World world) {
        TridentOverride t = tridents.remove(world.getUID());
        setTridentRain(world, false);
        Cycle cycle = worlds.get(world.getUID());
        if (t == null || cycle == null) return;
        cycle.state = t.state;
        cycle.target = t.target;
        cycle.enhanced = t.enhanced;
        cycle.deadline = weatherTicks + t.remainingTicks;
        cycle.seasonalThunderUntil =
                t.seasonalMillis == 0 ? 0 : System.currentTimeMillis() + t.seasonalMillis;
        applyBackend(world, cycle);
    }

    private void startTrident(World world, boolean manual) {
        loadWorld(world);
        Cycle cycle = worlds.get(world.getUID());
        TridentOverride current = tridents.get(world.getUID());
        if (current == null) {
            advance(world, cycle);
            current =
                    new TridentOverride(
                            cycle.state,
                            cycle.target,
                            cycle.enhanced,
                            Math.max(0, cycle.deadline - weatherTicks),
                            Math.max(0, cycle.seasonalThunderUntil - System.currentTimeMillis()));
            tridents.put(world.getUID(), current);
            setTridentRain(world, true);
            enterState(cycle, State.RAIN);
            cycle.seasonalThunderUntil = 0;
            applyBackend(world, cycle);
        }
        if (manual) current.endNanos = System.nanoTime() + 1_000_000_000L;
    }

    private static final class TridentOverride {
        final State state, target;
        final boolean enhanced;
        final long remainingTicks, seasonalMillis;
        long endNanos;
        boolean holding;

        TridentOverride(State state, State target, boolean enhanced, long ticks, long millis) {
            this.state = state;
            this.target = target;
            this.enhanced = enhanced;
            this.remainingTicks = ticks;
            this.seasonalMillis = millis;
        }
    }

    private void setManual(World world, Cycle cycle, State state) {
        tridents.remove(world.getUID());
        setTridentRain(world, false);
        cycle.seasonalThunderUntil = 0; // Manual weather always takes precedence.
        enterState(cycle, state);
        cycle.target = chooseTarget(state);
        cycle.deadline = weatherTicks + durationTicks(state);
        applyBackend(world, cycle);
        saveWorld(world, cycle);
        plugin.saveConfig();
    }

    /** Starts a timed storm without changing the normal weather-duration settings. */
    public static boolean startSeasonalThunder(World world, long durationMillis) {
        Weather weather = activeWeather;
        if (weather == null
                || !weather.registered
                || world.getEnvironment() != World.Environment.NORMAL) return false;
        // A trident override keeps the saved weather intact until it ends. Seasonal snow
        // still observes its own accumulation deadline while this rain is active.
        if (weather.tridents.containsKey(world.getUID())) return true;
        weather.tridents.remove(world.getUID());
        weather.setTridentRain(world, false);
        weather.loadWorld(world);
        Cycle cycle = weather.worlds.get(world.getUID());
        enterState(cycle, State.THUNDER);
        cycle.target = State.CLEAR;
        cycle.seasonalThunderUntil = System.currentTimeMillis() + durationMillis;
        cycle.deadline = weather.weatherTicks + Math.max(1, (durationMillis + 49) / 50);
        weather.applyBackend(world, cycle);
        weather.saveWorld(world, cycle);
        weather.plugin.saveConfig();
        return true;
    }

    private void advance(World world, Cycle cycle) {
        long now = weatherTicks;
        TridentOverride temporary = tridents.get(world.getUID());
        if (temporary != null) {
            if (temporary.holding || System.nanoTime() < temporary.endNanos) return;
            tridents.remove(world.getUID());
            setTridentRain(world, false);
            cycle.state = temporary.state;
            cycle.target = temporary.target;
            cycle.enhanced = temporary.enhanced;
            cycle.deadline = now + temporary.remainingTicks;
            cycle.seasonalThunderUntil =
                    temporary.seasonalMillis == 0
                            ? 0
                            : System.currentTimeMillis() + temporary.seasonalMillis;
            applyBackend(world, cycle);
            saveWorld(world, cycle);
            plugin.saveConfig();
            return;
        }
        if (cycle.seasonalThunderUntil != 0) {
            long remaining = cycle.seasonalThunderUntil - System.currentTimeMillis();
            if (remaining > 0) {
                cycle.deadline = now + (remaining + 49) / 50;
                return;
            }
            cycle.seasonalThunderUntil = 0;
            cycle.deadline = now; // Resume the ordinary step toward clear immediately.
        }
        if (advanceCycle(cycle, now)) {
            applyBackend(world, cycle);
            saveWorld(world, cycle);
            plugin.saveConfig();
        }
    }

    private static boolean advanceCycle(Cycle cycle, long now) {
        int transitions = 0;
        while (now >= cycle.deadline && transitions++ < 1000) {
            int direction = Integer.compare(cycle.target.ordinal(), cycle.state.ordinal());
            enterState(cycle, State.values()[cycle.state.ordinal() + direction]);
            cycle.deadline += durationTicks(cycle.state);
            if (cycle.state == cycle.target) cycle.target = chooseTarget(cycle.state);
        }
        if (transitions > 0) {
            if (now >= cycle.deadline) cycle.deadline = now + durationTicks(cycle.state);
            return true;
        }
        return false;
    }

    private void applyBackend(World world, Cycle cycle) {
        applyingWeather = true;
        try {
            if (world.isThundering() && cycle.state != State.THUNDER) world.setThundering(false);
            if (world.hasStorm() != cycle.state.rain) world.setStorm(cycle.state.rain);
            if (cycle.state == State.THUNDER && !world.isThundering()) world.setThundering(true);
            int duration =
                    (int) Math.max(1L, Math.min(Integer.MAX_VALUE, cycle.deadline - weatherTicks));
            world.setWeatherDuration(duration);
            world.setThunderDuration(duration);
        } finally {
            applyingWeather = false;
        }
        if (world.hasStorm() != cycle.state.rain
                || world.isThundering() != (cycle.state == State.THUNDER)) {
            plugin.getLogger()
                    .warning(
                            "Another plugin prevented the requested weather in " + world.getName());
        }
    }

    private void saveWorld(World world, Cycle cycle) {
        String base = PATH + world.getUID();
        plugin.getConfig().set(base + ".state", cycle.state.name());
        plugin.getConfig().set(base + ".target", cycle.target.name());
        plugin.getConfig().set(base + ".deadline", cycle.deadline);
        plugin.getConfig().set(base + ".enhanced", cycle.enhanced);
        plugin.getConfig().set(base + ".seasonal-thunder-until", cycle.seasonalThunderUntil);
        plugin.getConfig().set(base + ".schema", 3);
    }

    private static State chooseTarget(State state) {
        if (state.rain) return State.CLEAR;
        return State.values()[State.DRIZZLE.ordinal() + ThreadLocalRandom.current().nextInt(4)];
    }

    private static State parseSavedState(String value) {
        if (value.equals("CLOUDLESS") || value.equals("OVERCAST")) return State.CLEAR;
        return State.valueOf(value);
    }

    private static boolean rollEnhanced() {
        return isEnhancedRoll(ThreadLocalRandom.current().nextDouble());
    }

    private static boolean isEnhancedRoll(double roll) {
        return roll < 0.30;
    }

    private static void enterState(Cycle cycle, State next) {
        if (next == State.THUNDER && cycle.state != State.THUNDER) {
            cycle.enhanced = rollEnhanced();
            cycle.naturalStrikes = cycle.extraStrikes = cycle.cancelledStrikes = 0;
        } else if (next != State.THUNDER) cycle.enhanced = false;
        cycle.state = next;
    }

    private static long durationTicks(State state) {
        long min, max;
        if (state == State.THUNDER) {
            min = 400;
            max = 800;
        } else if (state.rain) {
            min = 200;
            max = 400;
        } else {
            min = 5000;
            max = 10000;
        }
        return ThreadLocalRandom.current().nextLong(min, max + 1);
    }

    private static boolean isDesertOrBadlands(Biome biome) {
        return biome == Biome.DESERT
                || biome == Biome.BADLANDS
                || biome == Biome.WOODED_BADLANDS
                || biome == Biome.ERODED_BADLANDS;
    }

    private static Visual visualFor(State state, boolean dry) {
        if (state == State.CLEAR || (dry && (state == State.DRIZZLE || state == State.LIGHT_RAIN)))
            return new Visual(0.0f, 0.0f);
        if (dry && state == State.RAIN) return new Visual(0.31f, 0.0f);
        if (state == State.DRIZZLE) return new Visual(0.31f, 0.0f);
        if (state == State.LIGHT_RAIN) return new Visual(0.5f, 0.0f);
        if (state == State.RAIN) return new Visual(0.8f, 0.0f);
        return new Visual(1.0f, 1.0f);
    }

    /** Vanilla clients omit rain in desert and mesa, so show a small particle approximation. */
    private void showDryBiomeDrizzle(Player player) {
        Location eye = player.getEyeLocation();
        World world = player.getWorld();
        if (world.getHighestBlockYAt(eye.getBlockX(), eye.getBlockZ()) > eye.getY() + 1.0) return;
        double y = Math.min(eye.getY() + 4.0, world.getMaxHeight() - 1.0);
        player.spawnParticle(
                Particle.FALLING_WATER, eye.getX(), y, eye.getZ(), 16, 6.0, 2.0, 6.0, 0.0);
    }

    /** Adds independent strikes at approximately the vanilla per-chunk rate. */
    private void extraLightning(World world, boolean enhanced) {
        List<Player> players = new ArrayList<>();
        for (Player player : world.getPlayers())
            if (player.getGameMode() != GameMode.SPECTATOR) players.add(player);
        if (players.isEmpty()) return;
        ThreadLocalRandom random = ThreadLocalRandom.current();
        for (Chunk chunk : world.getLoadedChunks()) {
            if (!chunk.isEntitiesLoaded() || !nearPlayer(chunk, players)) continue;
            int extraAttempts = extraLightningAttempts(enhanced);
            for (int attempt = 0; attempt < extraAttempts; attempt++) {
                if (random.nextDouble() >= EXTRA_LIGHTNING_CHANCE) continue;
                int x = (chunk.getX() << 4) + random.nextInt(16);
                int z = (chunk.getZ() << 4) + random.nextInt(16);
                int y = world.getHighestBlockYAt(x, z) + 1;
                if (y >= world.getMaxHeight()) continue;
                Biome biome = world.getBiome(x, y, z);
                if (isDryForLightning(biome) || world.getTemperature(x, y, z) < 0.15) continue;
                boolean silent = isSilentExtraStrike(enhanced, attempt);
                spawningExtraLightning = true;
                try {
                    world.spigot()
                            .strikeLightning(new Location(world, x + 0.5, y, z + 0.5), silent);
                } finally {
                    spawningExtraLightning = false;
                }
            }
        }
    }

    private static int extraLightningAttempts(boolean enhanced) {
        return enhanced ? 3 : 1;
    }

    private static boolean isSilentExtraStrike(boolean enhanced, int attempt) {
        return !enhanced || attempt > 0;
    }

    private static boolean nearPlayer(Chunk chunk, List<Player> players) {
        double x = (chunk.getX() << 4) + 8.0, z = (chunk.getZ() << 4) + 8.0;
        for (Player player : players) {
            Location p = player.getLocation();
            double dx = p.getX() - x, dz = p.getZ() - z;
            if (dx * dx + dz * dz < 128.0 * 128.0) return true;
        }
        return false;
    }

    private static boolean isDryForLightning(Biome biome) {
        return isDesertOrBadlands(biome)
                || biome == Biome.SAVANNA
                || biome == Biome.SAVANNA_PLATEAU
                || biome == Biome.WINDSWEPT_SAVANNA;
    }

    private static boolean naturalThunderDisabled(World world) {
        FileConfiguration config = Bukkit.getServer().spigot().getPaperConfig();
        return config.getBoolean(
                "world-settings." + world.getName() + ".disable-thunder",
                config.getBoolean("world-settings.default.disable-thunder", false));
    }

    private static int naturalThunderChance(World world) {
        FileConfiguration config = Bukkit.getServer().spigot().getSpigotConfig();
        return config.getInt(
                "world-settings." + world.getName() + ".thunder-chance",
                config.getInt("world-settings.default.thunder-chance", 100000));
    }

    private void sendVisual(Player player, float rain, float thunder) {
        try {
            packets.send(player, packets.rainPacket(rain));
            packets.send(player, packets.thunderPacket(thunder));
        } catch (RuntimeException exception) {
            if (!packetErrorLogged) {
                packetErrorLogged = true;
                plugin.getLogger().severe("Could not send custom weather packets: " + exception);
            }
        }
    }

    private void sendChangedVisual(Player player, VisualTransition transition, Visual visual) {
        int rain = packetLevel(visual.rain);
        int thunder = packetLevel(visual.thunder);
        int updates = pendingVisualUpdates(transition, rain, thunder);
        try {
            if ((updates & 1) != 0) {
                packets.send(player, packets.rainPacket(visual.rain));
                transition.lastRain = rain;
            }
            if ((updates & 2) != 0) {
                packets.send(player, packets.thunderPacket(visual.thunder));
                transition.lastThunder = thunder;
            }
        } catch (RuntimeException exception) {
            if (!packetErrorLogged) {
                packetErrorLogged = true;
                plugin.getLogger().severe("Could not send custom weather packets: " + exception);
            }
        }
    }

    private static int packetLevel(float value) {
        return Math.max(0, Math.min(1000, Math.round(value * 1000.0f)));
    }

    private static int pendingVisualUpdates(VisualTransition transition, int rain, int thunder) {
        return (transition.lastRain != rain ? 1 : 0) | (transition.lastThunder != thunder ? 2 : 0);
    }

    private enum State {
        CLEAR(false),
        DRIZZLE(true),
        LIGHT_RAIN(true),
        RAIN(true),
        THUNDER(true);
        private final boolean rain;

        State(boolean rain) {
            this.rain = rain;
        }
    }

    private static final class Cycle {
        private State state, target;
        private long deadline, seasonalThunderUntil;
        private boolean enhanced;
        private long naturalStrikes, extraStrikes, cancelledStrikes;

        Cycle(State state, State target, long deadline, boolean enhanced) {
            this.state = state;
            this.target = target;
            this.deadline = deadline;
            this.enhanced = enhanced;
        }
    }

    private static final class Visual {
        private final float rain, thunder;

        Visual(float rain, float thunder) {
            this.rain = rain;
            this.thunder = thunder;
        }
    }

    /** Interpolates visual changes in both directions over five seconds. */
    private static final class VisualTransition {
        private final UUID worldId;
        private Visual start, current, target;
        private int elapsed = VISUAL_TRANSITION_TICKS;
        private int lastRain = -1, lastThunder = -1;

        VisualTransition(UUID worldId, Visual initial) {
            this.worldId = worldId;
            start = current = target = initial;
        }

        Visual advance(Visual nextTarget) {
            if (nextTarget.rain != target.rain || nextTarget.thunder != target.thunder) {
                start = current;
                target = nextTarget;
                elapsed = 0;
            }
            if (elapsed < VISUAL_TRANSITION_TICKS) {
                float fraction = (float) ++elapsed / VISUAL_TRANSITION_TICKS;
                current =
                        new Visual(
                                start.rain + (target.rain - start.rain) * fraction,
                                start.thunder + (target.thunder - start.thunder) * fraction);
            }
            return current;
        }
    }

    /** Own packets bypass the interceptor; cached templates are cloned before sending. */
    private static final class PacketBridge {
        private final ProtocolManager manager;
        private final ConcurrentMap<Integer, PacketContainer> rainPackets =
                new ConcurrentHashMap<>();
        private final ConcurrentMap<Integer, PacketContainer> thunderPackets =
                new ConcurrentHashMap<>();

        PacketBridge(ProtocolManager manager) {
            this.manager = manager;
            // Resolve the 1.18.2 reason/float modifiers before taking control of weather.
            PacketContainer probe = createPacket(7, 0);
            if (probe.getGameStateIDs().read(0) != 7 || probe.getFloat().read(0) != 0.0f) {
                throw new IllegalStateException(
                        "ProtocolLib could not resolve weather packet fields.");
            }
        }

        private PacketContainer createPacket(int reason, int level) {
            PacketContainer packet = manager.createPacket(PacketType.Play.Server.GAME_STATE_CHANGE);
            packet.getGameStateIDs().write(0, reason);
            packet.getFloat().write(0, level / 1000.0f);
            return packet;
        }

        PacketContainer rainPacket(float value) {
            int level = packetLevel(value);
            return rainPackets.computeIfAbsent(level, k -> createPacket(7, k));
        }

        PacketContainer thunderPacket(float value) {
            int level = packetLevel(value);
            return thunderPackets.computeIfAbsent(level, k -> createPacket(8, k));
        }

        void send(Player player, PacketContainer packet) {
            // false skips ordinary packet listeners, including our HIGHEST interceptor.
            manager.sendServerPacket(player, packet.shallowClone(), false);
        }
    }
}
