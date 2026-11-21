package plugin;

import com.destroystokyo.paper.event.entity.EntityPathfindEvent;
import io.papermc.paper.event.entity.EntityMoveEvent;
import org.bukkit.Bukkit;
import org.bukkit.ChatColor;
import org.bukkit.Location;
import org.bukkit.World;
import org.bukkit.command.Command;
import org.bukkit.command.CommandExecutor;
import org.bukkit.command.CommandSender;
import org.bukkit.command.TabCompleter;
import org.bukkit.configuration.ConfigurationSection;
import org.bukkit.configuration.file.YamlConfiguration;
import org.bukkit.entity.Villager;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.Listener;
import org.bukkit.command.PluginCommand;
import org.bukkit.plugin.java.JavaPlugin;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.stream.Collectors;

public class Main extends JavaPlugin implements Listener, CommandExecutor, TabCompleter {

    private final Map<UUID, Map<Integer, VillagerZone>> zonesByWorld = new HashMap<>();
    private File zonesFile;
    private BetterVillagers betterVillagers;
    private RainSimple rainSimple;
    private Weather customWeather;
    private Seasons seasons;

    @Override
    public void onEnable() {
        zonesFile = new File(getDataFolder(), "zones.yml");
        loadZones();

        PluginCommand command = getCommand("vzone");
        if (command == null) {
            getLogger().severe("The vzone command is missing from plugin.yml.");
            getServer().getPluginManager().disablePlugin(this);
            return;
        }

        command.setExecutor(this);
        command.setTabCompleter(this);
        getServer().getPluginManager().registerEvents(this, this);

        getLogger().info("Villager zones enabled.");
        
        betterVillagers = new BetterVillagers(this);
        betterVillagers.register();
        
        rainSimple = new RainSimple(this);
        rainSimple.register();
        
        customWeather = new Weather(this);
        customWeather.register();
        
        seasons = new Seasons(this);
        seasons.register();
    }
    
    @Override
    public void onDisable() {
        if (betterVillagers != null) {
            betterVillagers.shutdown();
        }
        
        if (rainSimple != null) {
            rainSimple.shutdown();
        }
        
        if (customWeather != null) {
            customWeather.shutdown();
        }
        
        if (seasons != null) seasons.shutdown();
    }

    @Override
    public boolean onCommand(
            CommandSender sender,
            Command command,
            String label,
            String[] args
    ) {
        if (args.length == 1 && args[0].equalsIgnoreCase("display")) {
            displayZones(sender);
            return true;
        }

        if (args.length > 0 && args[0].equalsIgnoreCase("remove")) {
            if (args.length != 2) {
                sendUsage(sender);
                return true;
            }

            removeZone(sender, args[1]);
            return true;
        }

        if (args.length != 7) {
            sendUsage(sender);
            return true;
        }

        createOrUpdateZone(sender, args);
        return true;
    }

    private void createOrUpdateZone(CommandSender sender, String[] args) {
        if (!(sender instanceof org.bukkit.entity.Player player)) {
            sender.sendMessage(ChatColor.RED + "Run this command in-game so the zone can be assigned to a world.");
            return;
        }

        final int id;
        final int x1;
        final int y1;
        final int z1;
        final int x2;
        final int y2;
        final int z2;

        try {
            id = Integer.parseInt(args[0]);
            x1 = Integer.parseInt(args[1]);
            y1 = Integer.parseInt(args[2]);
            z1 = Integer.parseInt(args[3]);
            x2 = Integer.parseInt(args[4]);
            y2 = Integer.parseInt(args[5]);
            z2 = Integer.parseInt(args[6]);
        } catch (NumberFormatException exception) {
            sender.sendMessage(ChatColor.RED + "The zone number and coordinates must be integers.");
            return;
        }

        if (id < 1) {
            sender.sendMessage(ChatColor.RED + "The zone number must be a positive integer.");
            return;
        }

        World world = player.getWorld();
        UUID worldId = world.getUID();

        VillagerZone zone = new VillagerZone(
                id,
                worldId,
                world.getName(),
                Math.min(x1, x2), Math.min(y1, y2), Math.min(z1, z2),
                Math.max(x1, x2), Math.max(y1, y2), Math.max(z1, z2)
        );

        Map<Integer, VillagerZone> worldZones =
                zonesByWorld.computeIfAbsent(worldId, ignored -> new HashMap<>());

        VillagerZone previous = worldZones.put(id, zone);
        if (!saveZones()) {
            if (previous == null) {
                worldZones.remove(id);
            } else {
                worldZones.put(id, previous);
            }
            removeEmptyWorld(worldId);
            sender.sendMessage(ChatColor.RED + "Couldn't save the zone. Check the server log.");
            return;
        }

        sender.sendMessage(ChatColor.GREEN + "Created/updated villager zone " + id
                + " in " + world.getName() + ".");
    }

    private void removeZone(CommandSender sender, String idText) {
        if (!(sender instanceof org.bukkit.entity.Player player)) {
            sender.sendMessage(ChatColor.RED + "Run this command in-game to select the world.");
            return;
        }

        final int id;
        try {
            id = Integer.parseInt(idText);
        } catch (NumberFormatException exception) {
            sender.sendMessage(ChatColor.RED + "The zone number must be an integer.");
            return;
        }

        UUID worldId = player.getWorld().getUID();
        Map<Integer, VillagerZone> worldZones = zonesByWorld.get(worldId);
        if (worldZones == null || !worldZones.containsKey(id)) {
            sender.sendMessage(ChatColor.RED + "There is no zone " + id
                    + " in this world.");
            return;
        }

        VillagerZone removed = worldZones.remove(id);
        removeEmptyWorld(worldId);

        if (!saveZones()) {
            zonesByWorld.computeIfAbsent(worldId, ignored -> new HashMap<>())
                    .put(id, removed);
            sender.sendMessage(ChatColor.RED + "Couldn't save the change. Check the server log.");
            return;
        }

        sender.sendMessage(ChatColor.GREEN + "Removed villager zone " + id + ".");
    }

    private void displayZones(CommandSender sender) {
        List<VillagerZone> zones = new ArrayList<>();

        if (sender instanceof org.bukkit.entity.Player player) {
            Map<Integer, VillagerZone> worldZones =
                    zonesByWorld.get(player.getWorld().getUID());
            if (worldZones != null) {
                zones.addAll(worldZones.values());
            }
        } else {
            for (Map<Integer, VillagerZone> worldZones : zonesByWorld.values()) {
                zones.addAll(worldZones.values());
            }
        }

        if (zones.isEmpty()) {
            sender.sendMessage(ChatColor.YELLOW + "No villager zones are defined.");
            return;
        }

        zones.sort(Comparator
                .comparing(VillagerZone::worldName, String.CASE_INSENSITIVE_ORDER)
                .thenComparingInt(VillagerZone::id));

        sender.sendMessage(ChatColor.GOLD + "Villager zones:");
        for (VillagerZone zone : zones) {
            sender.sendMessage(ChatColor.YELLOW + "  " + zone.id()
                    + ChatColor.GRAY + " [" + zone.worldName() + "] "
                    + "(" + zone.minX() + ", " + zone.minY() + ", " + zone.minZ() + ")"
                    + " to "
                    + "(" + zone.maxX() + ", " + zone.maxY() + ", " + zone.maxZ() + ")");
        }
    }

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onVillagerPathfind(EntityPathfindEvent event) {
        if (!(event.getEntity() instanceof Villager villager)) {
            return;
        }

        if (wouldLeaveZone(villager.getLocation(), event.getLoc())) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onVillagerMove(EntityMoveEvent event) {
        if (!(event.getEntity() instanceof Villager)) {
            return;
        }

        if (wouldLeaveZone(event.getFrom(), event.getTo())) {
            event.setCancelled(true);
        }
    }

    private boolean wouldLeaveZone(Location from, Location to) {
        if (from.getWorld() == null || to.getWorld() == null) {
            return false;
        }

        Map<Integer, VillagerZone> worldZones =
                zonesByWorld.get(from.getWorld().getUID());
        if (worldZones == null) {
            return false;
        }

        for (VillagerZone zone : worldZones.values()) {
            if (zone.contains(from) && !zone.contains(to)) {
                return true;
            }
        }

        return false;
    }

    private void loadZones() {
        zonesByWorld.clear();

        if (!zonesFile.isFile()) {
            return;
        }

        YamlConfiguration data = YamlConfiguration.loadConfiguration(zonesFile);
        ConfigurationSection allZones = data.getConfigurationSection("zones");
        if (allZones == null) {
            return;
        }

        for (String worldKey : allZones.getKeys(false)) {
            final UUID worldId;
            try {
                worldId = UUID.fromString(worldKey);
            } catch (IllegalArgumentException exception) {
                getLogger().warning("Skipping zones with invalid world UUID: " + worldKey);
                continue;
            }

            ConfigurationSection worldSection =
                    allZones.getConfigurationSection(worldKey);
            if (worldSection == null) {
                continue;
            }

            for (String zoneKey : worldSection.getKeys(false)) {
                final int id;
                try {
                    id = Integer.parseInt(zoneKey);
                } catch (NumberFormatException exception) {
                    getLogger().warning("Skipping invalid zone number: " + zoneKey);
                    continue;
                }

                ConfigurationSection section =
                        worldSection.getConfigurationSection(zoneKey);
                if (section == null) {
                    continue;
                }

                Integer minX = readInteger(section, "min-x");
                Integer minY = readInteger(section, "min-y");
                Integer minZ = readInteger(section, "min-z");
                Integer maxX = readInteger(section, "max-x");
                Integer maxY = readInteger(section, "max-y");
                Integer maxZ = readInteger(section, "max-z");

                if (minX == null || minY == null || minZ == null
                        || maxX == null || maxY == null || maxZ == null) {
                    getLogger().warning("Skipping incomplete zone " + zoneKey
                            + " in world " + worldKey);
                    continue;
                }

                String worldName = section.getString("world-name", worldKey);
                VillagerZone zone = new VillagerZone(
                        id, worldId, worldName,
                        minX, minY, minZ, maxX, maxY, maxZ
                );

                zonesByWorld.computeIfAbsent(worldId, ignored -> new HashMap<>())
                        .put(id, zone);
            }
        }
    }

    private Integer readInteger(ConfigurationSection section, String path) {
        Object value = section.get(path);
        if (!(value instanceof Number number)) {
            return null;
        }

        double numericValue = number.doubleValue();
        if (numericValue < Integer.MIN_VALUE
                || numericValue > Integer.MAX_VALUE
                || numericValue != Math.rint(numericValue)) {
            return null;
        }

        return number.intValue();
    }

    private boolean saveZones() {
        if (!getDataFolder().exists() && !getDataFolder().mkdirs()) {
            getLogger().severe("Could not create the plugin data folder.");
            return false;
        }

        YamlConfiguration data = new YamlConfiguration();

        for (Map<Integer, VillagerZone> worldZones : zonesByWorld.values()) {
            for (VillagerZone zone : worldZones.values()) {
                String path = "zones." + zone.worldId() + "." + zone.id();

                data.set(path + ".world-name", zone.worldName());
                data.set(path + ".min-x", zone.minX());
                data.set(path + ".min-y", zone.minY());
                data.set(path + ".min-z", zone.minZ());
                data.set(path + ".max-x", zone.maxX());
                data.set(path + ".max-y", zone.maxY());
                data.set(path + ".max-z", zone.maxZ());
            }
        }

        try {
            data.save(zonesFile);
            return true;
        } catch (IOException exception) {
            getLogger().severe("Could not save villager zones: " + exception.getMessage());
            return false;
        }
    }

    private void removeEmptyWorld(UUID worldId) {
        Map<Integer, VillagerZone> worldZones = zonesByWorld.get(worldId);
        if (worldZones != null && worldZones.isEmpty()) {
            zonesByWorld.remove(worldId);
        }
    }

    private void sendUsage(CommandSender sender) {
        sender.sendMessage(ChatColor.YELLOW
                + "Usage: /vzone <num> <x1> <y1> <z1> <x2> <y2> <z2>");
        sender.sendMessage(ChatColor.YELLOW + "       /vzone remove <num>");
        sender.sendMessage(ChatColor.YELLOW + "       /vzone display");
    }

    @Override
    public List<String> onTabComplete(
            CommandSender sender,
            Command command,
            String alias,
            String[] args
    ) {
        if (args.length == 1) {
            String prefix = args[0].toLowerCase();
            return List.of("remove", "display").stream()
                    .filter(option -> option.startsWith(prefix))
                    .collect(Collectors.toList());
        }

        if (args.length == 2
                && args[0].equalsIgnoreCase("remove")
                && sender instanceof org.bukkit.entity.Player player) {
            Map<Integer, VillagerZone> worldZones =
                    zonesByWorld.get(player.getWorld().getUID());
            if (worldZones == null) {
                return List.of();
            }

            String prefix = args[1];
            return worldZones.keySet().stream()
                    .map(String::valueOf)
                    .filter(id -> id.startsWith(prefix))
                    .sorted()
                    .collect(Collectors.toList());
        }

        return List.of();
    }

    private record VillagerZone(
            int id,
            UUID worldId,
            String worldName,
            int minX,
            int minY,
            int minZ,
            int maxX,
            int maxY,
            int maxZ
    ) {
        private boolean contains(Location location) {
            return location.getWorld() != null
                    && worldId.equals(location.getWorld().getUID())
                    && location.getBlockX() >= minX
                    && location.getBlockX() <= maxX
                    && location.getBlockY() >= minY
                    && location.getBlockY() <= maxY
                    && location.getBlockZ() >= minZ
                    && location.getBlockZ() <= maxZ;
        }
    }
}