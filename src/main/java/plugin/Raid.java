package plugin;

import org.bukkit.Bukkit;
import org.bukkit.Chunk;
import org.bukkit.Difficulty;
import org.bukkit.GameRule;
import org.bukkit.Location;
import org.bukkit.Material;
import org.bukkit.NamespacedKey;
import org.bukkit.World;
import org.bukkit.attribute.Attribute;
import org.bukkit.block.Block;
import org.bukkit.block.BlockState;
import org.bukkit.block.data.type.Snow;
import org.bukkit.boss.BarColor;
import org.bukkit.boss.BarStyle;
import org.bukkit.boss.BossBar;
import org.bukkit.entity.Entity;
import org.bukkit.entity.Evoker;
import org.bukkit.entity.Illusioner;
import org.bukkit.entity.Pillager;
import org.bukkit.entity.Player;
import org.bukkit.entity.Raider;
import org.bukkit.entity.Villager;
import org.bukkit.entity.Vindicator;
import org.bukkit.command.PluginCommand;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.Listener;
import org.bukkit.event.entity.CreatureSpawnEvent;
import org.bukkit.event.entity.EntityDeathEvent;
import org.bukkit.event.raid.RaidTriggerEvent;
import org.bukkit.event.world.EntitiesLoadEvent;
import org.bukkit.event.world.EntitiesUnloadEvent;
import org.bukkit.persistence.PersistentDataType;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.scheduler.BukkitTask;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ThreadLocalRandom;

/** Bell-based, custom pillager raids for Paper 1.18.2. */
public final class Raid implements Listener {
    private static final String ROOT = "death-eater-raids";
    private static final String ACTIVE = ROOT + ".active";
    private static final long DAY_TICKS = 24000L;
    private static final double VILLAGE_RADIUS = 30.0;
    private static final int BABY_SPAWN_RADIUS = 30;
    private static final double BABY_SKIN_SOURCE_RADIUS = 20.0;
    private static final Villager.Type[] RAID_BABY_SKINS = {
        Villager.Type.DESERT,
        Villager.Type.JUNGLE,
        Villager.Type.SAVANNA,
        Villager.Type.SNOW,
        Villager.Type.SWAMP,
        Villager.Type.TAIGA
    };
    private static final double BELL_MERGE_RADIUS = 100.0;
    private static final double DISPLAY_RADIUS = 100.0;
    private static final int MIN_VILLAGERS = 3;
    private static final int[] WAVE_MEANS = {5, 9, 13, 17, 20};
    private static final int INTERMISSION_SECONDS = 10;
    private static final long WAVE_DURATION_MILLIS = 60_000L;
    private static final String KILLS_PATH = ROOT + ".pending-wave-kills";
    private static final String BIRTHS_PATH = ROOT + ".pending-births";

    private final JavaPlugin plugin;
    private final BetterVillagers betterVillagers;
    private final NamespacedKey raidKey;
    private final Map<UUID, RaiderState> raiders = new HashMap<>();
    private final Set<UUID> pendingWaveKills = new HashSet<>();
    private BukkitTask task;
    private BossBar bar;
    private UUID worldId;
    private int bellX, bellY, bellZ, wave, totalWaves, pending, waveSize, secondsUntilWave;
    private boolean active;
    private boolean boostActive;
    private int scanSeconds;
    private int failedSpawnSeconds;
    private long waveDeadlineMillis;
    private double raidProbability = 0.05;

    public Raid(JavaPlugin plugin, BetterVillagers betterVillagers) {
        this.plugin = plugin;
        this.betterVillagers = betterVillagers;
        this.raidKey = new NamespacedKey(plugin, "death_eater_raider");
    }

    public void register() {
        raidProbability = plugin.getConfig().getDouble(ROOT + ".probability", 0.05);
        if (!Double.isFinite(raidProbability) || raidProbability < 0 || raidProbability > 1) raidProbability = 0.05;
        PluginCommand raidCommand = plugin.getCommand("raid");
        if (raidCommand == null) throw new IllegalStateException("Add raid to plugin.yml.");
        raidCommand.setExecutor((sender, command, label, args) -> {
            if (args.length != 1) { sender.sendMessage("Usage: /raid <probability between 0 and 1>"); return true; }
            try {
                double value = Double.parseDouble(args[0]);
                if (!Double.isFinite(value) || value < 0 || value > 1) throw new NumberFormatException();
                raidProbability = value;
                plugin.getConfig().set(ROOT + ".probability", value);
                plugin.saveConfig();
                sender.sendMessage("Daily raid probability: " + value);
            } catch (NumberFormatException ex) { sender.sendMessage("Probability must be between 0 and 1."); }
            return true;
        });
        Bukkit.getPluginManager().registerEvents(this, plugin);
        loadPendingWork();
        spawnLegacyBirthsOnce();
        loadActiveRaid();
        task = Bukkit.getScheduler().runTaskTimer(plugin, this::tick, 20L, 20L);
    }

    public void shutdown() {
        if (task != null) task.cancel();
        if (active) saveActiveRaid();
        if (bar != null) bar.removeAll();
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onVanillaRaidTrigger(RaidTriggerEvent event) {
        if (active || anotherVanillaRaidExists(event.getRaid())) event.setCancelled(true);
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onVanillaRaidStarted(RaidTriggerEvent event) {
        applyBoost(true);
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onRaiderDeath(EntityDeathEvent event) {
        if (pendingWaveKills.remove(event.getEntity().getUniqueId())) savePendingWork();
        if (active && raiders.remove(event.getEntity().getUniqueId()) != null) saveActiveRaid();
    }

    @EventHandler
    public void onEntitiesUnload(EntitiesUnloadEvent event) {
        if (!active) return;
        boolean changed = false;
        for (Entity entity : event.getEntities()) {
            RaiderState state = raiders.get(entity.getUniqueId());
            if (state != null) {
                state.update(entity);
                changed = true;
            }
        }
        if (changed) saveActiveRaid();
    }

    @EventHandler
    public void onEntitiesLoad(EntitiesLoadEvent event) {
        for (Entity entity : event.getEntities()) {
            if (entity instanceof Raider raider
                    && pendingWaveKills.contains(entity.getUniqueId())) {
                raider.setHealth(0.0);
            } else if (entity instanceof Raider
                    && entity.getPersistentDataContainer().has(raidKey, PersistentDataType.BYTE)
                    && (!active || !raiders.containsKey(entity.getUniqueId()))) {
                entity.remove();
            }
        }
    }

    private void tick() {
        processPendingKills();
        if (++scanSeconds >= 10) {
            scanSeconds = 0;
            rollDailyRaids();
        }
        applyBoost(active || anotherVanillaRaidExists(null));
        if (!active) return;
        if (waveDeadlineMillis > 0 && System.currentTimeMillis() >= waveDeadlineMillis) {
            finishTimedOutWave();
        }
        World world = Bukkit.getWorld(worldId);
        if (world == null) return;
        updateViewers(world);
        if (!world.isChunkLoaded(bellX >> 4, bellZ >> 4)) return;

        if (world.getBlockAt(bellX, bellY, bellZ).getType() != Material.BELL
                || (villageChunksLoaded(world) && countVillagers(bellLocation(world)) == 0)) {
            endRaid(false);
            return;
        }
        updateRaiders(world);
        updateBar();
        if (pending > 0) {
            spawnPending(world);
            return;
        }
        if (!raiders.isEmpty()) return;
        if (waveDeadlineMillis != 0) {
            waveDeadlineMillis = 0;
            saveActiveRaid();
        }
        if (wave >= totalWaves) {
            endRaid(true);
            return;
        }
        if (secondsUntilWave > 0) {
            secondsUntilWave--;
            saveActiveRaid();
            return;
        }
        wave++;
        waveSize = WAVE_MEANS[wave - 1] + ThreadLocalRandom.current().nextInt(-2, 3);
        pending = waveSize;
        waveDeadlineMillis = System.currentTimeMillis() + WAVE_DURATION_MILLIS;
        secondsUntilWave = INTERMISSION_SECONDS;
        saveActiveRaid();
        spawnPending(world);
    }

    /** Roll once per eligible loaded village per world day. */
    private void rollDailyRaids() {
        List<Location> winners = new ArrayList<>();
        boolean canStart = !active && !anotherVanillaRaidExists(null);
        List<Map<String, Object>> checks = new ArrayList<>();
        for (Map<?, ?> row : plugin.getConfig().getMapList(ROOT + ".daily-checks")) {
            try {
                World world = Bukkit.getWorld(UUID.fromString(String.valueOf(row.get("world"))));
                long day = ((Number) row.get("day")).longValue();
                if (world != null && day == Math.floorDiv(world.getFullTime(), DAY_TICKS)) {
                    Map<String, Object> copy = new HashMap<>();
                    copy.put("world", world.getUID().toString());
                    copy.put("day", day);
                    copy.put("x", ((Number) row.get("x")).intValue());
                    copy.put("z", ((Number) row.get("z")).intValue());
                    checks.add(copy);
                }
            } catch (RuntimeException ignored) {
                plugin.getLogger().warning("Ignoring an invalid saved raid check.");
            }
        }
        boolean changed = false;
        for (World world : Bukkit.getWorlds()) {
            long today = Math.floorDiv(world.getFullTime(), DAY_TICKS);
            if (!canStart
                    || world.getDifficulty() == Difficulty.PEACEFUL
                    || Boolean.TRUE.equals(world.getGameRuleValue(GameRule.DISABLE_RAIDS)))
                continue;
            for (Location bell : eligibleVillages(world)) {
                boolean checked = false;
                for (Map<String, Object> row : checks) {
                    if (!world.getUID().toString().equals(row.get("world"))) continue;
                    double dx = bell.getBlockX() - ((Number) row.get("x")).intValue();
                    double dz = bell.getBlockZ() - ((Number) row.get("z")).intValue();
                    if (dx * dx + dz * dz <= BELL_MERGE_RADIUS * BELL_MERGE_RADIUS) {
                        checked = true;
                        break;
                    }
                }
                if (checked) continue;
                Map<String, Object> row = new HashMap<>();
                row.put("world", world.getUID().toString());
                row.put("day", today);
                row.put("x", bell.getBlockX());
                row.put("z", bell.getBlockZ());
                checks.add(row);
                changed = true;
                if (ThreadLocalRandom.current().nextDouble() < raidProbability) winners.add(bell);
            }
        }
        if (changed) {
            plugin.getConfig().set(ROOT + ".daily-checks", checks);
            plugin.saveConfig();
        }
        if (!winners.isEmpty() && !active && !anotherVanillaRaidExists(null)) {
            Location bell = winners.get(ThreadLocalRandom.current().nextInt(winners.size()));
            startRaid(bell);
        }
    }

    /** Nearby eligible bells are grouped so a village is rolled only once. */
    private List<Location> eligibleVillages(World world) {
        List<Location> bells = new ArrayList<>();
        for (Chunk chunk : world.getLoadedChunks()) {
            for (BlockState state : chunk.getTileEntities()) {
                if (state.getType() == Material.BELL
                        && countVillagers(state.getLocation()) >= MIN_VILLAGERS) {
                    bells.add(state.getLocation());
                }
            }
        }
        bells.sort(
                Comparator.comparingInt(Location::getBlockX)
                        .thenComparingInt(Location::getBlockZ)
                        .thenComparingInt(Location::getBlockY));
        List<Location> representatives = new ArrayList<>();
        boolean[] visited = new boolean[bells.size()];
        for (int i = 0; i < bells.size(); i++) {
            if (visited[i]) continue;
            representatives.add(bells.get(i));
            List<Integer> queue = new ArrayList<>();
            queue.add(i);
            visited[i] = true;
            for (int pos = 0; pos < queue.size(); pos++) {
                Location member = bells.get(queue.get(pos));
                for (int j = 0; j < bells.size(); j++) {
                    if (!visited[j]
                            && horizontalDistanceSquared(member, bells.get(j))
                                    <= BELL_MERGE_RADIUS * BELL_MERGE_RADIUS) {
                        visited[j] = true;
                        queue.add(j);
                    }
                }
            }
        }
        return representatives;
    }

    private int countVillagers(Location center) {
        int count = 0;
        for (Entity entity :
                center.getWorld()
                        .getNearbyEntities(
                                center, VILLAGE_RADIUS, VILLAGE_RADIUS, VILLAGE_RADIUS)) {
            if (entity instanceof Villager
                    && entity.isValid()
                    && !entity.isDead()
                    && entity.getLocation().distanceSquared(center)
                            <= VILLAGE_RADIUS * VILLAGE_RADIUS) count++;
        }
        return count;
    }

    private boolean villageChunksLoaded(World world) {
        int minX = (int) Math.floor((bellX - VILLAGE_RADIUS) / 16.0);
        int maxX = (int) Math.floor((bellX + VILLAGE_RADIUS) / 16.0);
        int minZ = (int) Math.floor((bellZ - VILLAGE_RADIUS) / 16.0);
        int maxZ = (int) Math.floor((bellZ + VILLAGE_RADIUS) / 16.0);
        for (int x = minX; x <= maxX; x++) {
            for (int z = minZ; z <= maxZ; z++) {
                if (!world.isChunkLoaded(x, z)) return false;
            }
        }
        return true;
    }

    private void startRaid(Location bell) {
        worldId = bell.getWorld().getUID();
        bellX = bell.getBlockX();
        bellY = bell.getBlockY();
        bellZ = bell.getBlockZ();
        int villagers = countVillagers(bell);
        totalWaves = villagers <= 5 ? 3 : villagers <= 10 ? 4 : 5;
        wave = 0;
        pending = 0;
        waveSize = 0;
        waveDeadlineMillis = 0;
        secondsUntilWave = INTERMISSION_SECONDS;
        raiders.clear();
        failedSpawnSeconds = 0;
        active = true;
        bar = Bukkit.createBossBar("Death Eater Raid", BarColor.RED, BarStyle.SOLID);
        applyBoost(true);
        saveActiveRaid();
        Bukkit.broadcastMessage(
                "§cA Death Eater Raid has begun near " + bellX + ", " + bellY + ", " + bellZ + "!");
    }

    private void spawnPending(World world) {
        int spawned = 0;
        for (int attempts = 0; attempts < 160 && pending > 0 && spawned < 5; attempts++) {
            Location place = findSpawnLocation(world);
            if (place == null) continue;
            try {
                Raider mob =
                        world.spawn(
                                place,
                                raiderType(ThreadLocalRandom.current().nextInt(100)),
                                CreatureSpawnEvent.SpawnReason.CUSTOM,
                                p -> {
                                    p.setRemoveWhenFarAway(false);
                                    p.getPersistentDataContainer()
                                            .set(raidKey, PersistentDataType.BYTE, (byte) 1);
                                });
                if (mob == null || !mob.isValid() || mob.isDead()) continue;
                raiders.put(mob.getUniqueId(), new RaiderState(mob.getLocation(), 1.0));
                pending--;
                spawned++;
            } catch (IllegalArgumentException ignored) {
                // A different plugin may reject the spawn or position.
            }
        }
        if (spawned > 0) saveActiveRaid();
        if (spawned > 0) {
            failedSpawnSeconds = 0;
        } else if (++failedSpawnSeconds >= 60) {
            endRaid(
                    false,
                    "§cThe Death Eater Raid ended because no suitable spawn area was available.");
            return;
        }
        updateBar();
    }

    private static Class<? extends Raider> raiderType(int roll) {
        if (roll < 65) return Pillager.class;
        if (roll < 85) return Vindicator.class;
        if (roll < 95) return Illusioner.class;
        return Evoker.class;
    }

    /** Kill loaded raiders now and record unloaded raiders for their next load. */
    private void finishTimedOutWave() {
        waveDeadlineMillis = 0;
        pending = 0;
        List<UUID> expired = new ArrayList<>(raiders.keySet());
        pendingWaveKills.addAll(expired);
        savePendingWork();
        saveActiveRaid();
        for (UUID id : expired) {
            Entity entity = Bukkit.getEntity(id);
            if (entity instanceof Raider raider && raider.isValid() && !raider.isDead()) {
                raider.setHealth(0.0);
            }
        }
        raiders.clear();
        saveActiveRaid();
    }

    private void processPendingKills() {
        for (UUID id : new ArrayList<>(pendingWaveKills)) {
            Entity entity = Bukkit.getEntity(id);
            if (entity instanceof Raider raider && raider.isValid() && !raider.isDead()) {
                raider.setHealth(0.0);
            } else if (entity != null && entity.isDead() && pendingWaveKills.remove(id)) {
                savePendingWork();
            }
        }
    }

    private Location findSpawnLocation(World world) {
        double angle = ThreadLocalRandom.current().nextDouble(2 * Math.PI);
        double distance = ThreadLocalRandom.current().nextDouble(18.0, 33.0);
        int x = bellX + (int) Math.round(Math.cos(angle) * distance);
        int z = bellZ + (int) Math.round(Math.sin(angle) * distance);
        if (!world.isChunkLoaded(x >> 4, z >> 4)) return null;
        int y = world.getHighestBlockYAt(x, z) + 1;
        if (Math.abs(y - bellY) > 20
                || y < world.getMinHeight() + 1
                || y + 1 >= world.getMaxHeight()) return null;
        Block floor = world.getBlockAt(x, y - 1, z);
        if (!floor.getType().isSolid()
                || !world.getBlockAt(x, y, z).isPassable()
                || !world.getBlockAt(x, y + 1, z).isPassable()) return null;
        return new Location(world, x + 0.5, y, z + 0.5);
    }

    private void updateRaiders(World world) {
        boolean changed = false;
        for (Map.Entry<UUID, RaiderState> entry : new ArrayList<>(raiders.entrySet())) {
            Entity entity = Bukkit.getEntity(entry.getKey());
            RaiderState state = entry.getValue();
            if (entity instanceof Raider raider && raider.isValid() && !raider.isDead()) {
                state.update(raider);
                if (raider.getTarget() == null) {
                    Villager nearest = null;
                    double best = 64.0 * 64.0;
                    for (Entity target : raider.getNearbyEntities(64, 64, 64)) {
                        if (target instanceof Villager villager
                                && villager.isValid()
                                && !villager.isDead()) {
                            double d = villager.getLocation().distanceSquared(raider.getLocation());
                            if (d < best) {
                                best = d;
                                nearest = villager;
                            }
                        }
                    }
                    if (nearest != null) raider.setTarget(nearest);
                }
            } else if (world.isChunkLoaded(state.chunkX, state.chunkZ)) {
                raiders.remove(entry.getKey());
                changed = true;
            }
        }
        if (changed) saveActiveRaid();
    }

    private void updateViewers(World world) {
        Location bell = bellLocation(world);
        for (Player player : Bukkit.getOnlinePlayers()) {
            boolean near =
                    player.getWorld().equals(world)
                            && player.getLocation().distanceSquared(bell)
                                    <= DISPLAY_RADIUS * DISPLAY_RADIUS;
            if (near) bar.addPlayer(player);
            else bar.removePlayer(player);
        }
    }

    private void updateBar() {
        double remaining = pending;
        for (RaiderState state : raiders.values()) remaining += state.healthFraction;
        bar.setTitle("Death Eater Raid" + (wave > 0 ? " - Wave " + wave + "/" + totalWaves : ""));
        bar.setProgress(waveSize == 0 ? 1.0 : Math.max(0.0, Math.min(1.0, remaining / waveSize)));
    }

    private void endRaid(boolean won) {
        endRaid(won, null);
    }

    private void endRaid(boolean won, String message) {
        active = false;
        if (bar != null) {
            bar.removeAll();
            bar = null;
        }
        for (UUID id : raiders.keySet()) {
            Entity mob = Bukkit.getEntity(id);
            if (mob != null) mob.remove();
        }
        raiders.clear();
        plugin.getConfig().set(ACTIVE, null);
        savePendingWork();
        applyBoost(anotherVanillaRaidExists(null));
        World world = Bukkit.getWorld(worldId);
        if (world != null) {
            spawnRaidBabies(world, bellX, bellY, bellZ, 5);
        } else {
            plugin.getLogger().warning("Cannot spawn raid babies: the raid world is unavailable.");
        }
        Bukkit.broadcastMessage(
                message != null
                        ? message
                        : won
                                ? "§aThe Death Eater Raid has been defeated!"
                                : "§cThe Death Eater Raid has ended: the village was lost.");
    }

    private void spawnRaidBabies(World world, int bellX, int bellY, int bellZ, int count) {
        List<Location> locations = findBabySpawnLocations(world, bellX, bellY, bellZ);
        if (locations.isEmpty()) {
            plugin.getLogger()
                    .warning(
                            "Could not spawn raid baby villagers: no open grass, sand, podzol,"
                                    + " or snow was found within 30 blocks of the bell.");
            return;
        }
        Location bell = new Location(world, bellX + 0.5, bellY + 0.5, bellZ + 0.5);
        Villager.Type sourceType = null;
        int eligibleVillagers = 0;
        for (Entity entity :
                world.getNearbyEntities(
                        bell,
                        BABY_SKIN_SOURCE_RADIUS,
                        BABY_SKIN_SOURCE_RADIUS,
                        BABY_SKIN_SOURCE_RADIUS)) {
            if (entity instanceof Villager villager
                    && villager.isValid()
                    && !villager.isDead()
                    && villager.getLocation().distanceSquared(bell)
                            <= BABY_SKIN_SOURCE_RADIUS * BABY_SKIN_SOURCE_RADIUS
                    && ThreadLocalRandom.current().nextInt(++eligibleVillagers) == 0) {
                sourceType = villager.getVillagerType();
            }
        }
        final Villager.Type inheritedType = sourceType;
        int spawned = 0;
        for (int i = 0; i < count; i++) {
            try {
                Villager baby =
                        world.spawn(
                                locations.get(i % locations.size()),
                                Villager.class,
                                CreatureSpawnEvent.SpawnReason.CUSTOM,
                                child -> {
                                    child.setBaby();
                                    child.setVillagerType(
                                            inheritedType != null
                                                    ? inheritedType
                                                    : RAID_BABY_SKINS[
                                                            ThreadLocalRandom.current()
                                                                    .nextInt(
                                                                            RAID_BABY_SKINS
                                                                                    .length)]);
                                });
                if (baby != null && baby.isValid() && !baby.isDead()) {
                    spawned++;
                }
            } catch (IllegalArgumentException exception) {
                plugin.getLogger()
                        .warning("Could not spawn a raid baby villager: " + exception.getMessage());
            }
        }
        if (spawned < count) {
            plugin.getLogger()
                    .warning("Only " + spawned + " of " + count + " raid baby villagers spawned.");
        }
    }

    private static List<Location> findBabySpawnLocations(
            World world, int bellX, int bellY, int bellZ) {
        List<Location> locations = new ArrayList<>();
        for (int radius = 0; radius <= BABY_SPAWN_RADIUS; radius++) {
            for (int dx = -radius; dx <= radius; dx++) {
                for (int dz = -radius; dz <= radius; dz++) {
                    if (Math.max(Math.abs(dx), Math.abs(dz)) != radius) continue;
                    if (dx * dx + dz * dz > BABY_SPAWN_RADIUS * BABY_SPAWN_RADIUS) continue;
                    int x = bellX + dx, z = bellZ + dz;
                    if (!world.isChunkLoaded(x >> 4, z >> 4)) continue;
                    for (int i = 0; i <= 2 * BABY_SPAWN_RADIUS; i++) {
                        int offset = i == 0 ? 0 : (i % 2 == 1 ? (i + 1) / 2 : -i / 2);
                        if (dx * dx + dz * dz + offset * offset
                                > BABY_SPAWN_RADIUS * BABY_SPAWN_RADIUS) continue;
                        int y = bellY + offset;
                        if (y <= world.getMinHeight() || y + 1 >= world.getMaxHeight()) continue;
                        Block surface = world.getBlockAt(x, y - 1, z);
                        Material material = surface.getType();
                        if (material != Material.GRASS_BLOCK
                                && material != Material.SAND
                                && material != Material.PODZOL
                                && material != Material.SNOW_BLOCK
                                && material != Material.SNOW) continue;
                        double spawnY = y;
                        if (material == Material.SNOW) {
                            if (!(surface.getBlockData() instanceof Snow snow)) continue;
                            spawnY = y - 1 + snow.getLayers() / 8.0;
                        }
                        double heightFromBell = spawnY - bellY;
                        if (dx * dx + dz * dz + heightFromBell * heightFromBell
                                > BABY_SPAWN_RADIUS * BABY_SPAWN_RADIUS) continue;
                        Block feet = world.getBlockAt(x, y, z);
                        Block head = world.getBlockAt(x, y + 1, z);
                        if (feet.getType() != Material.SNOW
                                && feet.isPassable()
                                && head.isPassable()
                                && !feet.isLiquid()
                                && !head.isLiquid()) {
                            locations.add(new Location(world, x + 0.5, spawnY, z + 0.5));
                            if (locations.size() >= 5) return locations;
                            break;
                        }
                    }
                }
            }
        }
        return locations;
    }

    private void savePendingWork() {
        List<String> kills = new ArrayList<>();
        for (UUID id : pendingWaveKills) kills.add(id.toString());
        plugin.getConfig().set(KILLS_PATH, kills);
        plugin.saveConfig();
    }

    private void loadPendingWork() {
        for (String id : plugin.getConfig().getStringList(KILLS_PATH)) {
            try {
                pendingWaveKills.add(UUID.fromString(id));
            } catch (IllegalArgumentException ignored) {
                plugin.getLogger().warning("Ignoring invalid saved raid raider ID.");
            }
        }
    }

    /** Migrate any old queued births once, without leaving a retry queue. */
    private void spawnLegacyBirthsOnce() {
        List<Map<?, ?>> oldBirths = plugin.getConfig().getMapList(BIRTHS_PATH);
        if (oldBirths.isEmpty()) return;
        plugin.getConfig().set(BIRTHS_PATH, null);
        plugin.saveConfig();
        for (Map<?, ?> row : oldBirths) {
            try {
                World world = Bukkit.getWorld(UUID.fromString(String.valueOf(row.get("world"))));
                int x = ((Number) row.get("x")).intValue();
                int y = ((Number) row.get("y")).intValue();
                int z = ((Number) row.get("z")).intValue();
                int remaining = ((Number) row.get("remaining")).intValue();
                if (remaining < 1 || remaining > 5) throw new IllegalArgumentException();
                if (world == null) {
                    plugin.getLogger()
                            .warning("Cannot spawn old raid babies: their world is unavailable.");
                    continue;
                }
                world.getChunkAt(x >> 4, z >> 4);
                spawnRaidBabies(world, x, y, z, remaining);
            } catch (RuntimeException ignored) {
                plugin.getLogger().warning("Ignoring invalid saved raid birth batch.");
            }
        }
    }

    private boolean anotherVanillaRaidExists(org.bukkit.Raid excluded) {
        for (World world : Bukkit.getWorlds()) {
            for (org.bukkit.Raid raid : world.getRaids()) {
                if (raid != excluded && raid.getStatus() == org.bukkit.Raid.RaidStatus.ONGOING)
                    return true;
            }
        }
        return false;
    }

    private void applyBoost(boolean enabled) {
        if (enabled != boostActive) {
            boostActive = enabled;
            betterVillagers.setRaidBoost(enabled);
        }
    }

    private Location bellLocation(World world) {
        return new Location(world, bellX + 0.5, bellY + 0.5, bellZ + 0.5);
    }

    private static double horizontalDistanceSquared(Location a, Location b) {
        double x = a.getX() - b.getX(), z = a.getZ() - b.getZ();
        return x * x + z * z;
    }

    private void saveActiveRaid() {
        if (!active) return;
        plugin.getConfig().set(ACTIVE + ".world", worldId.toString());
        plugin.getConfig().set(ACTIVE + ".x", bellX);
        plugin.getConfig().set(ACTIVE + ".y", bellY);
        plugin.getConfig().set(ACTIVE + ".z", bellZ);
        plugin.getConfig().set(ACTIVE + ".wave", wave);
        plugin.getConfig().set(ACTIVE + ".total-waves", totalWaves);
        plugin.getConfig().set(ACTIVE + ".pending", pending);
        plugin.getConfig().set(ACTIVE + ".wave-size", waveSize);
        plugin.getConfig().set(ACTIVE + ".intermission", secondsUntilWave);
        plugin.getConfig().set(ACTIVE + ".wave-deadline", waveDeadlineMillis);
        List<Map<String, Object>> saved = new ArrayList<>();
        for (Map.Entry<UUID, RaiderState> entry : raiders.entrySet()) {
            Map<String, Object> row = new HashMap<>();
            row.put("uuid", entry.getKey().toString());
            row.put("chunk-x", entry.getValue().chunkX);
            row.put("chunk-z", entry.getValue().chunkZ);
            row.put("health", entry.getValue().healthFraction);
            saved.add(row);
        }
        plugin.getConfig().set(ACTIVE + ".raiders", saved);
        plugin.saveConfig();
    }

    private void loadActiveRaid() {
        String world = plugin.getConfig().getString(ACTIVE + ".world");
        if (world == null) return;
        try {
            worldId = UUID.fromString(world);
            bellX = plugin.getConfig().getInt(ACTIVE + ".x");
            bellY = plugin.getConfig().getInt(ACTIVE + ".y");
            bellZ = plugin.getConfig().getInt(ACTIVE + ".z");
            wave = plugin.getConfig().getInt(ACTIVE + ".wave");
            totalWaves = plugin.getConfig().getInt(ACTIVE + ".total-waves");
            pending = plugin.getConfig().getInt(ACTIVE + ".pending");
            waveSize = plugin.getConfig().getInt(ACTIVE + ".wave-size");
            secondsUntilWave = plugin.getConfig().getInt(ACTIVE + ".intermission");
            waveDeadlineMillis =
                    plugin.getConfig()
                            .getLong(
                                    ACTIVE + ".wave-deadline",
                                    wave > 0
                                                    && (pending > 0
                                                            || !plugin.getConfig()
                                                                    .getMapList(ACTIVE + ".raiders")
                                                                    .isEmpty())
                                            ? System.currentTimeMillis() + WAVE_DURATION_MILLIS
                                            : 0L);
            if (wave < 0
                    || totalWaves < 3
                    || totalWaves > 5
                    || wave > totalWaves
                    || pending < 0
                    || waveSize < pending) throw new IllegalArgumentException();
            for (Map<?, ?> row : plugin.getConfig().getMapList(ACTIVE + ".raiders")) {
                UUID id = UUID.fromString(String.valueOf(row.get("uuid")));
                int cx = ((Number) row.get("chunk-x")).intValue();
                int cz = ((Number) row.get("chunk-z")).intValue();
                double health = ((Number) row.get("health")).doubleValue();
                raiders.put(id, new RaiderState(cx, cz, health));
            }
            active = true;
            bar = Bukkit.createBossBar("Death Eater Raid", BarColor.RED, BarStyle.SOLID);
            applyBoost(true);
        } catch (RuntimeException e) {
            raiders.clear();
            plugin.getLogger()
                    .warning("Could not restore the saved Death Eater Raid: " + e.getMessage());
        }
    }

    private static final class RaiderState {
        private int chunkX, chunkZ;
        private double healthFraction;

        RaiderState(Location location, double health) {
            this(location.getBlockX() >> 4, location.getBlockZ() >> 4, health);
        }

        RaiderState(int x, int z, double health) {
            chunkX = x;
            chunkZ = z;
            healthFraction = health;
        }

        void update(Entity entity) {
            Location location = entity.getLocation();
            chunkX = location.getBlockX() >> 4;
            chunkZ = location.getBlockZ() >> 4;
            if (entity instanceof Raider p
                    && p.getAttribute(Attribute.GENERIC_MAX_HEALTH) != null) {
                double max = p.getAttribute(Attribute.GENERIC_MAX_HEALTH).getValue();
                healthFraction = max <= 0 ? 0 : Math.max(0, Math.min(1, p.getHealth() / max));
            }
        }
    }
}
