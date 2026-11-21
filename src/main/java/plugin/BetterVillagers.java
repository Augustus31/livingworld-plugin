package plugin;

import com.destroystokyo.paper.entity.Pathfinder;

import org.bukkit.Bukkit;
import org.bukkit.ChatColor;
import org.bukkit.GameRule;
import org.bukkit.Location;
import org.bukkit.Material;
import org.bukkit.NamespacedKey;
import org.bukkit.World;
import org.bukkit.block.Block;
import org.bukkit.command.Command;
import org.bukkit.command.CommandExecutor;
import org.bukkit.command.CommandSender;
import org.bukkit.command.PluginCommand;
import org.bukkit.entity.Entity;
import org.bukkit.entity.IronGolem;
import org.bukkit.entity.LivingEntity;
import org.bukkit.entity.Player;
import org.bukkit.entity.Projectile;
import org.bukkit.entity.Villager;
import org.bukkit.entity.memory.MemoryKey;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.Listener;
import org.bukkit.event.entity.CreatureSpawnEvent;
import org.bukkit.event.entity.EntityBreedEvent;
import org.bukkit.event.entity.EntityDamageByEntityEvent;
import org.bukkit.event.entity.EntityDeathEvent;
import org.bukkit.event.entity.EntityTargetLivingEntityEvent;
import org.bukkit.event.world.ChunkLoadEvent;
import org.bukkit.event.world.EntitiesUnloadEvent;
import org.bukkit.inventory.ItemStack;
import org.bukkit.persistence.PersistentDataType;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.projectiles.ProjectileSource;
import org.bukkit.scheduler.BukkitTask;
import org.bukkit.util.Vector;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ThreadLocalRandom;

/** Villager breeding rules and the iron-golem height response. */
public final class BetterVillagers implements Listener, CommandExecutor {
    private static final double BREEDING_RANGE = 8.0;
    private static final double BREEDING_RANGE_SQUARED = BREEDING_RANGE * BREEDING_RANGE;
    private static final double BREEDING_COOLDOWN_RADIUS = 50.0;
    private static final double BREEDING_COOLDOWN_RADIUS_SQUARED =
            BREEDING_COOLDOWN_RADIUS * BREEDING_COOLDOWN_RADIUS;
    private static final long BREEDING_COOLDOWN_TICKS = 5L * 24_000L;
    private static final double GOLEM_FLEE_DISTANCE = 6.0;
    private static final double GOLEM_REQUIRED_SEPARATION = 5.0;
    private static final double GOLEM_CLOSE_RANGE = 10.0;
    private static final double GOLEM_CLOSE_RANGE_SQUARED = GOLEM_CLOSE_RANGE * GOLEM_CLOSE_RANGE;
    private static final double GOLEM_NOTICE_HORIZONTAL_RANGE = 15.0;
    private static final double GOLEM_NOTICE_VERTICAL_RANGE = 10.0;
    private static final double GOLEM_VILLAGER_DETECTION_RANGE = 16.0;
    private static final double MIN_GOLEM_RATE = 0.0;
    private static final double MAX_GOLEM_RATE = 10.0;

    private static final String COOLDOWN_WAVES_PATH = "better-villagers.breeding-cooldown-waves";
    private static final String GOLEM_RATE_PATH = "better-villagers.golem-rate";

    private final JavaPlugin plugin;
    private final NamespacedKey villagerCooldownKey;
    private final Map<UUID, GolemFleeState> fleeingGolems = new HashMap<>();
    private final Set<UUID> managedGolemMemories = new HashSet<>();
    private final List<CooldownWave> cooldownWaves = new ArrayList<>();
    private BukkitTask tickTask;
    private int waveCleanupTicks;
    private double golemRate;
    private boolean raidBoost;
    private Raid raidSystem;

    public BetterVillagers(JavaPlugin plugin) {
        this.plugin = plugin;
        this.villagerCooldownKey = new NamespacedKey(plugin, "breeding_cooldown_until");
        this.golemRate = loadGolemRate();
        loadCooldownWaves();
    }

    public void register() {
        plugin.getServer().getPluginManager().registerEvents(this, plugin);
        PluginCommand command = plugin.getCommand("vgolemrate");
        if (command == null) {
            throw new IllegalStateException("The vgolemrate command is missing from plugin.yml.");
        }
        command.setExecutor(this);
        raidSystem = new Raid(plugin, this);
        raidSystem.register();
        applyCooldownWavesToLoadedVillagers();
        tickTask = plugin.getServer().getScheduler().runTaskTimer(plugin, this::tick, 1L, 10L);
    }

    @Override
    public boolean onCommand(CommandSender sender, Command command, String label, String[] args) {
        if (!command.getName().equalsIgnoreCase("vgolemrate")) {
            return false;
        }
        if (args.length != 1) {
            sender.sendMessage(ChatColor.YELLOW + "Usage: /vgolemrate <multiplier>");
            sender.sendMessage(
                    ChatColor.GRAY
                            + "Choose a number from 0 to 10. Decimals are allowed; 1 is normal.");
            return true;
        }

        final double requestedRate;
        try {
            requestedRate = Double.parseDouble(args[0]);
        } catch (NumberFormatException exception) {
            sender.sendMessage(ChatColor.RED + "The multiplier must be a number from 0 to 10.");
            return true;
        }
        if (!Double.isFinite(requestedRate)
                || requestedRate < MIN_GOLEM_RATE
                || requestedRate > MAX_GOLEM_RATE) {
            sender.sendMessage(ChatColor.RED + "The multiplier must be between 0 and 10.");
            return true;
        }

        double previousRate = effectiveGolemRate();
        golemRate = requestedRate;
        plugin.getConfig().set(GOLEM_RATE_PATH, golemRate);
        plugin.saveConfig();
        sender.sendMessage(
                ChatColor.GREEN
                        + "Village iron golem spawn rate set to "
                        + formatRate(golemRate)
                        + "x normal.");
        if (effectiveGolemRate() < previousRate) {
            int removed = removeExcessLoadedGolems();
            sender.sendMessage(ChatColor.GRAY + "Removed " + removed + " excess loaded golem(s).");
        }
        return true;
    }

    public void shutdown() {
        if (raidSystem != null) {
            raidSystem.shutdown();
        }
        if (tickTask != null) {
            tickTask.cancel();
        }
        for (GolemFleeState state : fleeingGolems.values()) {
            if (state.golem.isValid()) {
                state.golem.getPathfinder().stopPathfinding();
                state.golem.setTarget(null);
            }
        }
        fleeingGolems.clear();
        clearManagedGolemMemories();
        saveCooldownWaves();
    }

    double effectiveGolemRate() {
        return golemRate * (raidBoost ? 3.0 : 1.0);
    }

    void setRaidBoost(boolean enabled) {
        double previous = effectiveGolemRate();
        raidBoost = enabled;
        if (effectiveGolemRate() < previous) {
            removeExcessLoadedGolems();
        }
    }

    /** Blocks vanilla breeding when either parent has an active cooldown. */
    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onVanillaVillagerBreed(EntityBreedEvent event) {
        if (!(event.getEntity() instanceof Villager baby)
                || !(event.getMother() instanceof Villager mother)
                || !(event.getFather() instanceof Villager father)) {
            return;
        }

        if (hasBreedingCooldown(mother) || hasBreedingCooldown(father)) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSuccessfulVillagerBirth(EntityBreedEvent event) {
        if (event.getEntity() instanceof Villager baby
                && event.getMother() instanceof Villager
                && event.getFather() instanceof Villager) {
            applyBirthCooldown(baby);
        }
    }

    /**
     * Tracks newly loaded villagers so entities saved in unloaded chunks also receive any
     * still-active birth-radius cooldown.
     */
    @EventHandler
    public void onChunkLoad(ChunkLoadEvent event) {
        for (Entity entity : event.getChunk().getEntities()) {
            if (entity instanceof Villager villager) {
                applyCooldownWaves(villager);
            }
        }
    }

    @EventHandler
    public void onEntitiesUnload(EntitiesUnloadEvent event) {
        for (Entity entity : event.getEntities()) {
            if (entity instanceof Villager villager
                    && managedGolemMemories.remove(villager.getUniqueId())) {
                villager.setMemory(MemoryKey.GOLEM_DETECTED_RECENTLY, null);
            }
            if (entity instanceof IronGolem golem) {
                GolemFleeState state = fleeingGolems.remove(golem.getUniqueId());
                if (state != null && golem.isValid()) {
                    golem.getPathfinder().stopPathfinding();
                    golem.setTarget(null);
                }
            }
        }
    }

    /** Cancels a golem's target selection when that target is vertically unsafe. */
    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onIronGolemTarget(EntityTargetLivingEntityEvent event) {
        if (!(event.getEntity() instanceof IronGolem golem)) {
            return;
        }
        LivingEntity target = event.getTarget();
        if (target != null && !(target instanceof Player)) {
            GolemFleeState state = fleeingGolems.remove(golem.getUniqueId());
            if (state != null) golem.getPathfinder().stopPathfinding();
            return;
        }
        if (target != null && isVerticallyUnsafeTarget(golem, target)) {
            event.setCancelled(true);
            startGolemFlee(golem, target);
        }
    }

    /** Damage events are a second guard if target selection was missed. */
    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onIronGolemDamage(EntityDamageByEntityEvent event) {
        if (!(event.getDamager() instanceof IronGolem golem)
                || !(event.getEntity() instanceof LivingEntity target)
                || !isVerticallyUnsafeTarget(golem, target)) {
            return;
        }
        event.setCancelled(true);
        startGolemFlee(golem, target);
    }

    /** Limits the iron drop from an iron golem to one ingot. */
    @EventHandler(priority = EventPriority.HIGHEST)
    public void onIronGolemDeath(EntityDeathEvent event) {
        if (!(event.getEntity() instanceof IronGolem golem)) {
            return;
        }
        event.getDrops().removeIf(drop -> drop.getType() == Material.IRON_INGOT);
        if (Boolean.TRUE.equals(golem.getWorld().getGameRuleValue(GameRule.DO_MOB_LOOT))) {
            event.getDrops().add(new ItemStack(Material.IRON_INGOT, 1));
        }
    }

    /** Alerts nearby iron golems when a player damages a villager. */
    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onVillagerAttacked(EntityDamageByEntityEvent event) {
        if (!(event.getEntity() instanceof Villager villager)) {
            return;
        }
        Player attacker = findPlayerAttacker(event.getDamager());
        if (attacker == null || !attacker.getWorld().equals(villager.getWorld())) {
            return;
        }

        List<UUID> alertedGolems = new ArrayList<>();
        Location villagerLocation = villager.getLocation();
        for (Entity entity :
                villager.getNearbyEntities(
                        GOLEM_NOTICE_HORIZONTAL_RANGE,
                        GOLEM_NOTICE_VERTICAL_RANGE,
                        GOLEM_NOTICE_HORIZONTAL_RANGE)) {
            if (entity instanceof IronGolem golem
                    && isWithinGolemNoticeRange(golem.getLocation(), villagerLocation)) {
                alertedGolems.add(golem.getUniqueId());
            }
        }
        if (alertedGolems.isEmpty()) {
            return;
        }

        UUID attackerId = attacker.getUniqueId();
        Bukkit.getScheduler()
                .runTask(
                        plugin,
                        () -> {
                            Entity currentAttacker = Bukkit.getEntity(attackerId);
                            if (!(currentAttacker instanceof Player player) || !player.isOnline()) {
                                return;
                            }
                            for (UUID golemId : alertedGolems) {
                                Entity entity = Bukkit.getEntity(golemId);
                                if (entity instanceof IronGolem golem
                                        && golem.isValid()
                                        && !golem.isDead()
                                        && golem.getWorld().equals(player.getWorld())) {
                                    golem.setTarget(player);
                                }
                            }
                        });
    }

    /** Reduces the chance of a natural village-defense spawn when the multiplier is below 1. */
    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onNaturalGolemSpawnRateLimit(CreatureSpawnEvent event) {
        if (event.getEntity() instanceof IronGolem
                && event.getSpawnReason() == CreatureSpawnEvent.SpawnReason.VILLAGE_DEFENSE
                && effectiveGolemRate() < 1.0
                && ThreadLocalRandom.current().nextDouble() >= effectiveGolemRate()) {
            event.setCancelled(true);
        }
    }

    /** Adds statistically scaled extra golems after each successful village-defense spawn. */
    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onNaturalGolemSpawnRateBoost(CreatureSpawnEvent event) {
        if (!(event.getEntity() instanceof IronGolem)
                || event.getSpawnReason() != CreatureSpawnEvent.SpawnReason.VILLAGE_DEFENSE
                || effectiveGolemRate() <= 1.0) {
            return;
        }

        double extraRate = effectiveGolemRate() - 1.0;
        int extraGolems = (int) Math.floor(extraRate);
        if (ThreadLocalRandom.current().nextDouble() < extraRate - extraGolems) {
            extraGolems++;
        }
        if (extraGolems <= 0) {
            return;
        }

        World world = event.getLocation().getWorld();
        Location origin = event.getLocation().clone();
        int additionalCount = extraGolems;
        plugin.getServer()
                .getScheduler()
                .runTask(plugin, () -> spawnExtraGolems(world, origin, additionalCount));
    }

    private double loadGolemRate() {
        double configuredRate = plugin.getConfig().getDouble(GOLEM_RATE_PATH, 1.0);
        if (!Double.isFinite(configuredRate)
                || configuredRate < MIN_GOLEM_RATE
                || configuredRate > MAX_GOLEM_RATE) {
            plugin.getLogger()
                    .warning(
                            "Invalid "
                                    + GOLEM_RATE_PATH
                                    + " value; using the default rate of 1.0.");
            return 1.0;
        }
        return configuredRate;
    }

    private static Player findPlayerAttacker(Entity damager) {
        if (damager instanceof Player player) {
            return player;
        }
        if (damager instanceof Projectile projectile) {
            ProjectileSource shooter = projectile.getShooter();
            if (shooter instanceof Player player) {
                return player;
            }
        }
        return null;
    }

    private static boolean isWithinGolemNoticeRange(Location golem, Location villager) {
        if (!golem.getWorld().equals(villager.getWorld())) {
            return false;
        }
        return Math.abs(golem.getX() - villager.getX()) <= GOLEM_NOTICE_HORIZONTAL_RANGE
                && Math.abs(golem.getZ() - villager.getZ()) <= GOLEM_NOTICE_HORIZONTAL_RANGE
                && Math.abs(golem.getY() - villager.getY()) <= GOLEM_NOTICE_VERTICAL_RANGE;
    }

    private void spawnExtraGolems(World world, Location origin, int requestedCount) {
        if (world == null
                || !world.isChunkLoaded(origin.getBlockX() >> 4, origin.getBlockZ() >> 4)) {
            return;
        }

        // Avoid adding a full batch when villagers are replacing a missing golem.
        // The original spawn is already present by the time this task runs.
        int cap = (int) Math.ceil(effectiveGolemRate());
        int nearbyGolems = countNearbyGolems(world, origin, cap);
        requestedCount = Math.min(requestedCount, Math.max(0, cap - nearbyGolems));
        if (requestedCount == 0) {
            return;
        }

        List<Location> candidates = new ArrayList<>();
        double[] radii = {2.5, 4.5, 6.5};
        int[] verticalOffsets = {0, 1, -1};
        double startingAngle = ThreadLocalRandom.current().nextDouble(0.0, 2.0 * Math.PI);
        for (double radius : radii) {
            for (int angleIndex = 0; angleIndex < 16; angleIndex++) {
                double angle = startingAngle + angleIndex * (2.0 * Math.PI / 16.0);
                int blockX = origin.getBlockX() + (int) Math.round(Math.cos(angle) * radius);
                int blockZ = origin.getBlockZ() + (int) Math.round(Math.sin(angle) * radius);
                for (int yOffset : verticalOffsets) {
                    Location candidate =
                            new Location(
                                    world,
                                    blockX + 0.5,
                                    origin.getBlockY() + yOffset,
                                    blockZ + 0.5);
                    if (world.isChunkLoaded(
                            candidate.getBlockX() >> 4, candidate.getBlockZ() >> 4)) {
                        candidates.add(candidate);
                    }
                }
            }
        }
        Collections.shuffle(candidates, ThreadLocalRandom.current());

        int spawned = 0;
        for (Location candidate : candidates) {
            if (!hasGolemSpawnSpace(world, candidate)) {
                continue;
            }
            try {
                world.spawn(candidate, IronGolem.class, CreatureSpawnEvent.SpawnReason.CUSTOM);
                spawned++;
                if (spawned >= requestedCount) {
                    return;
                }
            } catch (IllegalArgumentException exception) {
                // The server or another plugin may reject this location. Try another candidate.
            }
        }

        if (spawned < requestedCount) {
            plugin.getLogger()
                    .fine(
                            "Could only place "
                                    + spawned
                                    + " of "
                                    + requestedCount
                                    + " extra village iron golems at "
                                    + origin.getBlockX()
                                    + ", "
                                    + origin.getBlockY()
                                    + ", "
                                    + origin.getBlockZ()
                                    + ".");
        }
    }

    private static boolean hasGolemSpawnSpace(World world, Location candidate) {
        int blockX = candidate.getBlockX();
        int blockY = candidate.getBlockY();
        int blockZ = candidate.getBlockZ();
        Block floor = world.getBlockAt(blockX, blockY - 1, blockZ);
        if (!floor.getType().isSolid()) {
            return false;
        }
        for (int y = blockY; y < blockY + 3; y++) {
            if (!world.getBlockAt(blockX, y, blockZ).isPassable()) {
                return false;
            }
        }
        for (Entity entity : world.getNearbyEntities(candidate, 1.25, 3.0, 1.25)) {
            if (entity instanceof LivingEntity
                    && Math.abs(entity.getLocation().getX() - candidate.getX()) < 1.25
                    && Math.abs(entity.getLocation().getY() - candidate.getY()) < 3.0
                    && Math.abs(entity.getLocation().getZ() - candidate.getZ()) < 1.25) {
                return false;
            }
        }
        return true;
    }

    private static String formatRate(double rate) {
        return java.math.BigDecimal.valueOf(rate).stripTrailingZeros().toPlainString();
    }

    private boolean hasBreedingCooldown(Villager villager) {
        Long until =
                villager.getPersistentDataContainer()
                        .get(villagerCooldownKey, PersistentDataType.LONG);
        if (until == null) {
            return false;
        }
        if (until > villager.getWorld().getFullTime()) {
            return true;
        }
        villager.getPersistentDataContainer().remove(villagerCooldownKey);
        return false;
    }

    void applyBirthCooldown(Villager newborn) {
        World world = newborn.getWorld();
        Location birth = newborn.getLocation();
        long expiry = world.getFullTime() + BREEDING_COOLDOWN_TICKS;

        CooldownWave wave =
                new CooldownWave(world.getUID(), birth.getX(), birth.getY(), birth.getZ(), expiry);
        cooldownWaves.add(wave);

        applyCooldown(newborn, expiry);
        for (Entity entity :
                newborn.getNearbyEntities(
                        BREEDING_COOLDOWN_RADIUS,
                        BREEDING_COOLDOWN_RADIUS,
                        BREEDING_COOLDOWN_RADIUS)) {
            if (entity instanceof Villager villager
                    && villager.getLocation().distanceSquared(birth)
                            <= BREEDING_COOLDOWN_RADIUS_SQUARED) {
                applyCooldown(villager, expiry);
            }
        }
        saveCooldownWaves();
    }

    private void applyCooldown(Villager villager, long expiry) {
        Long existing =
                villager.getPersistentDataContainer()
                        .get(villagerCooldownKey, PersistentDataType.LONG);
        if (existing == null || existing < expiry) {
            villager.getPersistentDataContainer()
                    .set(villagerCooldownKey, PersistentDataType.LONG, expiry);
        }
    }

    private void applyCooldownWavesToLoadedVillagers() {
        for (World world : Bukkit.getWorlds()) {
            for (Villager villager : world.getEntitiesByClass(Villager.class)) {
                applyCooldownWaves(villager);
            }
        }
    }

    private void applyCooldownWaves(Villager villager) {
        long now = villager.getWorld().getFullTime();
        Location location = villager.getLocation();
        for (CooldownWave wave : cooldownWaves) {
            if (wave.expiry > now
                    && wave.worldId.equals(villager.getWorld().getUID())
                    && squaredDistance(location, wave.x, wave.y, wave.z)
                            <= BREEDING_COOLDOWN_RADIUS_SQUARED) {
                applyCooldown(villager, wave.expiry);
            }
        }
    }

    private void loadCooldownWaves() {
        for (Map<?, ?> stored : plugin.getConfig().getMapList(COOLDOWN_WAVES_PATH)) {
            try {
                UUID worldId = UUID.fromString(String.valueOf(stored.get("world")));
                double x = ((Number) stored.get("x")).doubleValue();
                double y = ((Number) stored.get("y")).doubleValue();
                double z = ((Number) stored.get("z")).doubleValue();
                long expiry = ((Number) stored.get("expiry")).longValue();
                World world = Bukkit.getWorld(worldId);
                if (world == null || expiry > world.getFullTime()) {
                    cooldownWaves.add(new CooldownWave(worldId, x, y, z, expiry));
                }
            } catch (IllegalArgumentException | NullPointerException ignored) {
                plugin.getLogger().warning("Ignoring malformed villager breeding cooldown entry.");
            }
        }
    }

    private void saveCooldownWaves() {
        List<Map<String, Object>> stored = new ArrayList<>();
        for (CooldownWave wave : cooldownWaves) {
            World world = Bukkit.getWorld(wave.worldId);
            if (world != null && wave.expiry <= world.getFullTime()) {
                continue;
            }
            Map<String, Object> values = new HashMap<>();
            values.put("world", wave.worldId.toString());
            values.put("x", wave.x);
            values.put("y", wave.y);
            values.put("z", wave.z);
            values.put("expiry", wave.expiry);
            stored.add(values);
        }
        plugin.getConfig().set(COOLDOWN_WAVES_PATH, stored);
        plugin.saveConfig();
    }

    private void tick() {
        detectUnsafeGolemTargets();
        updateVillagerGolemMemories();
        long now = System.currentTimeMillis();
        for (GolemFleeState state : new ArrayList<>(fleeingGolems.values())) {
            tickGolemFlee(state, now);
        }
        breedAvailableVillagers();

        if (++waveCleanupTicks >= 1200) {
            waveCleanupTicks = 0;
            if (removeExpiredCooldownWaves()) {
                saveCooldownWaves();
            }
        }
    }

    /** Adjusts the local golem detection threshold used by each villager. */
    private void updateVillagerGolemMemories() {
        if (effectiveGolemRate() <= 1.0) {
            clearManagedGolemMemories();
            return;
        }
        for (World world : Bukkit.getWorlds()) {
            for (Villager villager : world.getEntitiesByClass(Villager.class)) {
                if (!villager.isValid() || villager.isDead() || !villager.isAdult()) {
                    continue;
                }
                int cap = localGolemCap(villager);
                int nearby = countNearbyGolems(world, villager.getLocation(), cap);
                if (nearby >= cap) {
                    villager.setMemory(MemoryKey.GOLEM_DETECTED_RECENTLY, true);
                    managedGolemMemories.add(villager.getUniqueId());
                } else if (nearby > 0) {
                    villager.setMemory(MemoryKey.GOLEM_DETECTED_RECENTLY, null);
                    managedGolemMemories.remove(villager.getUniqueId());
                } else if (managedGolemMemories.remove(villager.getUniqueId())) {
                    villager.setMemory(MemoryKey.GOLEM_DETECTED_RECENTLY, null);
                }
            }
        }
    }

    private void clearManagedGolemMemories() {
        for (UUID id : managedGolemMemories) {
            Entity entity = Bukkit.getEntity(id);
            if (entity instanceof Villager villager && villager.isValid()) {
                villager.setMemory(MemoryKey.GOLEM_DETECTED_RECENTLY, null);
            }
        }
        managedGolemMemories.clear();
    }

    private int localGolemCap(Villager villager) {
        double rate = effectiveGolemRate();
        int whole = (int) Math.floor(rate);
        double fraction = rate - whole;
        // A stable choice avoids changing the target on every tick.
        long bits = villager.getUniqueId().getMostSignificantBits();
        double sample = (bits >>> 11) * 0x1.0p-53;
        return whole + (sample < fraction ? 1 : 0);
    }

    /** Applies a reduced threshold to golems near loaded villagers. */
    private int removeExcessLoadedGolems() {
        int removed = 0;
        for (World world : Bukkit.getWorlds()) {
            for (Villager villager : world.getEntitiesByClass(Villager.class)) {
                if (!villager.isValid() || villager.isDead() || !villager.isAdult()) {
                    continue;
                }
                List<IronGolem> nearby = new ArrayList<>();
                for (Entity entity :
                        villager.getNearbyEntities(
                                GOLEM_VILLAGER_DETECTION_RANGE,
                                GOLEM_VILLAGER_DETECTION_RANGE,
                                GOLEM_VILLAGER_DETECTION_RANGE)) {
                    if (entity instanceof IronGolem golem && golem.isValid() && !golem.isDead()) {
                        nearby.add(golem);
                    }
                }
                int excess = nearby.size() - localGolemCap(villager);
                for (IronGolem golem : nearby) {
                    if (excess <= 0) {
                        break;
                    }
                    if (golem.isPlayerCreated() || golem.getCustomName() != null) {
                        continue;
                    }
                    golem.remove();
                    fleeingGolems.remove(golem.getUniqueId());
                    excess--;
                    removed++;
                }
            }
        }
        return removed;
    }

    private static int countNearbyGolems(World world, Location center, int stopAt) {
        int count = 0;
        for (Entity entity :
                world.getNearbyEntities(
                        center,
                        GOLEM_VILLAGER_DETECTION_RANGE,
                        GOLEM_VILLAGER_DETECTION_RANGE,
                        GOLEM_VILLAGER_DETECTION_RANGE)) {
            if (entity instanceof IronGolem golem && golem.isValid() && !golem.isDead()) {
                count++;
                if (count >= stopAt) {
                    break;
                }
            }
        }
        return count;
    }

    private void breedAvailableVillagers() {
        for (World world : Bukkit.getWorlds()) {
            Map<Cell, List<Villager>> grid = new HashMap<>();
            List<Villager> adults = new ArrayList<>();
            for (Villager villager : world.getEntitiesByClass(Villager.class)) {
                if (villager.isValid()
                        && !villager.isDead()
                        && villager.isAdult()
                        && !hasBreedingCooldown(villager)) {
                    adults.add(villager);
                }
            }
            adults.sort(Comparator.comparing(v -> v.getUniqueId().toString()));
            for (Villager villager : adults) {
                grid.computeIfAbsent(
                                Cell.from(villager.getLocation()), ignored -> new ArrayList<>())
                        .add(villager);
            }

            Set<UUID> paired = new HashSet<>();
            for (Villager first : adults) {
                if (paired.contains(first.getUniqueId()) || hasBreedingCooldown(first)) {
                    continue;
                }
                Villager closest = findAvailableMate(first, grid, paired);
                if (closest == null) {
                    continue;
                }
                Villager baby = spawnBaby(first, closest);
                if (baby == null) {
                    continue;
                }
                paired.add(first.getUniqueId());
                paired.add(closest.getUniqueId());
                applyBirthCooldown(baby);
            }
        }
    }

    private Villager findAvailableMate(
            Villager first, Map<Cell, List<Villager>> grid, Set<UUID> paired) {
        Cell home = Cell.from(first.getLocation());
        Villager closest = null;
        double closestDistance = BREEDING_RANGE_SQUARED;
        for (int dx = -1; dx <= 1; dx++) {
            for (int dy = -1; dy <= 1; dy++) {
                for (int dz = -1; dz <= 1; dz++) {
                    List<Villager> candidates =
                            grid.get(new Cell(home.x + dx, home.y + dy, home.z + dz));
                    if (candidates == null) continue;
                    for (Villager candidate : candidates) {
                        if (candidate == first
                                || paired.contains(candidate.getUniqueId())
                                || hasBreedingCooldown(candidate)) {
                            continue;
                        }
                        double distance =
                                candidate.getLocation().distanceSquared(first.getLocation());
                        if (distance <= closestDistance) {
                            closestDistance = distance;
                            closest = candidate;
                        }
                    }
                }
            }
        }
        return closest;
    }

    private Villager spawnBaby(Villager first, Villager second) {
        Location spawnLocation = first.getLocation();
        Villager.Type inheritedType =
                ThreadLocalRandom.current().nextBoolean()
                        ? first.getVillagerType()
                        : second.getVillagerType();
        try {
            return first.getWorld()
                    .spawn(
                            spawnLocation,
                            Villager.class,
                            CreatureSpawnEvent.SpawnReason.BREEDING,
                            baby -> {
                                baby.setAge(-24_000);
                                baby.setVillagerType(inheritedType);
                            });
        } catch (IllegalArgumentException exception) {
            plugin.getLogger()
                    .warning("Could not spawn a villager child: " + exception.getMessage());
            return null;
        }
    }

    private void detectUnsafeGolemTargets() {
        for (World world : Bukkit.getWorlds()) {
            for (IronGolem golem : world.getEntitiesByClass(IronGolem.class)) {
                LivingEntity target = golem.getTarget();
                if (target != null && isVerticallyUnsafeTarget(golem, target)) {
                    startGolemFlee(golem, target);
                }
            }
        }
    }

    private void startGolemFlee(IronGolem golem, LivingEntity target) {
        GolemFleeState state = fleeingGolems.get(golem.getUniqueId());
        if (state == null || !state.target.getUniqueId().equals(target.getUniqueId())) {
            fleeingGolems.put(
                    golem.getUniqueId(),
                    new GolemFleeState(golem, target, golem.getLocation().clone()));
            golem.getPathfinder().stopPathfinding();
        }
        golem.setTarget(null);
    }

    private static boolean isVerticallyUnsafeTarget(IronGolem golem, LivingEntity target) {
        if (!(target instanceof Player) || !golem.getWorld().equals(target.getWorld())) {
            return false;
        }
        double verticalDifference =
                target.getBoundingBox().getMinY() - golem.getBoundingBox().getMinY();
        if (verticalDifference <= -2.0) {
            return true;
        }
        return verticalDifference >= 3.0
                && golem.getLocation().distanceSquared(target.getLocation())
                        < GOLEM_CLOSE_RANGE_SQUARED;
    }

    private void tickGolemFlee(GolemFleeState state, long now) {
        IronGolem golem = state.golem;
        LivingEntity target = state.target;
        if (!golem.isValid()
                || golem.isDead()
                || !target.isValid()
                || target.isDead()
                || !golem.getWorld().equals(target.getWorld())) {
            fleeingGolems.remove(golem.getUniqueId());
            return;
        }
        LivingEntity currentTarget = golem.getTarget();
        if (currentTarget != null && !(currentTarget instanceof Player)) {
            fleeingGolems.remove(golem.getUniqueId());
            golem.getPathfinder().stopPathfinding();
            return;
        }
        if (!isVerticallyUnsafeTarget(golem, target)) {
            fleeingGolems.remove(golem.getUniqueId());
            golem.getPathfinder().stopPathfinding();
            return;
        }

        golem.setTarget(null);
        boolean movedFiveBlocks =
                horizontalDistanceSquared(golem.getLocation(), state.origin) >= 25.0;
        boolean threatTooClose = golem.getLocation().distanceSquared(target.getLocation()) < 25.0;
        if ((!movedFiveBlocks || threatTooClose) && now >= state.nextMoveAt) {
            Pathfinder.PathResult path = findGolemFleePath(golem, target);
            if (path != null) {
                golem.getPathfinder().moveTo(path, 1.0);
            }
            state.nextMoveAt = now + 500L;
        } else if (movedFiveBlocks && !threatTooClose) {
            golem.getPathfinder().stopPathfinding();
        }
    }

    private Pathfinder.PathResult findGolemFleePath(IronGolem golem, LivingEntity target) {
        Location current = golem.getLocation();
        Vector away = current.toVector().subtract(target.getLocation().toVector());
        away.setY(0.0);
        double baseAngle;
        if (away.lengthSquared() < 0.0001) {
            baseAngle = (Math.abs(golem.getUniqueId().hashCode()) % 360) * Math.PI / 180.0;
        } else {
            baseAngle = Math.atan2(away.getZ(), away.getX());
        }

        double[] offsets = {0.0, 0.45, -0.45, 0.9, -0.9, 1.35, -1.35};
        for (double offset : offsets) {
            double angle = baseAngle + offset;
            Location candidate =
                    current.clone()
                            .add(
                                    Math.cos(angle) * GOLEM_FLEE_DISTANCE,
                                    0.0,
                                    Math.sin(angle) * GOLEM_FLEE_DISTANCE);
            Pathfinder.PathResult path = golem.getPathfinder().findPath(candidate);
            if (path == null || path.getFinalPoint() == null) continue;
            if (path.getFinalPoint().distanceSquared(target.getLocation())
                            >= GOLEM_REQUIRED_SEPARATION * GOLEM_REQUIRED_SEPARATION
                    && horizontalDistanceSquared(path.getFinalPoint(), current)
                            >= GOLEM_REQUIRED_SEPARATION * GOLEM_REQUIRED_SEPARATION) {
                return path;
            }
        }
        return null;
    }

    private static double horizontalDistanceSquared(Location first, Location second) {
        double dx = first.getX() - second.getX();
        double dz = first.getZ() - second.getZ();
        return dx * dx + dz * dz;
    }

    private static double squaredDistance(Location location, double x, double y, double z) {
        double dx = location.getX() - x;
        double dy = location.getY() - y;
        double dz = location.getZ() - z;
        return dx * dx + dy * dy + dz * dz;
    }

    private boolean removeExpiredCooldownWaves() {
        int oldSize = cooldownWaves.size();
        cooldownWaves.removeIf(
                wave -> {
                    World world = Bukkit.getWorld(wave.worldId);
                    return world != null && wave.expiry <= world.getFullTime();
                });
        return oldSize != cooldownWaves.size();
    }

    private record Cell(int x, int y, int z) {
        private static Cell from(Location location) {
            return new Cell(
                    (int) Math.floor(location.getX() / BREEDING_RANGE),
                    (int) Math.floor(location.getY() / BREEDING_RANGE),
                    (int) Math.floor(location.getZ() / BREEDING_RANGE));
        }
    }

    private static final class GolemFleeState {
        private final IronGolem golem;
        private final LivingEntity target;
        private final Location origin;
        private long nextMoveAt;

        private GolemFleeState(IronGolem golem, LivingEntity target, Location origin) {
            this.golem = golem;
            this.target = target;
            this.origin = origin;
        }
    }

    private static final class CooldownWave {
        private final UUID worldId;
        private final double x;
        private final double y;
        private final double z;
        private final long expiry;

        private CooldownWave(UUID worldId, double x, double y, double z, long expiry) {
            this.worldId = worldId;
            this.x = x;
            this.y = y;
            this.z = z;
            this.expiry = expiry;
        }
    }
}
