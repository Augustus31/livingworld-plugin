package plugin;

import com.comphenix.protocol.PacketType;
import com.comphenix.protocol.ProtocolLibrary;
import com.comphenix.protocol.ProtocolManager;
import com.comphenix.protocol.events.ListenerPriority;
import com.comphenix.protocol.events.PacketAdapter;
import com.comphenix.protocol.events.PacketContainer;
import com.comphenix.protocol.events.PacketEvent;
import com.comphenix.protocol.utility.MinecraftReflection;
import com.comphenix.protocol.wrappers.WrappedLevelChunkData;
import com.comphenix.protocol.wrappers.nbt.NbtBase;
import com.comphenix.protocol.wrappers.nbt.NbtCompound;
import com.comphenix.protocol.wrappers.nbt.NbtList;
import com.comphenix.protocol.wrappers.nbt.io.NbtBinarySerializer;

import org.bukkit.Axis;
import org.bukkit.Bukkit;
import org.bukkit.Chunk;
import org.bukkit.ChunkSnapshot;
import org.bukkit.HeightMap;
import org.bukkit.Location;
import org.bukkit.Material;
import org.bukkit.NamespacedKey;
import org.bukkit.Tag;
import org.bukkit.World;
import org.bukkit.block.Biome;
import org.bukkit.block.Block;
import org.bukkit.block.data.Bisected;
import org.bukkit.block.data.BlockData;
import org.bukkit.block.data.Orientable;
import org.bukkit.block.data.type.Leaves;
import org.bukkit.block.data.type.Snow;
import org.bukkit.command.Command;
import org.bukkit.command.CommandExecutor;
import org.bukkit.command.CommandSender;
import org.bukkit.command.PluginCommand;
import org.bukkit.command.TabCompleter;
import org.bukkit.entity.Entity;
import org.bukkit.entity.Player;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.HandlerList;
import org.bukkit.event.Listener;
import org.bukkit.event.block.BlockBreakEvent;
import org.bukkit.event.block.BlockBurnEvent;
import org.bukkit.event.block.BlockExplodeEvent;
import org.bukkit.event.block.BlockFadeEvent;
import org.bukkit.event.block.BlockFertilizeEvent;
import org.bukkit.event.block.BlockFormEvent;
import org.bukkit.event.block.BlockPistonExtendEvent;
import org.bukkit.event.block.BlockPistonRetractEvent;
import org.bukkit.event.block.BlockPlaceEvent;
import org.bukkit.event.block.BlockSpreadEvent;
import org.bukkit.event.block.EntityBlockFormEvent;
import org.bukkit.event.block.LeavesDecayEvent;
import org.bukkit.event.entity.EntityChangeBlockEvent;
import org.bukkit.event.entity.EntityExplodeEvent;
import org.bukkit.event.player.PlayerQuitEvent;
import org.bukkit.event.world.ChunkLoadEvent;
import org.bukkit.event.world.ChunkUnloadEvent;
import org.bukkit.event.world.StructureGrowEvent;
import org.bukkit.persistence.PersistentDataType;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.scheduler.BukkitTask;
import org.bukkit.util.Vector;

import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Base64;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.SplittableRandom;
import java.util.TreeMap;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadLocalRandom;
import java.util.logging.Level;
import java.util.zip.CRC32;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import javax.imageio.ImageIO;

/** Seasonal foliage and ground effects for Paper 1.18.2, with per-chunk recovery records. */
public final class Seasons implements Listener, CommandExecutor, TabCompleter {
    private static final long SEASON_TICKS = 5000L;
    private static final int GRADIENT_TOP_Y = 130;
    private static final double GRASS_CHANCE_LOW = 0.20, GRASS_CHANCE_HIGH = 0.50;
    private static final double LEAF_SURVIVAL_LOW = 0.40, LEAF_SURVIVAL_HIGH = 0.16;
    private static final double TREE_CAP_SURVIVAL = 0.95;
    private static final int PRESERVATION_RULES = 3;
    private static final int SURVIVAL_CENSUS_MAGIC = 0x53504333;
    // Compatibility only: ownership metadata written by the removed decorative overlays.
    private static final int LEGACY_OVERLAY_MAGIC = 0x53464331, LEGACY_OVERLAY_FLAG = 128;
    private static final double FALL_FINISH_FRACTION = 0.75;
    private static final int SNAPSHOTS_PER_TICK = 3;
    private static final int MAX_CHANGES_PER_TICK = 128;
    private static final int MAX_CHECKS_PER_TICK = 2048;
    private static final long WORK_BUDGET_NANOS = 2_000_000L;
    private static final int MAGIC = 0x53454131;
    private static final int DISCARD_MAGIC = 0x53444431;
    private static final int DISCARD_PAGE_SIZE = 4;
    private static final int LEGACY_PRESERVATION_STATE_MAGIC = 0x53505331;
    private static final int ADJACENT_PRESERVATION_STATE_MAGIC = 0x53505332;
    private static final int PRESERVATION_STATE_MAGIC = 0x53505333;
    private static final int CANOPY_POLICY_MAGIC = 0x53504332;
    private static final int PRESERVATION_CANOPY_MAGIC = 0x53504331;
    private static final int INVALID = 1, REMOVED = 2, PRESERVED = 4, TREE_CAP = 64;
    private static final int LOG_FACE_SHIFT = 3, LOG_FACE_MASK = 7 << LOG_FACE_SHIFT;
    private static final int[][] DIRECTIONS = {
        {1, 0, 0}, {-1, 0, 0}, {0, 1, 0}, {0, -1, 0}, {0, 0, 1}, {0, 0, -1}
    };

    private final JavaPlugin plugin;
    private final GroundSeasons ground;
    private final SnowSeasons snow = new SnowSeasons();
    private static volatile Seasons activeSeasons;
    private final ChunkAdmissions admissions = new ChunkAdmissions();
    private final NamespacedKey leavesKey, legacyCleanupKey;
    private final Path stateFile;
    private final Set<Key> indexed = new LinkedHashSet<>();
    private final Map<Key, Canopy> cache = new HashMap<>();
    private final ArrayDeque<Key> work = new ArrayDeque<>();
    private final ArrayDeque<Key> scans = new ArrayDeque<>();
    private final Set<Key> queuedScans = new HashSet<>(), scannedLoaded = new HashSet<>();
    private final Map<Key, LeafNormalization> winterNormalizations = new LinkedHashMap<>();
    private final Map<Key, Long> winterNormalized = new HashMap<>();
    private final Set<Material> logs;
    private final Map<Key, Integer> eligibleCounts = new HashMap<>();
    private final Map<Key, Integer> preservationQuotas = new HashMap<>();
    private final Map<Key, Integer> adjacentCounts = new HashMap<>();
    private long preservationSeed = newPreservationSeed();
    private long knownEligible, knownAdjacent, allocatedPreserved;
    private boolean adjacencyCatalogUpgrade, buildingSurvival;
    private ExecutorService worker;
    private BukkitTask task;
    private Scan scan;
    private volatile boolean running;
    private volatile boolean enabled;
    private boolean restoringAll;
    private volatile long elapsed;
    private long ticks, generation;

    public Seasons(JavaPlugin plugin) {
        this.plugin = plugin;
        ground = new GroundSeasons();
        leavesKey = new NamespacedKey(plugin, "season_leaf_records_v1");
        legacyCleanupKey = new NamespacedKey(plugin, "season_old_overlays_removed_v1");
        stateFile = plugin.getDataFolder().toPath().resolve("seasons-state.bin");
        logs = EnumSet.copyOf(Tag.LOGS.getValues());
    }

    public void register() {
        if (running) throw new IllegalStateException("Seasons is already registered.");
        PluginCommand command = plugin.getCommand("season");
        if (command == null)
            throw new IllegalStateException("Add the season command to plugin.yml.");
        try {
            readState();
        } catch (IOException e) {
            throw new IllegalStateException(
                    "Cannot read seasons-state.bin; preserving saved leaf records.", e);
        }
        worker =
                Executors.newSingleThreadExecutor(
                        r -> {
                            Thread t = new Thread(r, plugin.getName() + "-seasons-storage");
                            t.setDaemon(true);
                            return t;
                        });
        // Persist the selection seed before any new per-chunk selection is saved.
        if (!adjacencyCatalogUpgrade) saveBlocking();
        snow.register();
        running = true;
        activeSeasons = this;
        command.setExecutor(this);
        command.setTabCompleter(this);
        Bukkit.getPluginManager().registerEvents(this, plugin);
        for (World world : Bukkit.getWorlds()) {
            for (Chunk chunk : world.getLoadedChunks()) {
                cleanupLegacyOnLoad(chunk);
                snow.noteLoaded(chunk);
                if (enabled && !admissions.ready(key(chunk))) continue;
                Canopy c = load(chunk);
                if (!enabled && c != null) restoreChunkFully(chunk, c, false);
                snow.discover(chunk);
                ground.load(chunk);
                if (!enabled) ground.restoreChunk(chunk);
            }
        }
        if (adjacencyCatalogUpgrade) {
            rerollPreservation();
            adjacencyCatalogUpgrade = false;
        }
        task = Bukkit.getScheduler().runTaskTimer(plugin, this::tick, 1L, 1L);
    }

    public void shutdown() {
        if (!running) return;
        if (enabled || !snow.ownedChunks.isEmpty()) {
            PluginCommand command = plugin.getCommand("season");
            if (command != null)
                onCommand(Bukkit.getConsoleSender(), command, "season", new String[] {"disable"});
        }
        running = false;
        generation++;
        if (task != null) task.cancel();
        HandlerList.unregisterAll(this);
        admissions.clear();
        snow.shutdown();
        if (activeSeasons == this) activeSeasons = null;
        for (Map.Entry<Key, Canopy> e : cache.entrySet()) {
            World world = Bukkit.getWorld(e.getKey().world);
            if (world != null && world.isChunkLoaded(e.getKey().x, e.getKey().z))
                flush(world.getChunkAt(e.getKey().x, e.getKey().z), e.getValue());
        }
        ground.shutdown();
        saveBlocking();
        worker.shutdown();
        cache.clear();
        work.clear();
        scans.clear();
    }

    @Override
    public boolean onCommand(CommandSender sender, Command command, String label, String[] args) {
        if (!command.getName().equalsIgnoreCase("season")) return false;
        if (!sender.hasPermission("firstplugin.season")) {
            sender.sendMessage("§cYou do not have permission to manage seasons.");
            return true;
        }
        if (args.length == 0 || (args.length == 1 && args[0].equalsIgnoreCase("status"))) {
            showStatus(sender);
            return true;
        }
        if (args.length >= 1 && args[0].equalsIgnoreCase("discards")) {
            if (args.length > 2) {
                sender.sendMessage("§eUsage: /season discards [page]");
                return true;
            }
            int page = 1;
            if (args.length == 2) {
                try {
                    page = Integer.parseInt(args[1]);
                } catch (NumberFormatException e) {
                    page = 0;
                }
            }
            if (page < 1) sender.sendMessage("§cPage must be a positive whole number.");
            else showDiscards(sender, page);
            return true;
        }
        if (args.length == 1) {
            Season target = null;
            try {
                target = Season.valueOf(args[0].toUpperCase(java.util.Locale.ROOT));
            } catch (IllegalArgumentException ignored) {
            }
            if (target != null) {
                moveToSeason(sender, target);
                return true;
            }
        }
        if (args.length != 1
                || (!args[0].equalsIgnoreCase("enable") && !args[0].equalsIgnoreCase("disable"))) {
            sender.sendMessage(
                    "§eUsage: /season <summer|fall|winter|spring|enable|disable|status|discards"
                            + " [page]>");
            return true;
        }
        // Invalidate background scans before restoring anything or restarting the calendar.
        admissions.clear();
        snow.resetAdmissions();
        ground.resetScans();
        generation++;
        scan = null;
        scans.clear();
        queuedScans.clear();
        scannedLoaded.clear();
        enabled = false;
        snow.calendarChanged();
        saveBlocking();
        sender.sendMessage(
                "§eRestoring seasonal leaves and grass and removing seasonal flowers, including"
                        + " unloaded chunks...");
        int[] removedSnow = snow.cleanupOwned();
        int[] result = restoreAll();
        ground.restoreAll();
        sender.sendMessage("§aRemoved " + removedSnow[0] + " tracked snow layers.");
        if (removedSnow[1] != 0 || removedSnow[2] != 0)
            sender.sendMessage(
                    "§eSnow cleanup retained records for "
                            + removedSnow[1]
                            + " unavailable chunks and "
                            + removedSnow[2]
                            + " protected layers.");
        if (args[0].equalsIgnoreCase("enable")) {
            elapsed = 0;
            enabled = true;
            ground.seed = newPreservationSeed();
            snow.prepareLoaded(false);
            sender.sendMessage(
                    "§aSeasons enabled at the beginning of summer. Each season lasts "
                            + SEASON_TICKS
                            + " ticks.");
        } else sender.sendMessage("§aSeasons disabled. Restored " + result[0] + " leaf blocks.");
        sender.sendMessage(
                "§aRestored "
                        + ground.lastRestoredGrass
                        + " grass blocks; removed "
                        + ground.lastRemovedFlowers
                        + " seasonal flowers.");
        if (ground.lastUnavailable != 0)
            sender.sendMessage(
                    "§eGround records in "
                            + ground.lastUnavailable
                            + " chunk(s) belong to unavailable worlds and were retained.");
        if (result[1] != 0)
            sender.sendMessage(
                    "§e"
                            + result[2]
                            + " leaves in "
                            + result[1]
                            + " loaded chunk(s) still lack an unobstructed leaf path to a log."
                            + " Their records are retained; this is not an unloaded-chunk"
                            + " failure.");
        if (result[3] != 0)
            sender.sendMessage(
                    "§e"
                            + result[3]
                            + " saved chunk(s) belong to unavailable worlds; records are"
                            + " retained.");
        snow.calendarChanged();
        saveBlocking();
        return true;
    }

    @Override
    public List<String> onTabComplete(
            CommandSender sender, Command command, String alias, String[] args) {
        if (!sender.hasPermission("firstplugin.season")) return List.of();
        if (args.length == 2 && args[0].equalsIgnoreCase("discards")) {
            String prefix = args[1];
            return List.of("1", "2", "3").stream().filter(v -> v.startsWith(prefix)).toList();
        }
        if (args.length != 1) return List.of();
        return List.of(
                        "summer",
                        "fall",
                        "winter",
                        "spring",
                        "enable",
                        "disable",
                        "status",
                        "discards")
                .stream()
                .filter(v -> v.startsWith(args[0].toLowerCase(java.util.Locale.ROOT)))
                .toList();
    }

    private void moveToSeason(CommandSender sender, Season target) {
        Season before = season();
        boolean wasEnabled = enabled;
        long year = elapsed / (4 * SEASON_TICKS);
        if (wasEnabled && target.ordinal() <= before.ordinal()) year++;
        elapsed = year * 4 * SEASON_TICKS + (long) target.ordinal() * SEASON_TICKS;
        enabled = true;
        generation++;
        scan = null;
        scans.clear();
        queuedScans.clear();
        ground.resetScans();
        if (!wasEnabled) {
            admissions.clear();
            ground.seed = newPreservationSeed();
        }
        saveBlocking();
        if (target == Season.SUMMER) restoreAll();
        if ((target == Season.FALL || target == Season.WINTER)
                && (!wasEnabled || before == Season.SUMMER || target.ordinal() <= before.ordinal()))
            rerollPreservation();
        if (target == Season.WINTER) finishWinter();
        snow.prepareLoaded(target == Season.WINTER);
        snow.calendarChanged();
        discover();
        saveBlocking();
        sender.sendMessage(
                "§aMoved to the beginning of "
                        + target.name().toLowerCase(java.util.Locale.ROOT)
                        + ". Seasons are enabled; this season has "
                        + SEASON_TICKS
                        + " ticks remaining.");
    }

    private void showDiscards(CommandSender sender, int page) {
        List<DiscardEntry> entries = new ArrayList<>();
        int chunks = 0;
        for (Map.Entry<Key, Canopy> entry : cache.entrySet()) {
            Key key = entry.getKey();
            World world = Bukkit.getWorld(key.world);
            if (world == null || !world.isChunkLoaded(key.x, key.z)) continue;
            chunks++;
            Canopy c = entry.getValue();
            for (int i = 0; i < c.size(); i++)
                if ((c.flags[i] & INVALID) != 0) entries.add(new DiscardEntry(key, c, i));
        }
        entries.sort(
                Comparator.comparing((DiscardEntry e) -> e.key.world.toString())
                        .thenComparingInt(DiscardEntry::x)
                        .thenComparingInt(DiscardEntry::y)
                        .thenComparingInt(DiscardEntry::z));
        if (entries.isEmpty()) {
            sender.sendMessage(
                    "§7No discarded leaf records in " + chunks + " cached, loaded chunks.");
            sender.sendMessage("§7Unloaded or uncached chunks were not inspected.");
            return;
        }
        int pages = (entries.size() + DISCARD_PAGE_SIZE - 1) / DISCARD_PAGE_SIZE;
        if (page > pages) {
            sender.sendMessage("§cPage out of range. Use /season discards <1-" + pages + ">.");
            return;
        }
        sender.sendMessage(
                "§6Discarded leaf records: " + entries.size() + " | page " + page + "/" + pages);
        sender.sendMessage(
                "§7Cached, loaded chunks only; this command does not load other chunks.");
        int start = (page - 1) * DISCARD_PAGE_SIZE;
        for (int n = start; n < Math.min(entries.size(), start + DISCARD_PAGE_SIZE); n++) {
            DiscardEntry entry = entries.get(n);
            Key key = entry.key;
            Canopy c = entry.canopy;
            int i = entry.index;
            World world = Bukkit.getWorld(key.world);
            Block leaf = world.getBlockAt(entry.x(), entry.y(), entry.z());
            Block log = anchor(leaf, c.offsets[i], false);
            DiscardInfo info = c.discards.get(c.positions[i]);
            String reason =
                    info == null ? "reason not recorded (no saved discard details)" : info.reason;
            int offset = c.offsets[i];
            int logX = entry.x() + ((offset & 15) - 6);
            int logY = entry.y() + (((offset >>> 4) & 15) - 6);
            int logZ = entry.z() + (((offset >>> 8) & 15) - 6);
            sender.sendMessage(
                    "§e#"
                            + (n + 1)
                            + " "
                            + world.getName()
                            + " "
                            + entry.x()
                            + " "
                            + entry.y()
                            + " "
                            + entry.z()
                            + "§7: §f"
                            + reason);
            sender.sendMessage(
                    "§7Saved: "
                            + c.states[c.stateIds[i] & 0xffff]
                            + "; log "
                            + c.logTypes[c.logIds[i] & 0xffff]
                            + " at "
                            + logX
                            + " "
                            + logY
                            + " "
                            + logZ
                            + ".");
            if (info != null)
                sender.sendMessage(
                        "§7At discard ("
                                + java.time.Instant.ofEpochMilli(info.timeMillis)
                                + "): leaf="
                                + info.leaf
                                + "; log="
                                + info.log
                                + ".");
            sender.sendMessage(
                    "§7Now: leaf="
                            + leaf.getBlockData().getAsString()
                            + "; log="
                            + (log == null ? "unloaded" : log.getType().name())
                            + ".");
        }
        if (page < pages) sender.sendMessage("§eNext page: /season discards " + (page + 1));
    }

    private void showStatus(CommandSender sender) {
        Season current = season();
        long spent = elapsed % SEASON_TICKS;
        long left = SEASON_TICKS - spent;
        long present = 0, removed = 0, discarded = 0, removalDue = 0, restorationDue = 0;
        int cachedChunks = 0;
        long eligibleHere = 0, preservedHere = 0;
        for (Map.Entry<Key, Canopy> entry : cache.entrySet()) {
            Key key = entry.getKey();
            World world = Bukkit.getWorld(key.world);
            if (world == null || !world.isChunkLoaded(key.x, key.z)) continue;
            cachedChunks++;
            Canopy c = entry.getValue();
            for (int i = 0; i < c.size(); i++) {
                if ((c.flags[i] & INVALID) != 0) {
                    discarded++;
                    continue;
                }
                if (c.canShed(i)) {
                    eligibleHere++;
                    if ((c.flags[i] & PRESERVED) != 0) preservedHere++;
                }
                boolean absent = (c.flags[i] & REMOVED) != 0;
                if (absent) removed++;
                else present++;
                int position = c.positions[i];
                long absolute =
                        pack(
                                (key.x << 4) + (position & 15),
                                c.minY + (position >>> 8),
                                (key.z << 4) + ((position >>> 4) & 15));
                boolean wantedAbsent = enabled && shouldBeAbsent(c, i, key.world, absolute);
                if (absent && !wantedAbsent) restorationDue++;
                else if (!absent && wantedAbsent) removalDue++;
            }
        }
        String target =
                !enabled
                        ? "full foliage (seasonal effects off)"
                        : switch (current) {
                            case SUMMER -> "full foliage";
                            case FALL -> "gradually shedding leaves";
                            case WINTER ->
                                    "oak/birch foliage shed except the year-round preserved set";
                            case SPRING -> "gradually regrowing leaves";
                        };
        sender.sendMessage(
                "§6Seasons status: " + (enabled ? "§aenabled" : "§7disabled (clock paused)"));
        sender.sendMessage(
                "§eCurrent season: §f"
                        + current.name().toLowerCase(java.util.Locale.ROOT)
                        + "§e; next: §f"
                        + Season.values()[(current.ordinal() + 1) % 4]
                                .name()
                                .toLowerCase(java.util.Locale.ROOT));
        sender.sendMessage(
                "§eTicks left: §f"
                        + left
                        + "§e / "
                        + SEASON_TICKS
                        + " ("
                        + spent
                        + " elapsed"
                        + (enabled ? ")." : "; paused)."));
        sender.sendMessage("§eLeaf target: §f" + target + ".");
        sender.sendMessage(
                "§eKnown eligible oak/birch leaves: §f"
                        + knownEligible
                        + "§e; current-year selections catalogued: §f"
                        + allocatedPreserved
                        + "§e.");
        sender.sendMessage(
                "§eYear-round preserved (cached): §f"
                        + preservedHere
                        + "§e / §f"
                        + eligibleHere
                        + "§e eligible leaves.");
        sender.sendMessage(
                "§7Full-canopy survival budget: "
                        + Math.round(LEAF_SURVIVAL_LOW * 100)
                        + "% at/below sea level, declining to "
                        + Math.round(LEAF_SURVIVAL_HIGH * 100)
                        + "% at Y 130+. Innermost leaves survive first. Tree caps: 95%.");
        sender.sendMessage(
                "§7Outer layers shed first; cutoff-layer choices redraw at summer's end."
                        + " Unloaded chunks adopt the current draw when loaded.");

        sender.sendMessage(
                "§7Only nonpersistent oak and birch leaves shed; other leaves are protected.");
        sender.sendMessage(
                "§7Fall shedding finishes by tick "
                        + (long) (SEASON_TICKS * FALL_FINISH_FRACTION)
                        + "; a final nearby completion pass runs when winter begins.");
        sender.sendMessage("§eLeaf records in " + cachedChunks + " cached, loaded chunks:");
        sender.sendMessage(
                "§f"
                        + present
                        + "§7 in place, §f"
                        + removed
                        + "§7 seasonally removed, §f"
                        + discarded
                        + "§7 discarded.");
        sender.sendMessage(
                "§eDue by the current schedule: §f"
                        + removalDue
                        + "§7 removals, §f"
                        + restorationDue
                        + "§7 restorations.");
        sender.sendMessage("§7Counts use saved records; persistent leaves are excluded.");
        sender.sendMessage(
                "§eSaved chunk index: §f"
                        + indexed.size()
                        + "§e; other saved chunks not inspected: §f"
                        + Math.max(0, indexed.size() - cachedChunks)
                        + "§e.");
        String progress = "idle";
        if (scan != null) {
            World world = Bukkit.getWorld(scan.key.world);
            progress =
                    (scan.submitted
                                    ? "analyzing/saving"
                                    : "capturing " + scan.captured + "/9 snapshots")
                            + " at "
                            + (world == null ? scan.key.world.toString() : world.getName())
                            + " "
                            + scan.key.x
                            + ", "
                            + scan.key.z;
        }
        sender.sendMessage(
                "§eScan: §f" + progress + "§e; queued requests: §f" + scans.size() + "§e.");
        ground.status(sender);
        snow.status(sender);
        admissions.status(sender);
    }

    private void resumeSeasonalChunk(Key key) {
        World world = Bukkit.getWorld(key.world);
        if (!enabled || world == null || !world.isChunkLoaded(key.x, key.z) || !nearPlayer(key))
            return;
        Chunk chunk = world.getChunkAt(key.x, key.z);
        load(chunk);
        snow.discover(chunk);
        ground.discover(chunk);
        queueScan(key);
    }

    private final class ChunkAdmissions {
        private static final double FAST_SPEED_SQUARED = (25.0 / 20.0) * (25.0 / 20.0);
        private static final long CHECK_NANOS = 5_000_000_000L;
        private final Set<Key> admitted = new HashSet<>();
        private final Map<Key, ChunkDelay> deferred = new HashMap<>();
        private final PriorityQueue<ChunkDelay> deadlines =
                new PriorityQueue<>(Comparator.comparingLong(d -> d.nextCheck));

        private boolean fast(Player player) {
            // Bukkit velocities are blocks per tick; only X and Z contribute.
            Entity moving = player;
            while (moving.getVehicle() != null) moving = moving.getVehicle();
            Vector velocity = moving.getVelocity();
            return velocity.getX() * velocity.getX() + velocity.getZ() * velocity.getZ()
                    > FAST_SPEED_SQUARED;
        }

        private boolean inChunk(Player player, Key key) {
            if (player == null
                    || !player.isOnline()
                    || !player.getWorld().getUID().equals(key.world)) return false;
            Location location = player.getLocation();
            return (location.getBlockX() >> 4) == key.x && (location.getBlockZ() >> 4) == key.z;
        }

        private Player interestedPlayer(Key key) {
            World world = Bukkit.getWorld(key.world);
            if (world == null || world.getEnvironment() != World.Environment.NORMAL) return null;
            int radius = Math.max(1, Math.min(12, Bukkit.getViewDistance()));
            Player nearest = null;
            double best = Double.POSITIVE_INFINITY;
            for (Player player : world.getPlayers()) {
                Location position = player.getLocation();
                if (Math.abs((position.getBlockX() >> 4) - key.x) > radius
                        || Math.abs((position.getBlockZ() >> 4) - key.z) > radius) continue;
                // A slow viewer already needs this chunk, even if another player flies past it.
                if (!fast(player)) return player;
                double dx = position.getX() - ((key.x << 4) + 8),
                        dz = position.getZ() - ((key.z << 4) + 8);
                double distance = dx * dx + dz * dz;
                if (distance < best) {
                    best = distance;
                    nearest = player;
                }
            }
            return nearest;
        }

        private boolean ready(Key key) {
            if (!enabled || restoringAll) return true;
            if (admitted.contains(key)) return true;
            ChunkDelay previous = deferred.get(key);
            if (previous != null && !previous.abandoned) return false;
            Player player = interestedPlayer(key);
            if (player == null) return false;
            if (!fast(player)) {
                admit(key);
                return true;
            }
            // A cancelled fly-by is reconsidered on an actual revisit or new player interest.
            if (previous != null
                    && previous.owner.equals(player.getUniqueId())
                    && !inChunk(player, key)) return false;
            long now = System.nanoTime();
            ChunkDelay delay = new ChunkDelay(key, player.getUniqueId(), now, now + CHECK_NANOS);
            deferred.put(key, delay);
            deadlines.add(delay);
            return false;
        }

        private void admit(Key key) {
            deferred.remove(key);
            admitted.add(key);
        }

        private void check(long now) {
            if (deadlines.isEmpty() || deadlines.peek().nextCheck > now) return;
            List<Key> released = new ArrayList<>();
            while (!deadlines.isEmpty() && deadlines.peek().nextCheck <= now) {
                ChunkDelay delay = deadlines.poll();
                if (deferred.get(delay.key) != delay || delay.abandoned) continue;
                World world = Bukkit.getWorld(delay.key.world);
                if (world == null || !world.isChunkLoaded(delay.key.x, delay.key.z)) {
                    forget(delay.key);
                    continue;
                }
                Player player = Bukkit.getPlayer(delay.owner);
                if (!inChunk(player, delay.key)) {
                    delay.abandoned = true;
                    continue;
                }
                delay.checks++;
                if (now - delay.started >= 3 * CHECK_NANOS || !fast(player)) {
                    admit(delay.key);
                    released.add(delay.key);
                } else {
                    delay.nextCheck = delay.started + (delay.checks + 1) * CHECK_NANOS;
                    deadlines.add(delay);
                }
            }
            for (Key key : released) resumeSeasonalChunk(key);
        }

        private void forget(Key key) {
            admitted.remove(key);
            deferred.remove(key);
        }

        private void clear() {
            admitted.clear();
            deferred.clear();
            deadlines.clear();
        }

        private void status(CommandSender sender) {
            long waiting = deferred.values().stream().filter(d -> !d.abandoned).count();
            sender.sendMessage(
                    "§eFast-travel chunk delay: §f"
                            + waiting
                            + "§7 waiting; checks at 5/10/15 seconds, forced start at 15 seconds if"
                            + " still in the chunk.");
        }
    }

    private static final class ChunkDelay {
        final Key key;
        final UUID owner;
        final long started;
        long nextCheck;
        int checks;
        boolean abandoned;

        ChunkDelay(Key key, UUID owner, long started, long nextCheck) {
            this.key = key;
            this.owner = owner;
            this.started = started;
            this.nextCheck = nextCheck;
        }
    }

    private Season season() {
        return Season.values()[(int) ((elapsed / SEASON_TICKS) % 4)];
    }

    private void tick() {
        if (enabled) {
            Season before = season();
            elapsed++;
            if (before != season()) {
                ground.resetScans();
                for (World world : Bukkit.getWorlds())
                    if (world.getEnvironment() == World.Environment.NORMAL)
                        for (Chunk chunk : world.getLoadedChunks())
                            if (nearPlayer(key(chunk))) ground.discover(chunk);
            }
            if (before == Season.SUMMER && season() == Season.FALL) rerollPreservation();
            if (before != Season.WINTER && season() == Season.WINTER) finishWinter();
        }
        ticks++;
        if (enabled) admissions.check(System.nanoTime());
        if (ticks % 200 == 1) discover();
        if (ticks % 600 == 0) saveAsync(null);
        if (enabled) advanceScan();
        ground.tick();
        snow.tick();
        long until = System.nanoTime() + WORK_BUDGET_NANOS;
        int[] normalized = advanceWinterNormalizations(until);
        int checks = normalized[0], changes = normalized[1], rounds = work.size();
        while (rounds-- > 0
                && !work.isEmpty()
                && checks < MAX_CHECKS_PER_TICK
                && changes < MAX_CHANGES_PER_TICK
                && System.nanoTime() < until) {
            Key key = work.removeFirst();
            Canopy c = cache.get(key);
            World world = Bukkit.getWorld(key.world);
            if (c == null || world == null || !world.isChunkLoaded(key.x, key.z)) {
                cache.remove(key);
                continue;
            }
            if (!nearPlayer(key)) {
                evictCanopy(key);
                continue;
            }
            if (enabled && !admissions.ready(key)) {
                work.addLast(key);
                continue;
            }
            if (winterNormalizations.containsKey(key)) {
                work.addLast(key);
                continue;
            }
            int n = Math.min(c.size(), Math.min(256, MAX_CHECKS_PER_TICK - checks));
            Chunk chunk = world.getChunkAt(key.x, key.z);
            try {
                for (int j = 0;
                        j < n && changes < MAX_CHANGES_PER_TICK && System.nanoTime() < until;
                        j++) {
                    int i = c.cursor;
                    c.cursor = (c.cursor + 1) % c.size();
                    checks++;
                    if (updateLeaf(chunk, c, i, false, false)) changes++;
                }
            } finally {
                if (c.dirty) flush(chunk, c);
            }
            work.addLast(key);
        }
    }

    private void discover() {
        for (Map.Entry<Key, Canopy> e : new ArrayList<>(cache.entrySet())) {
            if (!nearPlayer(e.getKey())) evictCanopy(e.getKey());
        }
        for (Player player : Bukkit.getOnlinePlayers()) {
            World world = player.getWorld();
            if (world.getEnvironment() != World.Environment.NORMAL) continue;
            int radius = Math.max(1, Math.min(12, Bukkit.getViewDistance()));
            int cx = player.getLocation().getBlockX() >> 4,
                    cz = player.getLocation().getBlockZ() >> 4;
            for (int ring = 0; ring <= radius; ring++) {
                for (int dx = -ring; dx <= ring; dx++)
                    for (int dz = -ring; dz <= ring; dz++) {
                        if (Math.max(Math.abs(dx), Math.abs(dz)) != ring
                                || !world.isChunkLoaded(cx + dx, cz + dz)) continue;
                        Key key = new Key(world.getUID(), cx + dx, cz + dz);
                        if (enabled && !admissions.ready(key)) continue;
                        load(world.getChunkAt(key.x, key.z));
                        snow.discover(world.getChunkAt(key.x, key.z));
                        ground.discover(world.getChunkAt(key.x, key.z));
                        if (enabled) queueScan(key);
                    }
            }
        }
    }

    private boolean nearPlayer(Key key) {
        World world = Bukkit.getWorld(key.world);
        if (world == null) return false;
        int radius = Math.max(1, Math.min(12, Bukkit.getViewDistance()));
        for (Player p : world.getPlayers()) {
            Location l = p.getLocation();
            if (Math.abs((l.getBlockX() >> 4) - key.x) <= radius
                    && Math.abs((l.getBlockZ() >> 4) - key.z) <= radius) return true;
        }
        return false;
    }

    private void queueScan(Key key) {
        if ((!enabled || admissions.ready(key))
                && !scannedLoaded.contains(key)
                && queuedScans.add(key)) scans.addLast(key);
    }

    private void advanceScan() {
        if (scan == null) {
            int attempts = 32;
            while (!scans.isEmpty() && attempts-- > 0) {
                Key key = scans.removeFirst();
                queuedScans.remove(key);
                World w = Bukkit.getWorld(key.world);
                if (w == null || !nearPlayer(key) || !admissions.ready(key) || !haloLoaded(w, key))
                    continue;
                scan = new Scan(key, w.getMinHeight(), w.getMaxHeight(), generation);
                break;
            }
        }
        if (scan != null && !admissions.ready(scan.key)) {
            scan = null;
            return;
        }
        if (scan == null || scan.submitted) return;
        Scan s = scan;
        World world = Bukkit.getWorld(s.key.world);
        if (world == null || !haloLoaded(world, s.key) || !nearPlayer(s.key)) {
            scan = null;
            return;
        }
        // Capture a few snapshots per tick; examine their block contents off-thread.
        for (int snapshots = 0; snapshots < SNAPSHOTS_PER_TICK && s.captured < 9; snapshots++) {
            int i = s.captured++;
            s.snapshots[i] =
                    world.getChunkAt(s.key.x + i % 3 - 1, s.key.z + i / 3 - 1)
                            .getChunkSnapshot(false, false, false);
        }
        if (s.captured != 9) return;
        s.submitted = true;
        worker.execute(
                () -> {
                    try {
                        Map<Key, Canopy> built = scanCanopies(s, logs);
                        onMain(
                                () -> {
                                    if (generation != s.generation || !enabled || scan != s) return;
                                    Set<Key> added = new HashSet<>();
                                    for (Key key : built.keySet())
                                        if (indexed.add(key)) added.add(key);
                                    Runnable install =
                                            () -> {
                                                if (generation != s.generation
                                                        || !enabled
                                                        || scan != s) return;
                                                installCanopies(s.key, built);
                                                scan = null;
                                            };
                                    if (!added.isEmpty())
                                        saveAsync(
                                                install,
                                                () -> {
                                                    indexed.removeAll(added);
                                                    if (scan == s) scan = null;
                                                });
                                    else install.run();
                                });
                    } catch (Exception e) {
                        plugin.getLogger().log(Level.SEVERE, "Could not scan seasonal leaves", e);
                        onMain(
                                () -> {
                                    if (scan == s) scan = null;
                                });
                    }
                });
    }

    private void installCanopies(Key central, Map<Key, Canopy> built) {
        World world = Bukkit.getWorld(central.world);
        if (world == null || !haloLoaded(world, central) || (enabled && !admissions.ready(central)))
            return;
        // Install every original record before computing a census across chunk boundaries.
        boolean previousGuard = buildingSurvival;
        buildingSurvival = true;
        try {
            for (Map.Entry<Key, Canopy> entry : built.entrySet()) {
                Key key = entry.getKey();
                Chunk chunk = world.getChunkAt(key.x, key.z);
                Canopy previous = load(chunk);
                Canopy merged = merge(previous, entry.getValue());
                if (merged != previous) put(key, merged);
                if (merged != previous || merged.dirty) flush(chunk, merged);
            }
        } finally {
            buildingSurvival = previousGuard;
        }
        Canopy center = cache.get(central);
        if (center != null) {
            applyPreservation(central, center, true);
            if (center.dirty) flush(world.getChunkAt(central.x, central.z), center);
        }
        scannedLoaded.add(central);
        if (enabled && season() == Season.WINTER) stripWinterChunk(central);
    }

    private void stripWinterChunk(Key key) {
        if (!enabled || season() != Season.WINTER || !scannedLoaded.contains(key)) return;
        World world = Bukkit.getWorld(key.world);
        if (world == null || !world.isChunkLoaded(key.x, key.z) || !admissions.ready(key)) return;
        long winter = snow.winterId();
        if (winterNormalized.getOrDefault(key, Long.MIN_VALUE) == winter) return;
        Canopy c = load(world.getChunkAt(key.x, key.z));
        if (c == null || c.size() == 0) {
            winterNormalized.put(key, winter);
            return;
        }
        LeafNormalization existing = winterNormalizations.get(key);
        if (existing != null && existing.canopy == c && existing.winter == winter) return;
        applyPreservation(key, c);
        winterNormalizations.put(key, new LeafNormalization(c, winter));
    }

    private boolean leavesReadyForSnow(Key key) {
        if (!scannedLoaded.contains(key)) {
            if (nearPlayer(key)) queueScan(key);
            return false;
        }
        stripWinterChunk(key);
        return winterNormalized.getOrDefault(key, Long.MIN_VALUE) == snow.winterId();
    }

    private int[] advanceWinterNormalizations(long until) {
        int checks = 0, changes = 0;
        if (!enabled || season() != Season.WINTER) {
            winterNormalizations.clear();
            winterNormalized.clear();
            return new int[] {0, 0};
        }
        for (Map.Entry<Key, LeafNormalization> entry :
                new ArrayList<>(winterNormalizations.entrySet())) {
            if (checks >= MAX_CHECKS_PER_TICK
                    || changes >= MAX_CHANGES_PER_TICK
                    || System.nanoTime() >= until) break;
            Key key = entry.getKey();
            LeafNormalization normalization = entry.getValue();
            World world = Bukkit.getWorld(key.world);
            if (world == null
                    || !world.isChunkLoaded(key.x, key.z)
                    || normalization.winter != snow.winterId()
                    || cache.get(key) != normalization.canopy) {
                winterNormalizations.remove(key);
                continue;
            }
            if (!nearPlayer(key) || !admissions.ready(key)) continue;
            Canopy c = normalization.canopy;
            Chunk chunk = world.getChunkAt(key.x, key.z);
            try {
                while (checks < MAX_CHECKS_PER_TICK
                        && changes < MAX_CHANGES_PER_TICK
                        && System.nanoTime() < until
                        && normalization.phase < 3) {
                    if (normalization.cursor == c.size()) {
                        normalization.cursor = 0;
                        normalization.phase++;
                        if (normalization.phase == 3) {
                            if (normalization.pending) {
                                normalization.phase = 0;
                                normalization.pending = false;
                            } else {
                                winterNormalized.put(key, normalization.winter);
                                winterNormalizations.remove(key);
                            }
                        }
                        continue;
                    }
                    int offset = normalization.cursor++;
                    int i =
                            normalization
                                    .order[
                                    normalization.phase == 0 ? c.size() - 1 - offset : offset];
                    checks++;
                    if ((c.flags[i] & INVALID) != 0 || !c.canShed(i)) continue;
                    Block block = block(chunk, c, i);
                    boolean absent = shouldBeAbsent(c, i, block);
                    if (normalization.phase < 2) {
                        if (absent == (normalization.phase == 0)
                                && updateLeaf(chunk, c, i, false, false)) changes++;
                    } else if (absent) {
                        if (block.getBlockData() instanceof Leaves leaf && !leaf.isPersistent())
                            normalization.pending = true;
                    } else if ((c.flags[i] & REMOVED) != 0) normalization.pending = true;
                }
            } finally {
                if (c.dirty) flush(chunk, c);
            }
        }
        return new int[] {checks, changes};
    }

    private void finishWinter() {
        winterNormalized.clear();
        winterNormalizations.clear();
        // New/returning chunks use the same bounded scan and leaf-work budgets as other ticks.
        // Never force-load a halo or drain an entire forest synchronously to prepare snow.
        for (World world : Bukkit.getWorlds()) {
            if (world.getEnvironment() != World.Environment.NORMAL) continue;
            for (Chunk chunk : world.getLoadedChunks()) {
                Key key = key(chunk);
                if (!nearPlayer(key) || !admissions.ready(key)) continue;
                if (scannedLoaded.contains(key)) stripWinterChunk(key);
                else queueScan(key);
            }
        }
    }

    private static final class LeafNormalization {
        final Canopy canopy;
        final long winter;
        final int[] order;
        int cursor, phase;
        boolean pending;

        LeafNormalization(Canopy canopy, long winter) {
            this.canopy = canopy;
            this.winter = winter;
            order = new int[canopy.size()];
            int[] offsets = new int[8];
            for (byte distance : canopy.distances) offsets[Math.min(7, distance)]++;
            int total = 0;
            for (int i = 0; i < offsets.length; i++) {
                int count = offsets[i];
                offsets[i] = total;
                total += count;
            }
            for (int i = 0; i < canopy.size(); i++)
                order[offsets[Math.min(7, canopy.distances[i])]++] = i;
        }
    }

    private static boolean haloLoaded(World w, Key key) {
        for (int dx = -1; dx <= 1; dx++)
            for (int dz = -1; dz <= 1; dz++)
                if (!w.isChunkLoaded(key.x + dx, key.z + dz)) return false;
        return true;
    }

    private static Map<Key, Canopy> scanCanopies(Scan s, Set<Material> logs) {
        Map<Long, Node> nodes = new HashMap<>();
        ArrayDeque<Node> bfs = new ArrayDeque<>();
        for (ChunkSnapshot snap : s.snapshots) {
            for (int y = s.minY; y < s.maxY; y++)
                for (int x = 0; x < 16; x++)
                    for (int z = 0; z < 16; z++) {
                        Material type = snap.getBlockType(x, y, z);
                        boolean log = logs.contains(type);
                        if (!log && !TagName.isLeaves(type)) continue;
                        int wx = (snap.getX() << 4) + x, wz = (snap.getZ() << 4) + z;
                        BlockData data = log ? null : snap.getBlockData(x, y, z);
                        if (!log && !(data instanceof Leaves)) continue;
                        Node n = new Node(pack(wx, y, wz), type, log ? null : (Leaves) data, log);
                        nodes.put(n.position, n);
                        if (log) bfs.add(n);
                    }
        }
        while (!bfs.isEmpty()) {
            Node n = bfs.removeFirst();
            if (n.distance >= 6) continue;
            for (int[] d : DIRECTIONS) {
                Node other =
                        nodes.get(
                                pack(
                                        x(n.position) + d[0],
                                        y(n.position) + d[1],
                                        z(n.position) + d[2]));
                if (other != null && other.leaf != null && other.distance > n.distance + 1) {
                    other.distance = n.distance + 1;
                    other.anchor = n.anchor;
                    other.anchorType = n.anchorType;
                    bfs.addLast(other);
                }
            }
        }
        Map<Key, List<Row>> rows = new HashMap<>();
        for (Node n : nodes.values()) {
            if (n.leaf == null || n.leaf.isPersistent() || n.distance > 6) continue;
            int local =
                    ((y(n.position) - s.minY) << 8)
                            | ((z(n.position) & 15) << 4)
                            | (x(n.position) & 15);
            short offset =
                    (short)
                            ((x(n.anchor) - x(n.position) + 6)
                                    | ((y(n.anchor) - y(n.position) + 6) << 4)
                                    | ((z(n.anchor) - z(n.position) + 6) << 8));
            Key key = new Key(s.key.world, x(n.position) >> 4, z(n.position) >> 4);
            rows.computeIfAbsent(key, k -> new ArrayList<>())
                    .add(
                            new Row(
                                    local,
                                    offset,
                                    n.leaf.getAsString(),
                                    n.anchorType.name(),
                                    (byte) n.distance,
                                    (byte) 0));
        }
        Map<Key, Canopy> result = new HashMap<>();
        rows.forEach((key, values) -> result.put(key, Canopy.fromRows(s.minY, values)));
        return result;
    }

    private static Canopy merge(Canopy old, Canopy fresh) {
        if (old == null) return fresh;
        boolean changed = false;
        for (int position : fresh.positions) {
            int i = Arrays.binarySearch(old.positions, position);
            if (i < 0 || (old.flags[i] & INVALID) != 0) {
                changed = true;
                break;
            }
        }
        if (!changed) return old;
        TreeMap<Integer, Row> rows = new TreeMap<>();
        for (int i = 0; i < fresh.size(); i++) rows.put(fresh.positions[i], fresh.row(i));
        for (int i = 0; i < old.size(); i++)
            if ((old.flags[i] & INVALID) == 0) rows.put(old.positions[i], old.row(i));
        Canopy merged = Canopy.fromRows(fresh.minY, new ArrayList<>(rows.values()));
        merged.preservationSeed = old.preservationSeed;
        old.legacyOverlays.forEach(
                (position, material) -> {
                    int i = Arrays.binarySearch(merged.positions, position);
                    if (i >= 0
                            && (merged.flags[i] & (LEGACY_OVERLAY_FLAG | INVALID))
                                    == LEGACY_OVERLAY_FLAG)
                        merged.legacyOverlays.put(position, material);
                });
        for (Map.Entry<Integer, DiscardInfo> entry : old.discards.entrySet()) {
            int i = Arrays.binarySearch(merged.positions, entry.getKey());
            if (i >= 0 && (merged.flags[i] & INVALID) != 0)
                merged.discards.put(entry.getKey(), entry.getValue());
        }
        return merged;
    }

    private Canopy load(Chunk chunk) {
        Key key = key(chunk);
        Canopy c = cache.get(key);
        if (c != null) {
            if (!buildingSurvival
                    && (!enabled || restoringAll || admissions.ready(key))
                    && (c.preservationSeed != preservationSeed
                            || c.preservationPolicy != PRESERVATION_RULES)) {
                applyPreservation(key, c);
                if (c.dirty) flush(chunk, c);
            }
            return c;
        }
        byte[] bytes =
                chunk.getPersistentDataContainer().get(leavesKey, PersistentDataType.BYTE_ARRAY);
        if (bytes == null) return null;
        try {
            c = Canopy.decode(bytes);
        } catch (IOException | RuntimeException e) {
            throw new IllegalStateException(
                    "Invalid saved seasonal canopy in " + key + "; data was not discarded.", e);
        }
        migrateLegacyOverlays(chunk, c);
        indexed.add(key);
        if (!enabled || restoringAll || buildingSurvival || admissions.ready(key))
            recoverOverlayDiscards(chunk, c);
        if (!buildingSurvival && (!enabled || restoringAll || admissions.ready(key)))
            applyPreservation(key, c);
        put(key, c);
        if (c.dirty) flush(chunk, c);
        return c;
    }

    private static long newPreservationSeed() {
        return java.util.concurrent.ThreadLocalRandom.current().nextLong(1, Long.MAX_VALUE);
    }

    private static double elevationProbability(int y, int seaLevel, double low, double high) {
        double fraction =
                Math.max(
                        0.0,
                        Math.min(
                                1.0,
                                (double) (y - seaLevel) / Math.max(1, GRADIENT_TOP_Y - seaLevel)));
        return low + (high - low) * fraction;
    }

    private boolean choosePreservation(Key key, Canopy c, int i, int seaLevel) {
        if ((c.flags[i] & INVALID) != 0 || !c.canShed(i)) return false;
        double probability =
                (c.flags[i] & TREE_CAP) != 0 ? TREE_CAP_SURVIVAL : c.survivalChances[i];
        return (preservationRank(key, c, i) >>> 11) * 0x1.0p-53 < probability;
    }

    private static long originalAnchor(Key key, Canopy c, int i) {
        int local = c.positions[i], offset = c.offsets[i];
        return pack(
                (key.x << 4) + (local & 15) + ((offset & 15) - 6),
                c.minY + (local >>> 8) + (((offset >>> 4) & 15) - 6),
                (key.z << 4) + ((local >>> 4) & 15) + (((offset >>> 8) & 15) - 6));
    }

    private void buildSurvivalChances(Key key, Canopy center) {
        World world = Bukkit.getWorld(key.world);
        if (world == null) return;
        Map<Key, Canopy> sources = new LinkedHashMap<>();
        boolean previousGuard = buildingSurvival;
        buildingSurvival = true;
        try {
            // A saved leaf is at most six blocks from its anchor: a one-chunk halo
            // contains the complete saved population for every central anchor.
            for (int dx = -1; dx <= 1; dx++)
                for (int dz = -1; dz <= 1; dz++) {
                    Key other = new Key(key.world, key.x + dx, key.z + dz);
                    if (!world.isChunkLoaded(other.x, other.z) && !indexed.contains(other))
                        continue;
                    Canopy c =
                            other.equals(key) ? center : load(world.getChunkAt(other.x, other.z));
                    if (c != null) sources.put(other, c);
                }
            sources.put(key, center);
            Map<Long, SurvivalGroup> groups = new HashMap<>();
            Map<Long, SurvivalLeaf> leaves = new HashMap<>();
            for (Map.Entry<Key, Canopy> entry : sources.entrySet()) {
                Key source = entry.getKey();
                Canopy c = entry.getValue();
                Chunk chunk = world.getChunkAt(source.x, source.z);
                for (int i = 0; i < c.size(); i++) {
                    if ((c.flags[i] & INVALID) != 0) continue;
                    Block b = block(chunk, c, i);
                    BlockData current = b.getBlockData();
                    boolean persistent = current instanceof Leaves l && l.isPersistent();
                    boolean eligible = c.canShed(i) && !persistent;
                    boolean cap = eligible && isTreeCap(b);
                    boolean space =
                            current instanceof Leaves
                                    || (c.legacyOverlays.get(c.positions[i]) == b.getType())
                                    || isTemporaryOverlay(b.getType())
                                    || ((c.flags[i] & REMOVED) != 0 && b.getType().isAir());
                    SurvivalLeaf leaf =
                            new SurvivalLeaf(
                                    source,
                                    c,
                                    i,
                                    pack(b.getX(), b.getY(), b.getZ()),
                                    eligible,
                                    cap,
                                    space);
                    leaves.put(leaf.position, leaf);
                    if (eligible && !cap && space) {
                        SurvivalGroup group =
                                groups.computeIfAbsent(
                                        originalAnchor(source, c, i), k -> new SurvivalGroup());
                        group.layers[c.distances[i]]++;
                        group.target +=
                                elevationProbability(
                                        b.getY(),
                                        world.getSeaLevel(),
                                        LEAF_SURVIVAL_LOW,
                                        LEAF_SURVIVAL_HIGH);
                    }
                }
            }
            // Spend each complete anchor's budget on the innermost distance layers.
            // Only the cutoff layer needs a random annual roll.
            for (SurvivalLeaf leaf : leaves.values()) {
                if (!leaf.eligible) leaf.chance = 1.0f;
                else if (leaf.cap) leaf.chance = (float) TREE_CAP_SURVIVAL;
                else {
                    SurvivalGroup group =
                            groups.get(originalAnchor(leaf.key, leaf.canopy, leaf.index));
                    int distance = leaf.canopy.distances[leaf.index], inside = 0;
                    if (group != null) {
                        for (int d = 1; d < distance; d++) inside += group.layers[d];
                        if (group.layers[distance] > 0)
                            leaf.chance =
                                    (float)
                                            Math.max(
                                                    0,
                                                    Math.min(
                                                            1,
                                                            (group.target - inside)
                                                                    / group.layers[distance]));
                    }
                }
                double roll =
                        (preservationRank(leaf.key, leaf.canopy, leaf.index) >>> 11) * 0x1.0p-53;
                leaf.wanted =
                        leaf.space
                                && (!leaf.eligible
                                        || roll < (leaf.cap ? TREE_CAP_SURVIVAL : leaf.chance));
            }
            for (int i = 0; i < center.size(); i++) {
                int pos = center.positions[i];
                long absolute =
                        pack(
                                (key.x << 4) + (pos & 15),
                                center.minY + (pos >>> 8),
                                (key.z << 4) + ((pos >>> 4) & 15));
                SurvivalLeaf leaf = leaves.get(absolute);
                float chance = leaf == null ? 0.0f : leaf.chance;
                // A failed cap roll or a player edit must not leave a floating outer leaf.
                if (leaf != null && leaf.wanted && !hasSurvivingPath(leaf, leaves, world))
                    chance = 0.0f;
                center.survivalChances[i] = chance;
            }
            center.dirty = true;
        } finally {
            buildingSurvival = previousGuard;
        }
    }

    private boolean hasSurvivingPath(
            SurvivalLeaf leaf, Map<Long, SurvivalLeaf> leaves, World world) {
        if (!leaf.wanted) return false;
        if (leaf.support >= 0) return leaf.support == 1;
        leaf.support = 0;
        Block b = world.getBlockAt(x(leaf.position), y(leaf.position), z(leaf.position));
        if (leaf.cap || findLogFace(b, logFace(leaf.canopy, leaf.index)) != 0) {
            leaf.support = 1;
            return true;
        }
        int distance = leaf.canopy.distances[leaf.index];
        for (int[] direction : DIRECTIONS) {
            int xx = b.getX() + direction[0],
                    yy = b.getY() + direction[1],
                    zz = b.getZ() + direction[2];
            if (yy < world.getMinHeight() || yy >= world.getMaxHeight()) continue;
            SurvivalLeaf parent = leaves.get(pack(xx, yy, zz));
            if (parent != null) {
                if (parent.canopy.distances[parent.index] < distance
                        && hasSurvivingPath(parent, leaves, world)) {
                    leaf.support = 1;
                    return true;
                }
            } else if (world.isChunkLoaded(xx >> 4, zz >> 4)) {
                Block other = world.getBlockAt(xx, yy, zz);
                if (other.getBlockData() instanceof Leaves l
                        && (l.isPersistent()
                                || (other.getType() != Material.OAK_LEAVES
                                        && other.getType() != Material.BIRCH_LEAVES))
                        && supportDistance(other, false) < distance) {
                    leaf.support = 1;
                    return true;
                }
            }
        }
        return false;
    }

    private static final class SurvivalGroup {
        final int[] layers = new int[7];
        double target;
    }

    private static final class SurvivalLeaf {
        final Key key;
        final Canopy canopy;
        final int index;
        final long position;
        final boolean eligible, cap, space;
        float chance;
        boolean wanted;
        int support = -1;

        SurvivalLeaf(
                Key key,
                Canopy canopy,
                int index,
                long position,
                boolean eligible,
                boolean cap,
                boolean space) {
            this.key = key;
            this.canopy = canopy;
            this.index = index;
            this.position = position;
            this.eligible = eligible;
            this.cap = cap;
            this.space = space;
        }
    }

    private boolean isTreeCap(Block leaf) {
        if (leaf.getY() <= leaf.getWorld().getMinHeight()) return false;
        Block below = leaf.getRelative(0, -1, 0);
        return logs.contains(below.getType())
                && below.getBlockData() instanceof Orientable o
                && o.getAxis() == Axis.Y;
    }

    private void setEligibleCount(Key key, int count) {
        Integer previous = eligibleCounts.put(key, count);
        knownEligible += count - (previous == null ? 0 : previous);
    }

    private void setPreservationQuota(Key key, int quota) {
        Integer previous = preservationQuotas.put(key, quota);
        allocatedPreserved += quota - (previous == null ? 0 : previous);
    }

    private long preservationRank(Key key, Canopy c, int i) {
        int local = c.positions[i];
        long position =
                pack(
                        (key.x << 4) + (local & 15),
                        c.minY + (local >>> 8),
                        (key.z << 4) + ((local >>> 4) & 15));
        return mix(
                position
                        ^ key.world.getMostSignificantBits()
                        ^ key.world.getLeastSignificantBits()
                        ^ preservationSeed);
    }

    private void setAdjacentCount(Key key, int count) {
        Integer previous = adjacentCounts.put(key, count);
        knownAdjacent += count - (previous == null ? 0 : previous);
    }

    private static int logFace(Canopy c, int i) {
        return (c.flags[i] & LOG_FACE_MASK) >>> LOG_FACE_SHIFT;
    }

    private int findLogFace(Block leaf, int previous) {
        World world = leaf.getWorld();
        // A saved face is evidence from the last time that neighboring chunk was
        // loaded. Do not load it merely to recheck a frozen, distant block.
        if (previous >= 1 && previous <= DIRECTIONS.length) {
            int[] d = DIRECTIONS[previous - 1];
            int xx = leaf.getX() + d[0], yy = leaf.getY() + d[1], zz = leaf.getZ() + d[2];
            if (yy >= world.getMinHeight() && yy < world.getMaxHeight()) {
                if (!world.isChunkLoaded(xx >> 4, zz >> 4)) return previous;
                if (logs.contains(world.getBlockAt(xx, yy, zz).getType())) return previous;
            }
        }
        for (int face = 0; face < DIRECTIONS.length; face++) {
            if (face + 1 == previous) continue;
            int[] d = DIRECTIONS[face];
            int xx = leaf.getX() + d[0], yy = leaf.getY() + d[1], zz = leaf.getZ() + d[2];
            if (yy < world.getMinHeight()
                    || yy >= world.getMaxHeight()
                    || !world.isChunkLoaded(xx >> 4, zz >> 4)) continue;
            if (logs.contains(world.getBlockAt(xx, yy, zz).getType())) return face + 1;
        }
        return 0;
    }

    private void refreshLogFace(Key key, Canopy c, int i, Block leaf) {
        int before = logFace(c, i);
        boolean previousCap = (c.flags[i] & TREE_CAP) != 0;
        boolean eligible = (c.flags[i] & INVALID) == 0 && c.canShed(i);
        int face = eligible ? findLogFace(leaf, before) : 0;
        boolean cap = eligible && isTreeCap(leaf);
        int next =
                (c.flags[i] & ~(LOG_FACE_MASK | TREE_CAP))
                        | (face << LOG_FACE_SHIFT)
                        | (cap ? TREE_CAP : 0);
        if ((byte) next != c.flags[i]) {
            c.flags[i] = (byte) next;
            c.dirty = true;
        }
        if (face != before && adjacentCounts.containsKey(key))
            setAdjacentCount(
                    key,
                    Math.max(
                            0,
                            adjacentCounts.get(key) + (face == 0 ? 0 : 1) - (before == 0 ? 0 : 1)));
        if (face != before || cap != previousCap) c.preservationPolicy = 0;
        boolean previous = (c.flags[i] & PRESERVED) != 0;
        boolean currentPolicy =
                c.preservationSeed == preservationSeed
                        && c.preservationPolicy == PRESERVATION_RULES;
        boolean desired =
                currentPolicy
                        ? choosePreservation(key, c, i, leaf.getWorld().getSeaLevel())
                        : previous;
        if (desired != previous) {
            if (desired) c.flags[i] |= PRESERVED;
            else c.flags[i] &= ~PRESERVED;
            if (currentPolicy && preservationQuotas.containsKey(key))
                setPreservationQuota(
                        key, Math.max(0, preservationQuotas.get(key) + (desired ? 1 : -1)));
            c.dirty = true;
        }
    }

    private void refreshPreservationCandidates(Key key, Canopy c) {
        World world = Bukkit.getWorld(key.world);
        if (world == null || !world.isChunkLoaded(key.x, key.z)) return;
        Chunk chunk = world.getChunkAt(key.x, key.z);
        int eligible = 0, adjacent = 0;
        for (int i = 0; i < c.size(); i++) {
            refreshLogFace(key, c, i, block(chunk, c, i));
            if ((c.flags[i] & INVALID) == 0 && c.canShed(i)) {
                eligible++;
                if (logFace(c, i) != 0) adjacent++;
            }
        }
        setEligibleCount(key, eligible);
        setAdjacentCount(key, adjacent);
    }

    private void applyPreservation(Key key, Canopy c) {
        applyPreservation(key, c, false);
    }

    private void applyPreservation(Key key, Canopy c, boolean rebuild) {
        if (enabled && !restoringAll && !admissions.ready(key)) return;
        World world = Bukkit.getWorld(key.world);
        if (world == null) return;
        refreshPreservationCandidates(key, c);
        if (rebuild
                || c.preservationSeed != preservationSeed
                || c.preservationPolicy != PRESERVATION_RULES) buildSurvivalChances(key, c);
        int selected = 0;
        for (int i = 0; i < c.size(); i++) {
            boolean desired = choosePreservation(key, c, i, world.getSeaLevel());
            if (desired) selected++;
            if (desired != ((c.flags[i] & PRESERVED) != 0)) {
                if (desired) c.flags[i] |= PRESERVED;
                else c.flags[i] &= ~PRESERVED;
                c.dirty = true;
            }
        }
        if (c.preservationSeed != preservationSeed || c.preservationPolicy != PRESERVATION_RULES) {
            c.preservationSeed = preservationSeed;
            c.preservationPolicy = PRESERVATION_RULES;
            c.dirty = true;
        }
        setPreservationQuota(key, selected);
    }

    private void rerollPreservation() {
        // Only legacy records without a neighbor catalog require a one-time halo load.
        for (Key key : new ArrayList<>(indexed)) {
            World world = Bukkit.getWorld(key.world);
            if (world == null) continue;
            if (enabled && (!world.isChunkLoaded(key.x, key.z) || !admissions.ready(key))) continue;
            boolean missing = adjacencyCatalogUpgrade || !adjacentCounts.containsKey(key);
            if (missing)
                for (int dx = -1; dx <= 1; dx++)
                    for (int dz = -1; dz <= 1; dz++) world.getChunkAt(key.x + dx, key.z + dz);
            if (missing || world.isChunkLoaded(key.x, key.z)) {
                Canopy c = load(world.getChunkAt(key.x, key.z));
                if (c == null) {
                    setEligibleCount(key, 0);
                    setAdjacentCount(key, 0);
                } else refreshPreservationCandidates(key, c);
            }
        }
        long previous = preservationSeed;
        do {
            preservationSeed = newPreservationSeed();
        } while (preservationSeed == previous);
        preservationQuotas.clear();
        allocatedPreserved = 0;
        // Persist the new seed before saving any selections derived from it.
        saveBlocking();
        for (Map.Entry<Key, Canopy> entry : new ArrayList<>(cache.entrySet())) {
            Key key = entry.getKey();
            World world = Bukkit.getWorld(key.world);
            if (world == null
                    || !world.isChunkLoaded(key.x, key.z)
                    || (enabled && !admissions.ready(key))) continue;
            applyPreservation(key, entry.getValue());
            if (entry.getValue().dirty) flush(world.getChunkAt(key.x, key.z), entry.getValue());
        }
    }

    private static boolean isTemporaryOverlay(Material type) {
        if (isFlowerOverlay(type)) return true;
        return switch (type) {
            case WATER,
                            SAND,
                            GRAVEL,
                            LAVA,
                            SNOW,
                            SNOW_BLOCK,
                            VINE,
                            CAVE_VINES,
                            CAVE_VINES_PLANT,
                            WEEPING_VINES,
                            WEEPING_VINES_PLANT,
                            TWISTING_VINES,
                            TWISTING_VINES_PLANT ->
                    true;
            default -> false;
        };
    }

    private static boolean isFlowerOverlay(Material type) {
        return Tag.SMALL_FLOWERS.isTagged(type) || Tag.TALL_FLOWERS.isTagged(type);
    }

    private void removeFlowerCompanion(Block block) {
        if (!isFlowerOverlay(block.getType()) || !(block.getBlockData() instanceof Bisected flower))
            return;
        Block other = block.getRelative(0, flower.getHalf() == Bisected.Half.BOTTOM ? 1 : -1, 0);
        if (other.getType() != block.getType()
                || !(other.getBlockData() instanceof Bisected half)
                || half.getHalf() == flower.getHalf()) return;
        rememberLeafOverlay(other);
        ground.edited(other);
        other.setType(Material.AIR, true);
    }

    private static boolean canRegrowInto(Material type) {
        return type.isAir() || isTemporaryOverlay(type);
    }

    private void rememberLeafOverlay(Block block) {
        if (!enabled || !isTemporaryOverlay(block.getType())) return;
        Key key = key(block.getChunk());
        if (!snow.allowed.contains(key) && !admissions.ready(key)) return;
        Canopy c = load(block.getChunk());
        if (c == null) return;
        int i = c.index(block);
        if (i < 0 || !c.canShed(i) || (c.flags[i] & (INVALID | REMOVED)) != 0) return;
        // Preserve the evidence before snow or a seasonal flower disappears. A later leaf pass
        // may see only air; that is still a temporary overlay, not a missing-leaf discard.
        c.flags[i] |= REMOVED;
        c.dirty = true;
    }

    private static boolean isSnowOverlay(Material type) {
        return type == Material.SNOW || type == Material.SNOW_BLOCK;
    }

    private static boolean isFlowerSpace(Material type) {
        return type.isAir() || isSnowOverlay(type);
    }

    private static boolean observedOverlay(String data) {
        String material = data.split("\\[", 2)[0];
        Material type = Material.matchMaterial(material);
        return type != null && isTemporaryOverlay(type);
    }

    private boolean recoverOverlayDiscard(Canopy c, int i, Block block) {
        if ((c.flags[i] & INVALID) == 0) return true;
        DiscardInfo info = c.discards.get(c.positions[i]);
        boolean eligible =
                info == null
                        ? isTemporaryOverlay(block.getType())
                        : observedOverlay(info.leaf)
                                && !info.reason
                                        .toLowerCase(java.util.Locale.ROOT)
                                        .contains("supporting log");
        if (!eligible || !canRegrowInto(block.getType())) return false;
        c.flags[i] = (byte) ((c.flags[i] & ~INVALID) | REMOVED);
        c.discards.remove(c.positions[i]);
        c.dirty = true;
        Key key = key(block.getChunk());
        if (c.canShed(i) && eligibleCounts.containsKey(key)) {
            setEligibleCount(key, eligibleCounts.get(key) + 1);
            if (logFace(c, i) != 0 && adjacentCounts.containsKey(key))
                setAdjacentCount(key, adjacentCounts.get(key) + 1);
        }
        return true;
    }

    private void recoverOverlayDiscards(Chunk chunk, Canopy c) {
        for (int i = 0; i < c.size(); i++)
            if ((c.flags[i] & INVALID) != 0) recoverOverlayDiscard(c, i, block(chunk, c, i));
    }

    private void evictCanopy(Key key) {
        Canopy c = cache.get(key);
        World world = Bukkit.getWorld(key.world);
        if (c != null && c.dirty && world != null && world.isChunkLoaded(key.x, key.z))
            flush(world.getChunkAt(key.x, key.z), c);
        cache.remove(key);
        work.remove(key);
    }

    private void put(Key key, Canopy c) {
        winterNormalized.remove(key);
        winterNormalizations.remove(key);
        cache.put(key, c);
        work.remove(key);
        if (c.size() > 0) work.addLast(key);
    }

    private void flush(Chunk chunk, Canopy c) {
        try {
            byte[] bytes = c.encode();
            chunk.getPersistentDataContainer().set(leavesKey, PersistentDataType.BYTE_ARRAY, bytes);
            if (c.legacyOverlays.isEmpty())
                chunk.getPersistentDataContainer()
                        .set(legacyCleanupKey, PersistentDataType.LONG, journalHash(bytes));
            c.dirty = false;
        } catch (IOException e) {
            throw new IllegalStateException("Cannot save seasonal canopy", e);
        }
    }

    private boolean updateLeaf(
            Chunk chunk, Canopy c, int i, boolean forceRestore, boolean allowLoads) {
        if (!forceRestore && enabled && !admissions.ready(key(chunk))) return false;
        if (!forceRestore
                && !buildingSurvival
                && (c.preservationSeed != preservationSeed
                        || c.preservationPolicy != PRESERVATION_RULES))
            applyPreservation(key(chunk), c);
        Block block = block(chunk, c, i);
        if (!recoverOverlayDiscard(c, i, block)) return false;
        if ((c.flags[i] & (PRESERVED | TREE_CAP)) != 0) refreshLogFace(key(chunk), c, i, block);
        if (!forceRestore && !buildingSurvival && c.preservationPolicy != PRESERVATION_RULES)
            applyPreservation(key(chunk), c);
        clearLegacyOverlay(chunk, c, i);
        boolean removed = (c.flags[i] & REMOVED) != 0;
        if (!removed) {
            BlockData current = block.getBlockData();
            if (isTemporaryOverlay(current.getMaterial())) {
                c.flags[i] |= REMOVED;
                c.dirty = true;
                removed = true;
            }
            if (!removed && !(current instanceof Leaves)) {
                invalidate(
                        c,
                        i,
                        block,
                        current.getMaterial().isAir()
                                ? "Expected leaf was missing (air)"
                                : "Expected leaf was replaced by another block");
                return false;
            }
            if (!removed && ((Leaves) current).isPersistent()) {
                invalidate(c, i, block, "Leaf became persistent");
                return false;
            }
            if (!removed && current.getMaterial() != c.data(i).getMaterial()) {
                invalidate(c, i, block, "Leaf material changed");
                return false;
            }
            if (!removed && !forceRestore && enabled && shouldBeAbsent(c, i, block)) {
                if (!scannedLoaded.contains(key(chunk))) return false;
                c.flags[i] |= REMOVED;
                c.dirty = true;
                block.setType(Material.AIR, true);
                return true;
            }
            if (!removed) return false;
        }
        if (!forceRestore && enabled && shouldBeAbsent(c, i, block)) return false;
        Block anchor = anchor(block, c.offsets[i], allowLoads);
        if (anchor == null)
            return false; // A bordering chunk is unloaded; never load it during normal work.
        if (anchor.getType() != Material.valueOf(c.logTypes[c.logIds[i] & 0xffff])) {
            invalidate(c, i, block, "Supporting log was missing or changed");
            return false;
        }
        if (!canRegrowInto(block.getType())) {
            invalidate(c, i, block, "Restoration space was occupied");
            return false;
        }
        int support = supportDistance(block, allowLoads);
        if (support > 6) return false;
        Leaves restored = (Leaves) c.data(i).clone();
        restored.setDistance(support);
        if (isFlowerOverlay(block.getType())) {
            removeFlowerCompanion(block);
            ground.edited(block);
        }
        snow.forget(block);
        block.setBlockData(restored, true);
        c.flags[i] &= ~REMOVED;
        c.dirty = true;
        return true;
    }

    private boolean shouldBeAbsent(Canopy c, int i, Block block) {
        return shouldBeAbsent(
                c, i, block.getWorld().getUID(), pack(block.getX(), block.getY(), block.getZ()));
    }

    private boolean shouldBeAbsent(Canopy c, int i, UUID world, long position) {
        if (!c.canShed(i) || (c.flags[i] & PRESERVED) != 0) return false;
        Season season = season();
        if (season == Season.SUMMER) return false;
        if (season == Season.WINTER) return true;
        double fraction = (double) (elapsed % SEASON_TICKS) / SEASON_TICKS;
        double random =
                (mix(
                                        position
                                                ^ world.getMostSignificantBits()
                                                ^ ((elapsed / (4 * SEASON_TICKS))
                                                        * 0x9e3779b97f4a7c15L))
                                >>> 11)
                        * 0x1.0p-53;
        if (season == Season.FALL)
            return Math.min(1.0, fraction / FALL_FINISH_FRACTION)
                    >= (6 - c.distances[i] + random) / 6.0;
        return fraction < (c.distances[i] - 1 + random) / 6.0;
    }

    private static long mix(long z) {
        z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L;
        z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL;
        return z ^ (z >>> 31);
    }

    private Block anchor(Block leaf, short offset, boolean force) {
        int xx = leaf.getX() + ((offset & 15) - 6),
                yy = leaf.getY() + (((offset >>> 4) & 15) - 6),
                zz = leaf.getZ() + (((offset >>> 8) & 15) - 6);
        World w = leaf.getWorld();
        if (!force && !w.isChunkLoaded(xx >> 4, zz >> 4)) return null;
        return w.getBlockAt(xx, yy, zz);
    }

    private int supportDistance(Block block, boolean force) {
        // Vanilla distance properties may still be waiting for physics updates.
        // Find an actual leaf path instead of depending on those cached properties.
        World w = block.getWorld();
        ArrayDeque<Long> frontier = new ArrayDeque<>();
        Set<Long> visited = new HashSet<>();
        long start = pack(block.getX(), block.getY(), block.getZ());
        frontier.add(start);
        visited.add(start);
        for (int distance = 1; distance <= 6 && !frontier.isEmpty(); distance++) {
            int count = frontier.size();
            while (count-- > 0) {
                long position = frontier.removeFirst();
                for (int[] d : DIRECTIONS) {
                    int xx = x(position) + d[0], yy = y(position) + d[1], zz = z(position) + d[2];
                    if (yy < w.getMinHeight()
                            || yy >= w.getMaxHeight()
                            || (!force && !w.isChunkLoaded(xx >> 4, zz >> 4))) continue;
                    long next = pack(xx, yy, zz);
                    if (!visited.add(next)) continue;
                    Block other = w.getBlockAt(xx, yy, zz);
                    if (logs.contains(other.getType())) return distance;
                    if (distance < 6 && other.getBlockData() instanceof Leaves)
                        frontier.addLast(next);
                }
            }
        }
        return 7;
    }

    private static Block block(Chunk chunk, Canopy c, int i) {
        int p = c.positions[i];
        return chunk.getBlock(p & 15, c.minY + (p >>> 8), (p >>> 4) & 15);
    }

    private void invalidate(Canopy c, int i, Block leaf, String reason) {
        // Keep the original cause; a later event must not relabel an older discard.
        if ((c.flags[i] & INVALID) != 0) return;
        Block log = anchor(leaf, c.offsets[i], false);
        c.discards.put(
                c.positions[i],
                new DiscardInfo(
                        System.currentTimeMillis(),
                        reason,
                        leaf.getBlockData().getAsString(),
                        log == null ? "unloaded" : log.getType().name()));
        if (c.canShed(i)) {
            Key key = key(leaf.getChunk());
            if (eligibleCounts.containsKey(key))
                setEligibleCount(key, Math.max(0, eligibleCounts.get(key) - 1));
            if (logFace(c, i) != 0 && adjacentCounts.containsKey(key))
                setAdjacentCount(key, Math.max(0, adjacentCounts.get(key) - 1));
        }
        c.flags[i] |= INVALID;
        if ((c.flags[i] & PRESERVED) != 0 && c.preservationSeed == preservationSeed) {
            Key key = key(leaf.getChunk());
            if (preservationQuotas.containsKey(key))
                setPreservationQuota(key, Math.max(0, preservationQuotas.get(key) - 1));
        }
        c.legacyOverlays.remove(c.positions[i]);
        c.flags[i] &= ~(REMOVED | PRESERVED | LOG_FACE_MASK | TREE_CAP | LEGACY_OVERLAY_FLAG);
        Key changed = key(leaf.getChunk());
        for (int dx = -1; dx <= 1; dx++)
            for (int dz = -1; dz <= 1; dz++) {
                Canopy affected = cache.get(new Key(changed.world, changed.x + dx, changed.z + dz));
                if (affected != null) {
                    affected.preservationPolicy = 0;
                    affected.dirty = true;
                }
            }
        c.dirty = true;
    }

    private int restoreChunkFully(Chunk chunk, Canopy c, boolean force) {
        int restored = 0, progress;
        do {
            progress = 0;
            for (int i = 0; i < c.size(); i++) if (updateLeaf(chunk, c, i, true, force)) progress++;
            restored += progress;
        } while (progress != 0);
        if (c.dirty) flush(chunk, c);
        return restored;
    }

    private int[] restoreAll() {
        restoringAll = true;
        Set<Key> pinned = new HashSet<>();
        try {
            return restoreAllLoaded(pinned);
        } finally {
            for (Key key : pinned) {
                World w = Bukkit.getWorld(key.world);
                if (w != null && w.isChunkLoaded(key.x, key.z))
                    w.getChunkAt(key.x, key.z).removePluginChunkTicket(plugin);
            }
            restoringAll = false;
        }
    }

    private int[] restoreAllLoaded(Set<Key> pinned) {
        int restored = 0, remainingChunks = 0, remainingLeaves = 0, unavailable = 0;
        Map<Key, Canopy> targets = new LinkedHashMap<>();
        int progress;
        boolean discovered, indexGrew;
        do {
            int previousIndexSize = indexed.size();
            discovered = false;
            // Loading a neighbor can reveal another saved canopy. Include it in this
            // command as well, rather than requiring the administrator to run it again.
            for (Key key : new ArrayList<>(indexed)) {
                World w = Bukkit.getWorld(key.world);
                if (w == null || targets.containsKey(key)) continue;
                Chunk chunk = w.getChunkAt(key.x, key.z);
                if (plugin.isEnabled() && chunk.addPluginChunkTicket(plugin)) pinned.add(key);
                targets.put(key, load(chunk));
                discovered = true;
            }
            progress = 0;
            for (Map.Entry<Key, Canopy> entry : targets.entrySet()) {
                Key key = entry.getKey();
                World w = Bukkit.getWorld(key.world);
                Canopy c = entry.getValue();
                if (w == null || c == null) continue;
                Chunk chunk = w.getChunkAt(key.x, key.z);
                try {
                    for (int i = 0; i < c.size(); i++)
                        if (updateLeaf(chunk, c, i, true, true)) progress++;
                } finally {
                    if (c.dirty) flush(chunk, c);
                }
            }
            restored += progress;
            indexGrew = indexed.size() != previousIndexSize;
        } while (progress != 0 || discovered || indexGrew);
        for (Key key : indexed) {
            if (Bukkit.getWorld(key.world) == null) {
                unavailable++;
                continue;
            }
            Canopy c = targets.get(key);
            if (c == null) continue;
            int pending = 0, example = -1;
            for (int i = 0; i < c.size(); i++)
                if ((c.flags[i] & (INVALID | REMOVED)) == REMOVED) {
                    remainingLeaves++;
                    pending++;
                    if (example < 0) example = i;
                }
            if (pending != 0) {
                remainingChunks++;
                World w = Bukkit.getWorld(key.world);
                Block sample = block(w.getChunkAt(key.x, key.z), c, example);
                plugin.getLogger()
                        .warning(
                                "Seasonal restoration retained "
                                        + pending
                                        + " blocked leaf records in "
                                        + w.getName()
                                        + " chunk "
                                        + key.x
                                        + ", "
                                        + key.z
                                        + "; example "
                                        + sample.getX()
                                        + ", "
                                        + sample.getY()
                                        + ", "
                                        + sample.getZ()
                                        + ". No uninterrupted leaf path of at most 6 blocks to a"
                                        + " log is currently available.");
            }
        }
        return new int[] {restored, remainingChunks, remainingLeaves, unavailable};
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onChunkLoad(ChunkLoadEvent e) {
        if (e.getWorld().getEnvironment() != World.Environment.NORMAL) return;
        cleanupLegacyOnLoad(e.getChunk());
        snow.unload(key(e.getChunk()));
        admissions.forget(key(e.getChunk()));
        snow.noteLoaded(e.getChunk());
        if (enabled && !admissions.ready(key(e.getChunk()))) return;
        Canopy c = load(e.getChunk());
        snow.discover(e.getChunk());
        ground.discover(e.getChunk());
        if (!enabled && !restoringAll) ground.restoreChunk(e.getChunk());
        if (!enabled && !restoringAll && c != null) restoreChunkFully(e.getChunk(), c, false);
        if (enabled) queueScan(key(e.getChunk()));
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onChunkUnload(ChunkUnloadEvent e) {
        admissions.forget(key(e.getChunk()));
        snow.unload(key(e.getChunk()));
        ground.unload(e.getChunk());
        Key key = key(e.getChunk());
        Canopy c = cache.remove(key);
        if (c != null && c.dirty) flush(e.getChunk(), c);
        work.remove(key);
        scannedLoaded.remove(key);
        winterNormalized.remove(key);
        winterNormalizations.remove(key);
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onDecay(LeavesDecayEvent e) {
        if (!enabled || !(e.getBlock().getBlockData() instanceof Leaves l) || l.isPersistent())
            return;
        Canopy c = load(e.getBlock().getChunk());
        if (c == null) return;
        int i = c.index(e.getBlock());
        if (i < 0 || (c.flags[i] & (INVALID | REMOVED)) != 0) return;
        Block supporting = anchor(e.getBlock(), c.offsets[i], false);
        if (supporting == null
                || supporting.getType() == Material.valueOf(c.logTypes[c.logIds[i] & 0xffff]))
            e.setCancelled(true);
        else {
            invalidate(
                    c,
                    i,
                    e.getBlock(),
                    "Natural decay after supporting log was missing or changed");
            flush(e.getBlock().getChunk(), c);
        }
    }

    private void edited(Block b, String reason) {
        snow.disown(b);
        ground.edited(b);
        snow.changed(b);
        Canopy c = load(b.getChunk());
        if (c == null) return;
        int i = c.index(b);
        if (i >= 0) {
            if (isTemporaryOverlay(b.getType())) {
                if ((c.flags[i] & INVALID) == 0 || recoverOverlayDiscard(c, i, b)) {
                    c.flags[i] |= REMOVED;
                    c.dirty = true;
                    flush(b.getChunk(), c);
                }
                return;
            }
            invalidate(c, i, b, reason);
            flush(b.getChunk(), c);
        }
    }

    private void scheduleLogNeighbors(List<Block> logsChanged) {
        if (logsChanged.isEmpty()) return;
        List<Location> positions = logsChanged.stream().map(Block::getLocation).toList();
        Bukkit.getScheduler()
                .runTask(
                        plugin,
                        () -> {
                            if (!running) return;
                            Map<Chunk, Canopy> changed = new HashMap<>();
                            for (Location position : positions) {
                                World world = position.getWorld();
                                if (world == null) continue;
                                for (int[] d : DIRECTIONS) {
                                    int xx = position.getBlockX() + d[0],
                                            yy = position.getBlockY() + d[1],
                                            zz = position.getBlockZ() + d[2];
                                    if (yy < world.getMinHeight()
                                            || yy >= world.getMaxHeight()
                                            || !world.isChunkLoaded(xx >> 4, zz >> 4)) continue;
                                    Block leaf = world.getBlockAt(xx, yy, zz);
                                    Canopy c = load(leaf.getChunk());
                                    if (c == null) continue;
                                    int i = c.index(leaf);
                                    if (i >= 0) {
                                        refreshLogFace(key(leaf.getChunk()), c, i, leaf);
                                        if (c.dirty) changed.put(leaf.getChunk(), c);
                                    }
                                }
                            }
                            changed.forEach(
                                    (chunk, canopy) -> {
                                        if (!buildingSurvival
                                                && canopy.preservationPolicy != PRESERVATION_RULES)
                                            applyPreservation(key(chunk), canopy);
                                        flush(chunk, canopy);
                                    });
                        });
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onBreak(BlockBreakEvent e) {
        edited(e.getBlock(), "Block broken by player " + e.getPlayer().getName());
        if (logs.contains(e.getBlock().getType())) scheduleLogNeighbors(List.of(e.getBlock()));
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onPlace(BlockPlaceEvent e) {
        edited(e.getBlock(), "Block placed by player " + e.getPlayer().getName());
        if (logs.contains(e.getBlock().getType())
                || logs.contains(e.getBlockReplacedState().getType()))
            scheduleLogNeighbors(List.of(e.getBlock()));
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onBurn(BlockBurnEvent e) {
        edited(e.getBlock(), "Block burned");
        if (logs.contains(e.getBlock().getType())) scheduleLogNeighbors(List.of(e.getBlock()));
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onExplosion(EntityExplodeEvent e) {
        for (Block b : e.blockList()) edited(b, "Entity explosion");
        scheduleLogNeighbors(
                e.blockList().stream().filter(b -> logs.contains(b.getType())).toList());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onBlockExplosion(BlockExplodeEvent e) {
        for (Block b : e.blockList()) edited(b, "Block explosion");
        scheduleLogNeighbors(
                e.blockList().stream().filter(b -> logs.contains(b.getType())).toList());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onGrowth(StructureGrowEvent e) {
        Set<Key> keys = new HashSet<>();
        Map<Chunk, Canopy> changed = new HashMap<>();
        for (org.bukkit.block.BlockState state : e.getBlocks()) {
            Block b = state.getBlock();
            ground.edited(b);
            keys.add(key(b.getChunk()));
            Canopy c = load(b.getChunk());
            if (c != null) {
                int i = c.index(b);
                if (i >= 0) {
                    if (isTemporaryOverlay(state.getType())) {
                        if ((c.flags[i] & INVALID) == 0) {
                            c.flags[i] |= REMOVED;
                            c.dirty = true;
                            changed.put(b.getChunk(), c);
                        }
                    } else {
                        invalidate(c, i, b, "Tree growth replaced tracked position");
                        changed.put(b.getChunk(), c);
                    }
                }
            }
        }
        changed.forEach(this::flush);
        Bukkit.getScheduler()
                .runTask(
                        plugin,
                        () -> {
                            if (!running || !enabled) return;
                            for (Key key : keys) {
                                scannedLoaded.remove(key);
                                winterNormalized.remove(key);
                                winterNormalizations.remove(key);
                                queueScan(key);
                            }
                        });
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onSeasonalGrassSpread(BlockSpreadEvent e) {
        if (e.getNewState().getType() == Material.GRASS_BLOCK && ground.blocksSpread(e.getBlock()))
            e.setCancelled(true);
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSeasonalFertilize(BlockFertilizeEvent e) {
        for (org.bukkit.block.BlockState state : e.getBlocks()) ground.edited(state.getBlock());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSeasonalEntityChange(EntityChangeBlockEvent e) {
        snow.disown(e.getBlock());
        ground.edited(e.getBlock());
        snow.changed(e.getBlock());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSeasonalPistonExtend(BlockPistonExtendEvent e) {
        for (Block b : e.getBlocks()) {
            ground.edited(b);
            ground.edited(b.getRelative(e.getDirection()));
            snow.changed(b);
            snow.changed(b.getRelative(e.getDirection()));
        }
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSeasonalPistonRetract(BlockPistonRetractEvent e) {
        for (Block b : e.getBlocks()) {
            ground.edited(b);
            ground.edited(b.getRelative(e.getDirection()));
            snow.changed(b);
            snow.changed(b.getRelative(e.getDirection()));
        }
    }

    private void onMain(Runnable action) {
        if (!running) return;
        try {
            Bukkit.getScheduler()
                    .runTask(
                            plugin,
                            () -> {
                                if (running) action.run();
                            });
        } catch (IllegalStateException ignored) {
            /* The plugin is shutting down. */
        }
    }

    private void readState() throws IOException {
        if (!Files.exists(stateFile)) return;
        try (DataInputStream in = new DataInputStream(Files.newInputStream(stateFile))) {
            if (in.readInt() != MAGIC) throw new IOException("Unknown season state format");
            enabled = in.readBoolean();
            elapsed = in.readLong();
            if (elapsed < 0) throw new IOException("Invalid season clock");
            int count = in.readInt();
            if (count < 0 || count > 5_000_000) throw new IOException("Invalid chunk index");
            for (int i = 0; i < count; i++)
                indexed.add(
                        new Key(
                                new UUID(in.readLong(), in.readLong()),
                                in.readInt(),
                                in.readInt()));
            int first = in.read();
            if (first >= 0) {
                int marker =
                        (first << 24)
                                | (in.readUnsignedByte() << 16)
                                | (in.readUnsignedByte() << 8)
                                | in.readUnsignedByte();
                if (marker != PRESERVATION_STATE_MAGIC
                        && marker != ADJACENT_PRESERVATION_STATE_MAGIC
                        && marker != LEGACY_PRESERVATION_STATE_MAGIC)
                    throw new IOException("Unknown preservation state");
                adjacencyCatalogUpgrade = marker == LEGACY_PRESERVATION_STATE_MAGIC;
                preservationSeed = in.readLong();
                if (preservationSeed <= 0 || in.readInt() != indexed.size())
                    throw new IOException("Invalid preservation catalog");
                for (Key key : indexed) {
                    int eligible = in.readInt();
                    int adjacent = adjacencyCatalogUpgrade ? -1 : in.readInt();
                    int quota = in.readInt();
                    if (eligible < -1
                            || eligible > 1048576
                            || adjacent < -1
                            || adjacent > 1048576
                            || quota < -1
                            || quota > 1048576)
                        throw new IOException("Invalid preservation counts");
                    if (eligible >= 0) setEligibleCount(key, eligible);
                    if (adjacent >= 0) setAdjacentCount(key, adjacent);
                    if (quota >= 0 && marker == PRESERVATION_STATE_MAGIC)
                        setPreservationQuota(key, quota);
                }
            } else adjacencyCatalogUpgrade = !indexed.isEmpty();
            ground.readState(in);
            snow.readState(in);
        }
    }

    private byte[] stateBytes() throws IOException {
        ByteArrayOutputStream bytes = new ByteArrayOutputStream();
        try (DataOutputStream out = new DataOutputStream(bytes)) {
            out.writeInt(MAGIC);
            out.writeBoolean(enabled);
            out.writeLong(elapsed);
            out.writeInt(indexed.size());
            for (Key key : indexed) {
                out.writeLong(key.world.getMostSignificantBits());
                out.writeLong(key.world.getLeastSignificantBits());
                out.writeInt(key.x);
                out.writeInt(key.z);
            }
            out.writeInt(PRESERVATION_STATE_MAGIC);
            out.writeLong(preservationSeed);
            out.writeInt(indexed.size());
            for (Key key : indexed) {
                out.writeInt(eligibleCounts.getOrDefault(key, -1));
                out.writeInt(adjacentCounts.getOrDefault(key, -1));
                out.writeInt(preservationQuotas.getOrDefault(key, -1));
            }
            ground.writeState(out);
            snow.writeState(out);
        }
        return bytes.toByteArray();
    }

    private void writeState(byte[] bytes) throws IOException {
        Files.createDirectories(stateFile.getParent());
        Path temporary = stateFile.resolveSibling(stateFile.getFileName() + ".tmp");
        Files.write(temporary, bytes);
        try {
            Files.move(
                    temporary,
                    stateFile,
                    StandardCopyOption.REPLACE_EXISTING,
                    StandardCopyOption.ATOMIC_MOVE);
        } catch (java.nio.file.AtomicMoveNotSupportedException e) {
            Files.move(temporary, stateFile, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private void saveAsync(Runnable success) {
        saveAsync(success, null);
    }

    private void saveAsync(Runnable success, Runnable failure) {
        final byte[] bytes;
        try {
            bytes = stateBytes();
        } catch (IOException e) {
            throw new IllegalStateException(e);
        }
        worker.execute(
                () -> {
                    try {
                        writeState(bytes);
                        if (success != null) onMain(success);
                    } catch (IOException e) {
                        plugin.getLogger()
                                .log(
                                        Level.SEVERE,
                                        "Could not save season state; new canopy changes were not"
                                                + " started.",
                                        e);
                        if (failure != null) onMain(failure);
                    }
                });
    }

    private void saveBlocking() {
        try {
            byte[] bytes = stateBytes();
            Future<?> saved =
                    worker.submit(
                            () -> {
                                try {
                                    writeState(bytes);
                                } catch (IOException e) {
                                    throw new IllegalStateException(e);
                                }
                            });
            saved.get();
        } catch (Exception e) {
            throw new IllegalStateException("Cannot persist season state", e);
        }
    }

    private static Key key(Chunk chunk) {
        return new Key(chunk.getWorld().getUID(), chunk.getX(), chunk.getZ());
    }

    private static long pack(int x, int y, int z) {
        return ((x & 0x3ffffffL) << 38) | ((z & 0x3ffffffL) << 12) | (y & 0xfffL);
    }

    private static int x(long p) {
        return (int) (p >> 38);
    }

    private static int y(long p) {
        return (int) (p << 52 >> 52);
    }

    private static int z(long p) {
        return (int) (p << 26 >> 38);
    }

    // Terrain effects have their own small work budget and compressed per-chunk journal.
    private final class GroundSeasons {
        private static final int STATE_MAGIC = 0x53475231, PATCH_MAGIC = 0x53475031;
        private static final int CHECKS = 768, CHANGES = 48;
        private static final long BUDGET_NANOS = 1_000_000L;
        private static final double FINISH = 0.85;
        private static final int CLUSTER_SIZE = 12;
        private static final double FLOWER_DENSITY = 0.325, FLOWER_VARIANT_CHANCE = 0.10;
        private static final int GROUND_RULES = 2,
                FLOWER_RULES = 3,
                PATCH_POLICY_MAGIC = 0x53475032;
        private final NamespacedKey dataKey = new NamespacedKey(plugin, "season_ground_records_v1");
        private final Set<Key> index = new LinkedHashSet<>();
        private final Map<Key, GroundPatch> patches = new HashMap<>();
        private final ArrayDeque<Key> todo = new ArrayDeque<>(), scanQueue = new ArrayDeque<>();
        private final Set<Key> queued = new HashSet<>();
        private Key scanning;
        private long seed = newPreservationSeed(), scanSerial;
        private int lastRestoredGrass, lastRemovedFlowers, lastUnavailable;
        private final Set<Biome> autumnBiomes =
                EnumSet.of(
                        Biome.PLAINS,
                        Biome.SUNFLOWER_PLAINS,
                        Biome.FOREST,
                        Biome.OLD_GROWTH_BIRCH_FOREST,
                        Biome.BIRCH_FOREST);
        private final Set<Biome> flowerBiomes =
                EnumSet.of(
                        Biome.PLAINS,
                        Biome.SUNFLOWER_PLAINS,
                        Biome.FOREST,
                        Biome.OLD_GROWTH_BIRCH_FOREST,
                        Biome.BIRCH_FOREST,
                        Biome.WINDSWEPT_HILLS,
                        Biome.WINDSWEPT_FOREST);
        private final Material[] flowers = {
            Material.DANDELION,
            Material.POPPY,
            Material.BLUE_ORCHID,
            Material.ALLIUM,
            Material.AZURE_BLUET,
            Material.RED_TULIP,
            Material.ORANGE_TULIP,
            Material.WHITE_TULIP,
            Material.PINK_TULIP,
            Material.OXEYE_DAISY,
            Material.CORNFLOWER,
            Material.LILY_OF_THE_VALLEY
        };

        private long epoch(boolean spring) {
            return mix(
                            seed
                                    ^ (elapsed / (4 * SEASON_TICKS)) * 0x9e3779b97f4a7c15L
                                    ^ (spring ? 0x537072696e67L : 0x46616c6cL))
                    | 1L;
        }

        private double rank(Key key, int position, long salt) {
            return unit(
                    mix(
                            key.world.getMostSignificantBits()
                                    ^ key.world.getLeastSignificantBits()
                                    ^ pack(
                                            (key.x << 4) + (position & 15),
                                            position >>> 8,
                                            (key.z << 4) + ((position >>> 4) & 15))
                                    ^ salt));
        }

        private double unit(long hash) {
            return (hash >>> 11) * 0x1.0p-53;
        }

        private Material[] palette(long springEpoch) {
            List<Material> choices = new ArrayList<>(Arrays.asList(flowers));
            java.util.Collections.shuffle(choices, new java.util.Random(springEpoch));
            return choices.subList(0, 5).toArray(Material[]::new);
        }

        private boolean autumn() {
            return season() == Season.FALL || season() == Season.WINTER;
        }

        private void resetScans() {
            scanSerial++;
            scanning = null;
            scanQueue.clear();
            queued.clear();
        }

        private void discover(Chunk chunk) {
            if (enabled && !admissions.ready(key(chunk))) return;
            GroundPatch p = load(chunk);
            if (!enabled || !nearPlayer(key(chunk))) return;
            boolean need =
                    autumn()
                            ? p.grassEpoch != epoch(false) || p.grassPolicy != GROUND_RULES
                            : season() == Season.SPRING
                                    && (p.flowerEpoch != epoch(true)
                                            || p.flowerPolicy != FLOWER_RULES);
            if (need && queued.add(key(chunk))) scanQueue.addLast(key(chunk));
        }

        private GroundPatch load(Chunk chunk) {
            Key key = key(chunk);
            GroundPatch p = patches.get(key);
            if (p != null) return p;
            byte[] bytes =
                    chunk.getPersistentDataContainer().get(dataKey, PersistentDataType.BYTE_ARRAY);
            try {
                p =
                        bytes == null
                                ? new GroundPatch(chunk.getWorld().getMinHeight())
                                : decode(bytes);
            } catch (IOException | RuntimeException e) {
                throw new IllegalStateException(
                        "Invalid saved seasonal ground in " + key + "; records were not discarded.",
                        e);
            }
            patches.put(key, p);
            todo.remove(key);
            todo.addLast(key);
            if (bytes != null && (!p.grass.isEmpty() || !p.flowers.isEmpty()) && index.add(key))
                saveAsync(null);
            return p;
        }

        private Block at(Chunk chunk, GroundPatch p, int position) {
            return chunk.getBlock(position & 15, p.minY + (position >>> 8), (position >>> 4) & 15);
        }

        private boolean due(Key key, int pos, long token, double progress) {
            return rank(key, pos, token) < Math.min(1.0, progress / FINISH);
        }

        private boolean wantsDirt(Key key, GroundPatch p, GroundGrass r) {
            if (!enabled || p.grassEpoch != epoch(false)) return false;
            double progress = (double) (elapsed % SEASON_TICKS) / SEASON_TICKS;
            if (season() == Season.WINTER) return true;
            if (season() == Season.FALL)
                return due(key, r.position, p.grassEpoch ^ 0x53686564L, progress);
            return season() == Season.SPRING
                    && r.state == 1
                    && !due(key, r.position, p.grassEpoch ^ 0x526567726f77L, progress);
        }

        private boolean grassStep(Chunk chunk, GroundPatch p, GroundGrass r, boolean restore) {
            if (r.state == 2) return false;
            Block block = at(chunk, p, r.position);
            boolean desired = !restore && wantsDirt(key(chunk), p, r);
            if (r.state == 1) {
                if (block.getType() != Material.COARSE_DIRT) {
                    // A player or natural process changed our block: relinquish ownership.
                    r.state = 2;
                    p.dirty = true;
                    return false;
                }
                if (!desired) {
                    r.state = 2;
                    p.dirty = true;
                    block.setBlockData(Bukkit.createBlockData(r.original), true);
                    return true;
                }
            } else {
                if (block.getType() == Material.COARSE_DIRT) {
                    // Recover a journal written immediately before a chunk save/crash.
                    r.state = 1;
                    p.dirty = true;
                    return grassStep(chunk, p, r, restore);
                }
                if (block.getType() != Material.GRASS_BLOCK
                        || restore
                        || !enabled
                        || p.grassEpoch != epoch(false)
                        || (!autumn() && season() != Season.SPRING)) {
                    r.state = 2;
                    p.dirty = true;
                    return false;
                }
                if (desired
                        && autumn()
                        && autumnBiomes.contains(block.getBiome())
                        && block.getRelative(0, 1, 0).getType().isAir()) {
                    r.state = 1;
                    p.dirty = true;
                    block.setType(Material.COARSE_DIRT, true);
                    return true;
                }
                if (season() == Season.SPRING) {
                    r.state = 2;
                    p.dirty = true;
                }
            }
            return false;
        }

        private boolean flowerStep(Chunk chunk, GroundPatch p, GroundFlower r, boolean restore) {
            if (r.state == 2) return false;
            Block block = at(chunk, p, r.position);
            double progress = (double) (elapsed % SEASON_TICKS) / SEASON_TICKS;
            boolean current = p.flowerEpoch == epoch(true);
            boolean keep =
                    enabled
                            && !restore
                            && ((season() == Season.SPRING && current)
                                    || (season() == Season.SUMMER
                                            && p.flowerEpoch == previousSpringEpoch()
                                            && !due(
                                                    key(chunk),
                                                    r.position,
                                                    p.flowerEpoch ^ 0x53756d6d6572L,
                                                    progress)));
            if (r.state == 0 && block.getType() == r.type) {
                r.state = 1;
                p.dirty = true;
            }
            // Snow cannot invalidate a flower we still own, even if it appeared after planting.
            boolean reclaimSnow = r.state == 1 && keep && isSnowOverlay(block.getType());
            if (r.state == 1 && !reclaimSnow) {
                if (block.getType() != r.type) {
                    r.state = 2;
                    p.dirty = true;
                    return false;
                }
                if (!keep) {
                    r.state = 2;
                    p.dirty = true;
                    rememberLeafOverlay(block);
                    block.setType(Material.AIR, false); // Seasonal disappearance creates no drops.
                    return true;
                }
                return false;
            }
            if (!keep || (season() != Season.SPRING && !reclaimSnow)) {
                r.state = 2;
                p.dirty = true;
                return false;
            }
            if (!reclaimSnow && !due(key(chunk), r.position, p.flowerEpoch, progress)) return false;
            if (!isFlowerSpace(block.getType())) {
                r.state = 2;
                p.dirty = true;
                return false;
            }
            Block support = block.getRelative(0, -1, 0);
            if (!flowerBiomes.contains(support.getBiome())) {
                r.state = 2;
                p.dirty = true;
                return false;
            }
            if (support.getType() == Material.COARSE_DIRT && ownsCoarse(p, r.position - 256))
                return false; // Wait for this spring's grass restoration.
            BlockData data = Bukkit.createBlockData(r.type);
            if (support.getType() != Material.GRASS_BLOCK || !block.canPlace(data)) {
                r.state = 2;
                p.dirty = true;
                return false;
            }
            r.state = 1;
            p.dirty = true;
            snow.forget(block);
            block.setBlockData(data, true);
            rememberLeafOverlay(block);
            return true;
        }

        private long previousSpringEpoch() {
            long year = elapsed / (4 * SEASON_TICKS) - 1;
            return (mix(seed ^ year * 0x9e3779b97f4a7c15L ^ 0x537072696e67L) | 1L);
        }

        private boolean ownsCoarse(GroundPatch p, int position) {
            for (GroundGrass r : p.grass) if (r.position == position && r.state == 1) return true;
            return false;
        }

        private void tick() {
            if (enabled && scanning == null && ticks % 4 == 0) startScan();
            long deadline = System.nanoTime() + BUDGET_NANOS;
            int checks = 0, changes = 0, rounds = todo.size();
            while (rounds-- > 0
                    && !todo.isEmpty()
                    && checks < CHECKS
                    && changes < CHANGES
                    && System.nanoTime() < deadline) {
                Key key = todo.removeFirst();
                World world = Bukkit.getWorld(key.world);
                GroundPatch p = patches.get(key);
                if (p == null || world == null || !world.isChunkLoaded(key.x, key.z)) {
                    patches.remove(key);
                    continue;
                }
                Chunk chunk = world.getChunkAt(key.x, key.z);
                if (!nearPlayer(key)) {
                    if (p.dirty) flush(chunk, p);
                    patches.remove(key);
                    continue;
                }
                if (enabled && !admissions.ready(key)) {
                    todo.addLast(key);
                    continue;
                }
                int size = p.grass.size() + p.flowers.size();
                for (int j = 0;
                        j < Math.min(size, 96)
                                && checks < CHECKS
                                && changes < CHANGES
                                && System.nanoTime() < deadline;
                        j++) {
                    int i = p.cursor++ % size;
                    if (p.cursor < 0) p.cursor = 0;
                    checks++;
                    boolean changed =
                            i < p.grass.size()
                                    ? grassStep(chunk, p, p.grass.get(i), false)
                                    : flowerStep(
                                            chunk, p, p.flowers.get(i - p.grass.size()), false);
                    if (changed) changes++;
                }
                if (p.dirty) flush(chunk, p);
                todo.addLast(key);
            }
        }

        private void startScan() {
            int attempts = 32;
            while (!scanQueue.isEmpty() && attempts-- > 0) {
                Key key = scanQueue.removeFirst();
                queued.remove(key);
                World world = Bukkit.getWorld(key.world);
                if (world == null
                        || !world.isChunkLoaded(key.x, key.z)
                        || !nearPlayer(key)
                        || !admissions.ready(key)) continue;
                Chunk chunk = world.getChunkAt(key.x, key.z);
                GroundPatch p = load(chunk);
                boolean spring = season() == Season.SPRING;
                if ((!spring && !autumn())
                        || ((spring ? p.flowerEpoch : p.grassEpoch) == epoch(spring)
                                && (spring
                                        ? p.flowerPolicy == FLOWER_RULES
                                        : p.grassPolicy == GROUND_RULES))) continue;
                // A policy upgrade must not regrow flowers already harvested this spring.
                Set<Integer> releasedFlowers = new HashSet<>();
                if (spring && p.flowerEpoch == epoch(true))
                    for (GroundFlower r : p.flowers)
                        if (r.state == 2) releasedFlowers.add(r.position);
                // Reconcile skipped years and earlier rules before selecting new candidates.
                for (GroundGrass r : p.grass)
                    if (p.grassEpoch != epoch(false) || (!spring && p.grassPolicy != GROUND_RULES))
                        grassStep(chunk, p, r, true);
                for (GroundFlower r : p.flowers)
                    if (!spring || p.flowerEpoch != epoch(true) || p.flowerPolicy != FLOWER_RULES)
                        flowerStep(chunk, p, r, true);
                if (p.dirty) flush(chunk, p);
                Set<Integer> coarse = new HashSet<>();
                for (GroundGrass r : p.grass) if (r.state == 1) coarse.add(r.position);
                ChunkSnapshot snapshot = chunk.getChunkSnapshot(false, false, false);
                long token = epoch(spring), serial = ++scanSerial, requestGeneration = generation;
                int minY = world.getMinHeight(), maxY = world.getMaxHeight();
                scanning = key;
                worker.execute(
                        () -> {
                            try {
                                GroundPatch built =
                                        scanGround(
                                                key,
                                                snapshot,
                                                minY,
                                                maxY,
                                                spring,
                                                token,
                                                coarse,
                                                releasedFlowers);
                                onMain(
                                        () -> {
                                            if (serial != scanSerial) return;
                                            if (!enabled
                                                    || generation != requestGeneration
                                                    || spring != (season() == Season.SPRING)
                                                    || token != epoch(spring)
                                                    || !world.isChunkLoaded(key.x, key.z)
                                                    || !nearPlayer(key)
                                                    || !admissions.ready(key)) {
                                                scanning = null;
                                                return;
                                            }
                                            // Paper 1.18.2 snapshots can misindex 3D biomes. Check
                                            // live biomes on the main thread.
                                            Chunk candidateChunk = world.getChunkAt(key.x, key.z);
                                            built.grass.removeIf(
                                                    r -> {
                                                        Block b =
                                                                at(
                                                                        candidateChunk,
                                                                        built,
                                                                        r.position);
                                                        return b.getType() != Material.GRASS_BLOCK
                                                                || !b.getRelative(0, 1, 0)
                                                                        .getType()
                                                                        .isAir()
                                                                || !autumnBiomes.contains(
                                                                        b.getBiome());
                                                    });
                                            if (!spring) {
                                                built.eligibleGrass = built.grass.size();
                                                built.grass.removeIf(
                                                        r ->
                                                                rank(key, r.position, token)
                                                                        >= elevationProbability(
                                                                                built.minY
                                                                                        + (r.position
                                                                                                >>> 8),
                                                                                world.getSeaLevel(),
                                                                                GRASS_CHANCE_LOW,
                                                                                GRASS_CHANCE_HIGH));
                                                built.grass.sort(
                                                        Comparator.comparingInt(r -> r.position));
                                            }
                                            built.flowers.removeIf(
                                                    r ->
                                                            !flowerBiomes.contains(
                                                                    at(
                                                                                    candidateChunk,
                                                                                    built,
                                                                                    r.position)
                                                                            .getRelative(0, -1, 0)
                                                                            .getBiome()));
                                            Runnable install =
                                                    () -> {
                                                        if (serial != scanSerial) return;
                                                        scanning = null;
                                                        if (!enabled
                                                                || generation != requestGeneration
                                                                || token != epoch(spring)
                                                                || spring
                                                                        != (season()
                                                                                == Season.SPRING)
                                                                || !world.isChunkLoaded(
                                                                        key.x, key.z)
                                                                || !admissions.ready(key)) return;
                                                        Chunk live = world.getChunkAt(key.x, key.z);
                                                        GroundPatch current = load(live);
                                                        // Snapshots may precede a build or a new
                                                        // plant; validate again before owning a
                                                        // position.
                                                        for (GroundGrass r : built.grass) {
                                                            Block b = at(live, built, r.position);
                                                            if (b.getType() != Material.GRASS_BLOCK
                                                                    || !b.getRelative(0, 1, 0)
                                                                            .getType()
                                                                            .isAir()
                                                                    || !autumnBiomes.contains(
                                                                            b.getBiome()))
                                                                r.state = 2;
                                                        }
                                                        for (GroundFlower r : built.flowers) {
                                                            Block b = at(live, built, r.position),
                                                                    below = b.getRelative(0, -1, 0);
                                                            if (!isFlowerSpace(b.getType())
                                                                    || !flowerBiomes.contains(
                                                                            below.getBiome())
                                                                    || (below.getType()
                                                                                    != Material
                                                                                            .GRASS_BLOCK
                                                                            && !(below.getType()
                                                                                            == Material
                                                                                                    .COARSE_DIRT
                                                                                    && ownsCoarse(
                                                                                            current,
                                                                                            r.position
                                                                                                    - 256))))
                                                                r.state = 2;
                                                        }
                                                        if (spring) {
                                                            current.flowers.clear();
                                                            current.flowers.addAll(built.flowers);
                                                            current.flowerEpoch = token;
                                                            current.flowerPolicy = FLOWER_RULES;
                                                        } else {
                                                            current.grass.clear();
                                                            current.grass.addAll(built.grass);
                                                            current.grassEpoch = token;
                                                            current.grassPolicy = GROUND_RULES;
                                                            current.eligibleGrass =
                                                                    built.eligibleGrass;
                                                        }
                                                        current.cursor = 0;
                                                        current.dirty = true;
                                                        flush(
                                                                world.getChunkAt(key.x, key.z),
                                                                current);
                                                    };
                                            if ((!built.grass.isEmpty() || !built.flowers.isEmpty())
                                                    && index.add(key))
                                                saveAsync(
                                                        install,
                                                        () -> {
                                                            index.remove(key);
                                                            if (serial == scanSerial)
                                                                scanning = null;
                                                        });
                                            else install.run();
                                        });
                            } catch (Exception e) {
                                plugin.getLogger()
                                        .log(Level.SEVERE, "Could not scan seasonal ground", e);
                                onMain(
                                        () -> {
                                            if (serial == scanSerial) scanning = null;
                                        });
                            }
                        });
                return;
            }
        }

        private GroundPatch scanGround(
                Key key,
                ChunkSnapshot snapshot,
                int minY,
                int maxY,
                boolean spring,
                long token,
                Set<Integer> coarse,
                Set<Integer> releasedFlowers) {
            GroundPatch p = new GroundPatch(minY);
            Material[] palette = palette(token);
            for (int y = minY; y < maxY - 1; y++)
                for (int x = 0; x < 16; x++)
                    for (int z = 0; z < 16; z++) {
                        Material type = snapshot.getBlockType(x, y, z);
                        int position = ((y - minY) << 8) | (z << 4) | x;
                        if (type != Material.GRASS_BLOCK
                                && !(spring
                                        && type == Material.COARSE_DIRT
                                        && coarse.contains(position))) continue;
                        Material above = snapshot.getBlockType(x, y + 1, z);
                        if (spring ? !isFlowerSpace(above) : !above.isAir()) continue;
                        if (!spring) {
                            p.grass.add(
                                    new GroundGrass(
                                            position,
                                            snapshot.getBlockData(x, y, z).getAsString(),
                                            0));
                        } else {
                            if (releasedFlowers.contains(position + 256)) continue;
                            Material flower = clusteredFlower(key, x, z, position, token, palette);
                            if (flower != null)
                                p.flowers.add(new GroundFlower(position + 256, flower, 0));
                        }
                    }
            return p;
        }

        private Material clusteredFlower(
                Key key, int x, int z, int position, long token, Material[] palette) {
            int wx = (key.x << 4) + x, wz = (key.z << 4) + z;
            int cellX = Math.floorDiv(wx, CLUSTER_SIZE), cellZ = Math.floorDiv(wz, CLUSTER_SIZE);
            double best = 0;
            int chosen = -1;
            long worldSeed =
                    token
                            ^ key.world.getMostSignificantBits()
                            ^ key.world.getLeastSignificantBits();
            for (int dx = -1; dx <= 1; dx++)
                for (int dz = -1; dz <= 1; dz++) {
                    int cx = cellX + dx, cz = cellZ + dz;
                    long hash = mix(worldSeed ^ pack(cx, 0, cz));
                    double centerX = cx * (double) CLUSTER_SIZE + 2 + unit(hash) * 8;
                    double centerZ = cz * (double) CLUSTER_SIZE + 2 + unit(mix(hash)) * 8;
                    double radius = 3 + unit(mix(hash ^ 91)) * 2;
                    double d =
                            ((wx - centerX) * (wx - centerX) + (wz - centerZ) * (wz - centerZ))
                                    / (radius * radius);
                    double chance = Math.max(0, 1 - d) * FLOWER_DENSITY;
                    if (chance > best) {
                        best = chance;
                        chosen = Math.floorMod(mix(hash ^ 17), palette.length);
                    }
                }
            if (chosen < 0 || rank(key, position, token ^ 0x466c6f776572L) >= best) return null;
            if (palette.length > 1
                    && rank(key, position, token ^ 0x56617269616e74L) < FLOWER_VARIANT_CHANCE) {
                int alternative =
                        (int) (rank(key, position, token ^ 0x4d69786564L) * (palette.length - 1));
                if (alternative >= chosen) alternative++;
                chosen = alternative;
            }
            return palette[chosen];
        }

        private void flush(Chunk chunk, GroundPatch p) {
            try {
                ByteArrayOutputStream bytes = new ByteArrayOutputStream();
                try (DataOutputStream out = new DataOutputStream(new GZIPOutputStream(bytes))) {
                    out.writeInt(PATCH_MAGIC);
                    out.writeInt(p.minY);
                    out.writeLong(p.grassEpoch);
                    out.writeLong(p.flowerEpoch);
                    out.writeInt(p.eligibleGrass);
                    out.writeInt(p.grass.size());
                    for (GroundGrass r : p.grass) {
                        out.writeInt(r.position);
                        out.writeUTF(r.original);
                        out.writeByte(r.state);
                    }
                    out.writeInt(p.flowers.size());
                    for (GroundFlower r : p.flowers) {
                        out.writeInt(r.position);
                        out.writeUTF(r.type.name());
                        out.writeByte(r.state);
                    }
                    out.writeInt(PATCH_POLICY_MAGIC);
                    out.writeInt(p.grassPolicy);
                    out.writeInt(p.flowerPolicy);
                }
                chunk.getPersistentDataContainer()
                        .set(dataKey, PersistentDataType.BYTE_ARRAY, bytes.toByteArray());
                p.dirty = false;
            } catch (IOException e) {
                throw new IllegalStateException("Cannot save seasonal ground", e);
            }
        }

        private GroundPatch decode(byte[] bytes) throws IOException {
            try (DataInputStream in =
                    new DataInputStream(new GZIPInputStream(new ByteArrayInputStream(bytes)))) {
                if (in.readInt() != PATCH_MAGIC)
                    throw new IOException("Unknown seasonal ground format");
                GroundPatch p = new GroundPatch(in.readInt());
                p.grassEpoch = in.readLong();
                p.flowerEpoch = in.readLong();
                p.eligibleGrass = in.readInt();
                int n = count(in);
                for (int i = 0; i < n; i++) {
                    int position = in.readInt();
                    String original = in.readUTF();
                    int state = in.readUnsignedByte();
                    if (position < 0 || state > 2 || !original.startsWith("minecraft:grass_block"))
                        throw new IOException("Invalid seasonal grass record");
                    p.grass.add(new GroundGrass(position, original, state));
                }
                n = count(in);
                for (int i = 0; i < n; i++) {
                    int position = in.readInt();
                    Material type = Material.valueOf(in.readUTF());
                    int state = in.readUnsignedByte();
                    if (position < 256 || state > 2 || !Arrays.asList(flowers).contains(type))
                        throw new IOException("Invalid seasonal flower record");
                    p.flowers.add(new GroundFlower(position, type, state));
                }
                // Old terrain journals end here and are replanned under the current rules.
                try {
                    if (in.readInt() != PATCH_POLICY_MAGIC)
                        throw new IOException("Unknown ground policy");
                    p.grassPolicy = in.readInt();
                    p.flowerPolicy = in.readInt();
                } catch (java.io.EOFException oldJournal) {
                    p.grassPolicy = 0;
                    p.flowerPolicy = 0;
                }
                return p;
            }
        }

        private int count(DataInputStream in) throws IOException {
            int n = in.readInt();
            if (n < 0 || n > 1048576) throw new IOException("Invalid seasonal ground count");
            return n;
        }

        private void writeState(DataOutputStream out) throws IOException {
            out.writeInt(STATE_MAGIC);
            out.writeLong(seed);
            out.writeInt(index.size());
            for (Key key : index) {
                out.writeLong(key.world.getMostSignificantBits());
                out.writeLong(key.world.getLeastSignificantBits());
                out.writeInt(key.x);
                out.writeInt(key.z);
            }
        }

        private void readState(DataInputStream in) throws IOException {
            int first = in.read();
            if (first < 0) return; // Existing leaf-only journals have no terrain extension.
            int marker =
                    (first << 24)
                            | (in.readUnsignedByte() << 16)
                            | (in.readUnsignedByte() << 8)
                            | in.readUnsignedByte();
            if (marker != STATE_MAGIC) throw new IOException("Unknown seasonal ground state");
            seed = in.readLong();
            int n = in.readInt();
            if (n < 0 || n > 5_000_000) throw new IOException("Invalid seasonal ground index");
            for (int i = 0; i < n; i++)
                index.add(
                        new Key(
                                new UUID(in.readLong(), in.readLong()),
                                in.readInt(),
                                in.readInt()));
        }

        private void unload(Chunk chunk) {
            Key key = key(chunk);
            GroundPatch p = patches.remove(key);
            if (p != null && p.dirty) flush(chunk, p);
            todo.remove(key);
        }

        private void shutdown() {
            resetScans();
            for (var entry : patches.entrySet()) {
                World w = Bukkit.getWorld(entry.getKey().world);
                if (entry.getValue().dirty
                        && w != null
                        && w.isChunkLoaded(entry.getKey().x, entry.getKey().z))
                    flush(w.getChunkAt(entry.getKey().x, entry.getKey().z), entry.getValue());
            }
        }

        private void restoreChunk(Chunk chunk) {
            GroundPatch p = load(chunk);
            for (GroundGrass r : p.grass) if (grassStep(chunk, p, r, true)) lastRestoredGrass++;
            for (GroundFlower r : p.flowers)
                if (flowerStep(chunk, p, r, true)) lastRemovedFlowers++;
            if (p.dirty) flush(chunk, p);
        }

        private void restoreAll() {
            resetScans();
            lastRestoredGrass = 0;
            lastRemovedFlowers = 0;
            lastUnavailable = 0;
            Set<Key> targets = new LinkedHashSet<>(index);
            targets.addAll(patches.keySet());
            Set<Key> tickets = new HashSet<>();
            try {
                for (Key key : targets) {
                    World world = Bukkit.getWorld(key.world);
                    if (world == null) {
                        lastUnavailable++;
                        continue;
                    }
                    Chunk chunk = world.getChunkAt(key.x, key.z);
                    if (plugin.isEnabled() && chunk.addPluginChunkTicket(plugin)) tickets.add(key);
                    restoreChunk(chunk);
                }
            } finally {
                for (Key key : tickets) {
                    World w = Bukkit.getWorld(key.world);
                    if (w != null && w.isChunkLoaded(key.x, key.z))
                        w.getChunkAt(key.x, key.z).removePluginChunkTicket(plugin);
                }
            }
        }

        private void edited(Block block) {
            if (block.getWorld().getEnvironment() != World.Environment.NORMAL) return;
            GroundPatch p = load(block.getChunk());
            int pos =
                    ((block.getY() - p.minY) << 8)
                            | ((block.getZ() & 15) << 4)
                            | (block.getX() & 15);
            // Explicit edits terminate ownership, except snow covering a flower position.
            // Replacing a flower with the same material still counts as an explicit edit.
            for (GroundGrass r : p.grass)
                if (r.position == pos && r.state != 2) {
                    r.state = 2;
                    p.dirty = true;
                }
            for (GroundFlower r : p.flowers)
                if (r.position == pos && r.state != 2 && !isSnowOverlay(block.getType())) {
                    r.state = 2;
                    p.dirty = true;
                }
            if (p.dirty) flush(block.getChunk(), p);
        }

        private boolean blocksSpread(Block block) {
            if (!enabled || !autumn()) return false;
            GroundPatch p = load(block.getChunk());
            int pos =
                    ((block.getY() - p.minY) << 8)
                            | ((block.getZ() & 15) << 4)
                            | (block.getX() & 15);
            return block.getType() == Material.COARSE_DIRT && ownsCoarse(p, pos);
        }

        private void status(CommandSender sender) {
            long chosen = 0, coarse = 0, planned = 0, planted = 0, eligible = 0;
            for (GroundPatch p : patches.values()) {
                eligible += p.eligibleGrass;
                for (GroundGrass r : p.grass) {
                    if (r.state != 2) chosen++;
                    if (r.state == 1) coarse++;
                }
                for (GroundFlower r : p.flowers) {
                    if (r.state == 0) planned++;
                    if (r.state == 1) planted++;
                }
            }
            sender.sendMessage(
                    "§eGround (cached): §f"
                            + coarse
                            + "§7 converted coarse dirt; §f"
                            + chosen
                            + "§7 active selections / §f"
                            + eligible
                            + "§7 fall candidates (20% at sea level to 50% at Y 130+).");
            sender.sendMessage(
                    "§eFlowers (cached): §f" + planted + "§7 placed; §f" + planned + "§7 planned.");
            sender.sendMessage(
                    "§e"
                            + (season() == Season.SPRING ? "This" : "Next")
                            + " spring's flowers: §f"
                            + Arrays.stream(palette(epoch(true)))
                                    .map(m -> m.name().toLowerCase(java.util.Locale.ROOT))
                                    .collect(java.util.stream.Collectors.joining(", "))
                            + ".");
            sender.sendMessage(
                    "§eGround saved chunks: §f"
                            + index.size()
                            + "§e; scans queued: §f"
                            + scanQueue.size()
                            + (scanning == null ? "§7 (idle)." : "§7 (one scan in progress)."));
        }
    }

    private static final class GroundPatch {
        final int minY;
        long grassEpoch, flowerEpoch;
        int eligibleGrass, cursor, grassPolicy, flowerPolicy;
        boolean dirty;
        final List<GroundGrass> grass = new ArrayList<>();
        final List<GroundFlower> flowers = new ArrayList<>();

        GroundPatch(int minY) {
            this.minY = minY;
        }
    }

    private static final class GroundGrass {
        final int position;
        final String original;
        int state; // 0 selected, 1 converted, 2 released.

        GroundGrass(int position, String original, int state) {
            this.position = position;
            this.original = original;
            this.state = state;
        }
    }

    private static final class GroundFlower {
        final int position;
        final Material type;
        int state; // 0 planned, 1 planted, 2 released (never regrow a harvested flower).

        GroundFlower(int position, Material type, int state) {
            this.position = position;
            this.type = type;
            this.state = state;
        }
    }

    private enum Season {
        SUMMER,
        FALL,
        WINTER,
        SPRING
    }

    private record Key(UUID world, int x, int z) {}

    private record DiscardInfo(long timeMillis, String reason, String leaf, String log) {}

    private record DiscardEntry(Key key, Canopy canopy, int index) {
        int x() {
            return (key.x << 4) + (canopy.positions[index] & 15);
        }

        int y() {
            return canopy.minY + (canopy.positions[index] >>> 8);
        }

        int z() {
            return (key.z << 4) + ((canopy.positions[index] >>> 4) & 15);
        }
    }

    private record Row(
            int position, short offset, String data, String log, byte distance, byte flags) {}

    private static final class TagName {
        static boolean isLeaves(Material m) {
            return m.name().endsWith("_LEAVES");
        }
    }

    private static final class Scan {
        final Key key;
        final int minY, maxY;
        final long generation;
        final ChunkSnapshot[] snapshots = new ChunkSnapshot[9];
        int captured;
        boolean submitted;

        Scan(Key key, int minY, int maxY, long generation) {
            this.key = key;
            this.minY = minY;
            this.maxY = maxY;
            this.generation = generation;
        }
    }

    private static final class Node {
        final long position;
        final Leaves leaf;
        long anchor;
        Material anchorType;
        int distance;

        Node(long position, Material type, Leaves leaf, boolean log) {
            this.position = position;
            this.leaf = leaf;
            distance = log ? 0 : 7;
            anchor = position;
            anchorType = type;
        }
    }

    public static boolean tridentRainApplies(World world) {
        Seasons seasons = activeSeasons;
        return seasons != null && seasons.enabled && Weather.tridentRainActive(world);
    }

    public static void tridentRainChanged(World world, boolean active) {
        Seasons seasons = activeSeasons;
        if (seasons == null || !seasons.enabled || world == null) return;
        seasons.snow.tridentRainChanged(world, active);
    }

    /** Used by Weather to apply normal precipitation intensity wherever seasonal snow appears. */
    public static boolean winterSnowAt(Location location) {
        Seasons seasons = activeSeasons;
        World world = location.getWorld();
        if (seasons == null
                || !seasons.enabled
                || world == null
                || world.getEnvironment() != World.Environment.NORMAL) return false;
        Key key = new Key(world.getUID(), location.getBlockX() >> 4, location.getBlockZ() >> 4);
        return location.getY() >= seasons.snow.minimumSnowY(key);
    }

    private boolean coldHalf() {
        long phase = Math.floorMod(elapsed, 4 * SEASON_TICKS);
        return phase * 2 >= 3 * SEASON_TICKS && phase * 2 < 7 * SEASON_TICKS;
    }

    private void cleanupLegacyOnLoad(Chunk chunk) {
        byte[] bytes =
                chunk.getPersistentDataContainer().get(leavesKey, PersistentDataType.BYTE_ARRAY);
        if (bytes == null) return;
        Long cleaned =
                chunk.getPersistentDataContainer().get(legacyCleanupKey, PersistentDataType.LONG);
        if (cleaned != null && cleaned == journalHash(bytes)) return;
        Canopy c = cache.get(key(chunk));
        if (c == null) {
            try {
                c = Canopy.decode(bytes);
            } catch (IOException | RuntimeException ex) {
                throw new IllegalStateException(
                        "Cannot recover saved leaf overlays in " + key(chunk), ex);
            }
        }
        migrateLegacyOverlays(chunk, c);
        if (c.dirty) flush(chunk, c);
        else
            chunk.getPersistentDataContainer()
                    .set(legacyCleanupKey, PersistentDataType.LONG, journalHash(bytes));
    }

    private static long journalHash(byte[] bytes) {
        CRC32 checksum = new CRC32();
        checksum.update(bytes);
        return checksum.getValue();
    }

    private void migrateLegacyOverlays(Chunk chunk, Canopy c) {
        for (int position : new ArrayList<>(c.legacyOverlays.keySet())) {
            int i = Arrays.binarySearch(c.positions, position);
            if (i >= 0) clearLegacyOverlay(chunk, c, i);
        }
    }

    private void clearLegacyOverlay(Chunk chunk, Canopy c, int i) {
        Material material = c.legacyOverlays.remove(c.positions[i]);
        if (material == null) return;
        Block block = block(chunk, c, i);
        // Remove only the old plugin-owned placeholder; preserve a replacement build.
        if (block.getType() == material) block.setType(Material.AIR, true);
        c.flags[i] &= ~LEGACY_OVERLAY_FLAG;
        if (block.getType() == c.data(i).getMaterial()
                && block.getBlockData() instanceof Leaves leaf
                && !leaf.isPersistent()) c.flags[i] &= ~REMOVED;
        else c.flags[i] |= REMOVED;
        c.dirty = true;
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onSeasonalFade(BlockFadeEvent event) {
        Material material = event.getBlock().getType();
        if (enabled
                && event.getBlock().getWorld().getEnvironment() == World.Environment.NORMAL
                && (material == Material.SNOW || material == Material.SNOW_BLOCK)) {
            // Cold: never melt. Warm: layers use the indexed, elevation-aware thaw rate.
            if (snow.snowy(event.getBlock().getBiome())
                    || (!snow.thawing && (coldHalf() || material == Material.SNOW)))
                event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onSeasonalForm(BlockFormEvent event) {
        if (enabled
                && Weather.tridentRainActive(event.getBlock().getWorld())
                && !(event instanceof EntityBlockFormEvent)
                && event.getNewState().getType() == Material.SNOW) {
            event.setCancelled(true);
            return;
        }
        if (enabled
                && (snow.coldFor(key(event.getBlock().getChunk()))
                        || event.getBlock().getY() >= SnowSeasons.WARM_SNOW_MIN_Y)
                && !snow.formingSnow
                && !(event instanceof EntityBlockFormEvent)
                && event.getNewState().getType() == Material.SNOW
                && event.getBlock().getWorld().getEnvironment() == World.Environment.NORMAL
                && !snow.snowy(event.getBlock().getBiome())) {
            event.setCancelled(true); // Non-snowy biomes use our elevation-dependent roll.
        }
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSnowFormObserved(BlockFormEvent event) {
        // Reconcile on the next snow-work pass, after the event's block change is applied.
        if (!snow.formingSnow) snow.disown(event.getBlock());
        if (event.getNewState().getType() == Material.SNOW) snow.expectSnow(event.getBlock());
        else snow.changed(event.getBlock());
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onSnowFadeObserved(BlockFadeEvent event) {
        rememberLeafOverlay(event.getBlock());
        if (!snow.thawing) snow.disown(event.getBlock());
        snow.changed(event.getBlock());
    }

    @EventHandler
    public void onSnowPlayerQuit(PlayerQuitEvent event) {
        snow.sessions.remove(event.getPlayer().getUniqueId());
    }

    private final class SnowSeasons {
        private static final int OWNED_SNOW_MAGIC = 0x53534f31;
        private final Set<Key> ownedChunks = new LinkedHashSet<>();
        private final Map<Key, Set<Long>> ownedCache = new HashMap<>();
        private NamespacedKey ownedSnowKey;

        private Set<Long> owned(Chunk chunk) {
            Key key = key(chunk);
            return ownedCache.computeIfAbsent(
                    key,
                    ignored -> {
                        Set<Long> positions = new HashSet<>();
                        long[] saved =
                                chunk.getPersistentDataContainer()
                                        .get(ownedSnowKey, PersistentDataType.LONG_ARRAY);
                        if (saved != null) for (long position : saved) positions.add(position);
                        return positions;
                    });
        }

        private void saveOwned(Chunk chunk, Set<Long> positions) {
            if (positions.isEmpty()) chunk.getPersistentDataContainer().remove(ownedSnowKey);
            else
                chunk.getPersistentDataContainer()
                        .set(
                                ownedSnowKey,
                                PersistentDataType.LONG_ARRAY,
                                positions.stream().mapToLong(Long::longValue).toArray());
        }

        private void rememberPlaced(Block block) {
            Chunk chunk = block.getChunk();
            Key key = key(chunk);
            if (ownedChunks.add(key)) saveBlocking();
            Set<Long> positions = owned(chunk);
            positions.add(pack(block.getX(), block.getY(), block.getZ()));
            saveOwned(chunk, positions);
        }

        private void disown(Block block) {
            Chunk chunk = block.getChunk();
            if (!ownedChunks.contains(key(chunk))) return;
            Set<Long> positions = owned(chunk);
            if (positions.remove(pack(block.getX(), block.getY(), block.getZ())))
                saveOwned(chunk, positions);
        }

        private int[] cleanupOwned() {
            int removed = 0, unavailable = 0, retained = 0;
            Set<Key> tickets = new HashSet<>();
            try {
                for (Key key : new ArrayList<>(ownedChunks)) {
                    World world = Bukkit.getWorld(key.world);
                    if (world == null) {
                        unavailable++;
                        continue;
                    }
                    try {
                        Chunk chunk = world.getChunkAt(key.x, key.z);
                        if (plugin.isEnabled() && chunk.addPluginChunkTicket(plugin))
                            tickets.add(key);
                        Set<Long> positions = owned(chunk);
                        for (long position : new ArrayList<>(positions)) {
                            Block block = world.getBlockAt(x(position), y(position), z(position));
                            // A layer changed by a player or another plugin is no longer ours.
                            if (block.getBlockData() instanceof Snow layer
                                    && layer.getLayers() == 1) {
                                org.bukkit.block.BlockState replacement = block.getState();
                                replacement.setType(Material.AIR);
                                BlockFadeEvent event = new BlockFadeEvent(block, replacement);
                                thawing = true;
                                try {
                                    Bukkit.getPluginManager().callEvent(event);
                                } finally {
                                    thawing = false;
                                }
                                if (event.isCancelled()
                                        || event.getNewState().getType() != Material.AIR) {
                                    retained++;
                                    continue;
                                }
                                block.setType(Material.AIR, true);
                                removed++;
                            }
                            positions.remove(position);
                        }
                        saveOwned(chunk, positions);
                        if (positions.isEmpty()) {
                            ownedChunks.remove(key);
                            ownedCache.remove(key);
                        }
                    } catch (RuntimeException ex) {
                        unavailable++;
                        plugin.getLogger()
                                .log(Level.WARNING, "Unable to clean owned snow in " + key, ex);
                    }
                }
            } finally {
                for (Key key : tickets) {
                    World world = Bukkit.getWorld(key.world);
                    if (world != null && world.isChunkLoaded(key.x, key.z))
                        world.getChunkAt(key.x, key.z).removePluginChunkTicket(plugin);
                }
            }
            return new int[] {removed, unavailable, retained};
        }

        private static final int MELT_LOW_Y = 90, SNOW_HIGH_Y = 130, WARM_SNOW_MIN_Y = 126;
        private static final int SNOW_LINE_MAX_Y = 95;
        private static final double COVERAGE_REFERENCE = 0.75;
        private static final double MELT_FRACTION_PER_SECOND = 0.05;
        private static final double MELT_MAX_LAYERS_PER_SECOND = 400.0;
        private static final int MELT_MAX_CHANGES_PER_TICK = 20;
        private static final int SNOW_PROFILE_MAGIC = 0x53535031;
        private volatile SnowProfile snowProfile;
        private final Map<UUID, Integer> seaLevels = new ConcurrentHashMap<>();

        // Immutable and persisted: one draw each fall, shared by live snow and chunk estimates.
        private record SnowProfile(
                long winter, double minProbability, double maxProbability, double rateScale) {}

        private void ensureSnowProfile() {
            long winter = winterId();
            if (snowProfile != null && snowProfile.winter == winter) return;
            SplittableRandom random = new SplittableRandom(mix(winter ^ 0x536e6f7750726f66L));
            // About 70-80% high-altitude coverage after the initial 150-second storm.
            // Four falls in five have minimal coverage at the snow line; one in five is snowier.
            double maximum = random.nextDouble(0.33, 0.38);
            double ratio =
                    random.nextDouble(0.08, 0.2);
            snowProfile =
                    new SnowProfile(
                            winter, maximum * ratio, maximum, random.nextDouble(0.95, 1.05));
        }

        private int seaLevel(Key key) {
            return seaLevels.getOrDefault(key.world, 63);
        }

        private int coldSnowLine(Key key) {
            SnowProfile profile = snowProfile;
            return snowLine(profile == null ? winterId() : profile.winter, seaLevel(key));
        }

        private static int snowLine(long winter, int sea) {
            // A separate random draw keeps the snow line independent of snowfall intensity.
            // The persisted winter id also makes the line stable across unloads and restarts.
            double draw = (mix(winter ^ 0x536e6f774c696e65L) >>> 11) * 0x1.0p-53;
            return sea + (int) (draw * (Math.max(sea - 20, SNOW_LINE_MAX_Y) - sea + 1));
        }

        private static double coverageProbability(
                int y, int floor, double min, double max, double scale) {
            if (y < floor) return 0.0;
            double height =
                    Math.max(
                            0.0,
                            Math.min(1.0, (y - floor) / (double) Math.max(1, SNOW_HIGH_Y - floor)));
            // At the instant the upper endpoint reaches 75% coverage, coverage at every
            // intermediate height is linear. Interpolate coverage, then invert saturation.
            double exposure = -Math.log1p(-COVERAGE_REFERENCE) / max;
            double lowCoverage = -Math.expm1(-exposure * min);
            double coverage = lowCoverage + (COVERAGE_REFERENCE - lowCoverage) * height;
            return -Math.log1p(-coverage) / exposure * scale;
        }

        private static final double WARM_ACCUMULATION_MULTIPLIER = 0.5;
        // Layers per real second per active chunk; fractional rates are supported.
        private static final double MELT_RATE_LOW = 10.8, MELT_RATE_HIGH = 1.2;
        private static final double MELT_RATE_MULTIPLIER = 1.0;
        private static final int CLUMP_EXTRA_MIN = 2, CLUMP_EXTRA_MAX = 10, CLUMP_MAX_STEP = 2;
        private static final int CHUNKS_PER_TICK = 32,
                REFRESHES_PER_TICK = 2,
                SNOW_CHANGES_PER_TICK = 128;
        private static final int SURFACE_COLUMNS_PER_TICK = 32;
        private static final long STORM_DURATION_MILLIS = 60_000L;
        private static final long SNOW_ACCUMULATION_MILLIS = 150_000L; // 2 minutes 30 seconds.
        private static final long DEPOSITION_INTERVAL_NANOS = 1_000_000_000L;
        private static final long SAMPLE_BUDGET_NANOS = 1_500_000L;
        // Quantiles of four-block smooth noise, calibrated once offline. They convert desired
        // coverage into a threshold without repeating a calibration or simulation per chunk.
        private static final double[] PRELOAD_COVERAGE_LEVELS = {
            0, 0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65,
            0.7, 0.75, 0.8, 0.85, 0.9, 0.95, 0.98, 0.99, 1
        };
        private static final double[] PRELOAD_NOISE_QUANTILES = {
            0.0,
            0.0654427,
            0.09624959,
            0.15022501,
            0.20833969,
            0.25568655,
            0.29807239,
            0.33692625,
            0.37325847,
            0.40729021,
            0.43948244,
            0.4703065,
            0.5003083,
            0.53022531,
            0.56116724,
            0.59355235,
            0.62755501,
            0.66369187,
            0.70251048,
            0.74451192,
            0.7919221,
            0.84956197,
            0.90338952,
            0.9340577,
            1.0
        };

        private static final int SNOW_STATE_MAGIC = 0x53534e32;
        private final Set<Biome> vanillaSnowy =
                EnumSet.of(
                        Biome.SNOWY_PLAINS,
                        Biome.ICE_SPIKES,
                        Biome.SNOWY_TAIGA,
                        Biome.GROVE,
                        Biome.SNOWY_SLOPES,
                        Biome.FROZEN_PEAKS,
                        Biome.JAGGED_PEAKS,
                        Biome.FROZEN_RIVER,
                        Biome.FROZEN_OCEAN,
                        Biome.DEEP_FROZEN_OCEAN);
        private final Set<String> snowyNames = ConcurrentHashMap.newKeySet();
        private final Set<Key> allowed = ConcurrentHashMap.newKeySet();
        private final Map<UUID, BiomeSession> sessions = new ConcurrentHashMap<>();
        private final Map<Key, SnowChunk> active = new HashMap<>();
        private final Set<Key> pendingPreloads = ConcurrentHashMap.newKeySet();
        private final ArrayDeque<SnowCapture> captures = new ArrayDeque<>();
        private long preloadSerial;
        private final ArrayDeque<Key> preloadQueue = new ArrayDeque<>();
        private final ArrayDeque<SnowPreload> readyPreloads = new ArrayDeque<>();
        private ExecutorService preloadWorker;
        private int preloadsInFlight;
        private final List<SnowChunk> meltCandidates = new ArrayList<>();
        private long lastMelt = System.nanoTime();
        private double meltSeconds;
        private MeltTarget pendingMelt;
        private final ArrayDeque<Key> surveyQueue = new ArrayDeque<>();
        private SnowChunk surveying;
        private SnowSurvey installingSurvey;
        private long surveySerial, lastAccumulationYear = -1;
        private volatile long lateFallUntilMillis;
        private final ArrayDeque<Key> samples = new ArrayDeque<>(), refreshes = new ArrayDeque<>();
        private final Set<Key> queuedRefreshes = new HashSet<>();
        private ProtocolManager manager;
        private PacketAdapter listener;
        private boolean lastCold, formingSnow;
        private volatile boolean warned;
        private long formed, melted;

        private void register() {
            if (!Bukkit.getPluginManager().isPluginEnabled("ProtocolLib"))
                throw new IllegalStateException(
                        "Seasonal snowfall requires ProtocolLib. Keep depend: [ProtocolLib] in"
                                + " plugin.yml.");
            coverageKey = new NamespacedKey(plugin, "season_snow_coverage_v1");
            ownedSnowKey = new NamespacedKey(plugin, "season_owned_snow_v1");
            preloadWorker =
                    Executors.newSingleThreadExecutor(
                            r -> {
                                Thread thread = new Thread(r, plugin.getName() + "-snow-preload");
                                thread.setDaemon(true);
                                return thread;
                            });
            manager = ProtocolLibrary.getProtocolManager();
            listener =
                    new PacketAdapter(
                            plugin,
                            ListenerPriority.HIGH,
                            PacketType.Play.Server.LOGIN,
                            PacketType.Play.Server.MAP_CHUNK) {
                        @Override
                        public void onPacketSending(PacketEvent event) {
                            try {
                                if (event.getPacketType() == PacketType.Play.Server.LOGIN)
                                    registerBiomes(event);
                                else rewriteChunk(event);
                            } catch (IOException | RuntimeException ex) {
                                // Never send a chunk encoded against a different registry after a
                                // codec failure.
                                event.setCancelled(true);
                                if (!warned) {
                                    warned = true;
                                    plugin.getLogger()
                                            .log(
                                                    Level.SEVERE,
                                                    "Cannot encode seasonal snow biomes; affected"
                                                            + " packet was withheld.",
                                                    ex);
                                }
                                onMain(
                                        () -> {
                                            Player player = event.getPlayer();
                                            if (player.isOnline())
                                                player.kickPlayer(
                                                        "Seasonal biome data could not be sent."
                                                            + " Please reconnect; the server log"
                                                            + " has details.");
                                        });
                            }
                        }
                    };
            manager.addPacketListener(listener);
            for (World world : Bukkit.getWorlds())
                seaLevels.put(world.getUID(), world.getSeaLevel());
            lastCold = enabled && coldHalf();
            if (!Bukkit.getOnlinePlayers().isEmpty())
                plugin.getLogger()
                        .info(
                                "Players already connected must reconnect to receive seasonal snow"
                                        + " biomes.");
        }

        private void registerBiomes(PacketEvent event) throws IOException {
            // 1.18.2 stores RegistryAccess, not an NBT field, in the login packet.
            // Work through its wire codec to create an isolated, client-only registry.
            byte[] wire = packetBytes(event.getPacket());
            ByteArrayInputStream bytes = new ByteArrayInputStream(wire);
            DataInputStream in = new DataInputStream(bytes);
            in.skipNBytes(7); // Entity id, hardcore, current and previous game modes.
            int dimensions = readVarInt(in);
            if (dimensions < 0 || dimensions > 1024)
                throw new IOException("Invalid dimension count");
            for (int i = 0; i < dimensions; i++) {
                int size = readVarInt(in);
                if (size < 0 || size > 32767) throw new IOException("Invalid dimension name");
                in.skipNBytes(size);
            }
            int prefix = wire.length - bytes.available();
            NbtCompound registry = NbtBinarySerializer.DEFAULT.deserializeCompound(in);
            byte[] tail = in.readAllBytes();
            if (!registry.containsKey("minecraft:worldgen/biome"))
                throw new IOException("Missing login biome registry (Paper 1.18.2 required)");
            NbtList<Map<String, NbtBase<?>>> values =
                    registry.getCompound("minecraft:worldgen/biome").getList("value");
            List<NbtCompound> original = new ArrayList<>();
            int nextId = 0;
            Set<String> names = new HashSet<>();
            for (NbtBase<Map<String, NbtBase<?>>> value : values.asCollection()) {
                NbtCompound entry = (NbtCompound) value;
                original.add(entry);
                names.add(entry.getString("name"));
                nextId = Math.max(nextId, entry.getInteger("id") + 1);
            }
            int[] snowIds = new int[nextId], rainIds = new int[nextId];
            for (int i = 0; i < nextId; i++) snowIds[i] = i;
            for (NbtCompound entry : original) {
                NbtCompound climate = entry.getCompound("element");
                String name = entry.getString("name");
                if ("snow".equals(climate.getString("precipitation"))
                        || climate.getFloat("temperature") < 0.15f) {
                    snowyNames.add(name);
                    continue;
                }
                NbtCompound copy = (NbtCompound) entry.deepClone();
                copy.setName(""); // NBT list elements must be unnamed; deepClone may use null.
                String newName = "seasons:snow_" + name.replace(':', '_');
                while (names.contains(newName)) newName += "_";
                names.add(newName);
                copy.put("name", newName).put("id", nextId);
                NbtCompound element = copy.getCompound("element"),
                        effects = element.getCompound("effects");
                double temperature = Math.max(0, Math.min(1, climate.getFloat("temperature")));
                double humidity = Math.max(0, Math.min(1, climate.getFloat("downfall")));
                // Preserve the ordinary biome's grass/foliage tint despite the client-only cold
                // temperature.
                if (!effects.containsKey("grass_color"))
                    effects.put("grass_color", SnowColors.color(true, temperature, humidity));
                if (!effects.containsKey("foliage_color"))
                    effects.put("foliage_color", SnowColors.color(false, temperature, humidity));
                element.put("precipitation", "snow").put("temperature", -0.5f);
                element.remove("temperature_modifier");
                snowIds[entry.getInteger("id")] = nextId++;
                values.add(copy);
            }
            for (NbtCompound entry : original) {
                NbtCompound climate = entry.getCompound("element");
                NbtCompound copy = (NbtCompound) entry.deepClone();
                copy.setName("");
                String newName = "seasons:rain_" + entry.getString("name").replace(':', '_');
                while (names.contains(newName)) newName += "_";
                names.add(newName);
                copy.put("name", newName).put("id", nextId);
                NbtCompound element = copy.getCompound("element"),
                        effects = element.getCompound("effects");
                double temperature = Math.max(0, Math.min(1, climate.getFloat("temperature")));
                double humidity = Math.max(0, Math.min(1, climate.getFloat("downfall")));
                if (!effects.containsKey("grass_color"))
                    effects.put("grass_color", SnowColors.color(true, temperature, humidity));
                if (!effects.containsKey("foliage_color"))
                    effects.put("foliage_color", SnowColors.color(false, temperature, humidity));
                element.put("precipitation", "rain").put("temperature", 2.0f);
                element.remove("temperature_modifier");
                rainIds[entry.getInteger("id")] = nextId++;
                values.add(copy);
            }
            ByteArrayOutputStream encoded = new ByteArrayOutputStream(wire.length + 32768);
            DataOutputStream out = new DataOutputStream(encoded);
            out.write(wire, 0, prefix);
            NbtBinarySerializer.DEFAULT.serialize(registry, out);
            out.write(tail);
            PacketContainer packet =
                    packetFromBytes(PacketType.Play.Server.LOGIN, encoded.toByteArray());
            event.setPacket(packet);
            sessions.put(
                    event.getPlayer().getUniqueId(),
                    new BiomeSession(snowIds, rainIds, Math.max(4, bitsFor(nextId))));
        }

        private void rewriteChunk(PacketEvent event) throws IOException {

            BiomeSession session = sessions.get(event.getPlayer().getUniqueId());
            if (session == null) return; // No custom registry was sent to this existing connection.
            World world = event.getPlayer().getWorld();
            PacketContainer original = event.getPacket();
            int cx = original.getIntegers().read(0), cz = original.getIntegers().read(1);
            Key key = new Key(world.getUID(), cx, cz);
            int minimumY =
                    enabled
                                    && world.getEnvironment() == World.Environment.NORMAL
                                    && allowed.contains(key)
                            ? minimumSnowY(key)
                            : Integer.MAX_VALUE;
            WrappedLevelChunkData.ChunkData data = original.getLevelChunkData().read(0);
            byte[] rewritten =
                    rewriteBiomes(
                            data.getBuffer(),
                            world.getMinHeight(),
                            (world.getMaxHeight() - world.getMinHeight()) / 16,
                            session,
                            minimumY,
                            tridentRainApplies(world));
            if (rewritten == null) return;
            // Chunk packets may be shared by players; isolate the mutable data wrapper as well.
            PacketContainer packet = original.deepClone();
            packet.getLevelChunkData().read(0).setBuffer(rewritten);
            event.setPacket(packet);
        }

        private static final int FULL_STORM = 1, PARTIAL_STORM = 2, PRELOADED = 4;
        private NamespacedKey coverageKey;
        private Season lastSeason;

        private long winterId() {
            // The ground seed is persisted and renewed by /season enable. Include the year so
            // reloading chunks or restarting the server cannot grant a second load this winter.
            return mix(
                    ground.seed
                            ^ (elapsed / (4 * SEASON_TICKS)) * 0x9e3779b97f4a7c15L
                            ^ 0x57696e746572536eL);
        }

        private void readCoverage(SnowChunk state) {
            long winter = winterId();
            if (state.coverageWinter == winter) return;
            World world = Bukkit.getWorld(state.key.world);
            if (world == null || !world.isChunkLoaded(state.key.x, state.key.z)) return;
            long[] record =
                    world.getChunkAt(state.key.x, state.key.z)
                            .getPersistentDataContainer()
                            .get(coverageKey, PersistentDataType.LONG_ARRAY);
            state.coverageWinter = winter;
            state.coverageFlags =
                    record != null && record.length == 2 && record[0] == winter
                            ? (int) record[1] & (FULL_STORM | PARTIAL_STORM | PRELOADED)
                            : 0;
        }

        private void writeCoverage(SnowChunk state) {
            World world = Bukkit.getWorld(state.key.world);
            if (world != null && world.isChunkLoaded(state.key.x, state.key.z))
                world.getChunkAt(state.key.x, state.key.z)
                        .getPersistentDataContainer()
                        .set(
                                coverageKey,
                                PersistentDataType.LONG_ARRAY,
                                new long[] {state.coverageWinter, state.coverageFlags});
        }

        private boolean initialStormActive() {
            return System.currentTimeMillis() < lateFallUntilMillis
                    && lastAccumulationYear == elapsed / (4 * SEASON_TICKS);
        }

        private void observeStorm(SnowChunk state, boolean atStart) {
            if (!initialStormActive() || state.stormEnd == lateFallUntilMillis) return;
            readCoverage(state);
            state.stormEnd = lateFallUntilMillis;
            state.fullStormCandidate =
                    atStart
                            && state.admitted
                            && !state.preloading
                            && !Weather.tridentRainActive(Bukkit.getWorld(state.key.world));
            // Partial is durable immediately. An unload or restart before the deadline must
            // never be mistaken for uninterrupted coverage of the entire storm.
            state.coverageFlags |= PARTIAL_STORM;
            writeCoverage(state);
        }

        private void completeStormCoverage(SnowChunk state, long ended) {
            if (state.stormEnd != ended || state.coverageWinter != winterId()) return;
            if (state.fullStormCandidate) {
                state.coverageFlags = (state.coverageFlags & ~PARTIAL_STORM) | FULL_STORM;
                writeCoverage(state);
            }
            state.fullStormCandidate = false;
            state.stormEnd = 0;
        }

        private void finishAccumulation(long ended) {
            for (SnowChunk state : active.values()) completeStormCoverage(state, ended);
            lateFallUntilMillis = 0;
            calendarChanged();
            if (enabled && season() == Season.WINTER)
                for (SnowChunk state : active.values()) requestPreload(state);
            if (enabled) saveAsync(null);
        }

        private void prepareLoaded(boolean winterPreload) {
            if (season() != Season.WINTER
                    || active.values().stream()
                            .anyMatch(
                                    state ->
                                            state.preloading && state.coverageWinter != winterId()))
                cancelPreloads();
            for (World world : Bukkit.getWorlds()) {
                if (world.getEnvironment() != World.Environment.NORMAL) continue;
                for (Chunk chunk : world.getLoadedChunks()) {
                    SnowChunk state = ensureLoaded(chunk);
                    observeStorm(state, false);
                    if (winterPreload && season() == Season.WINTER) requestPreload(state);
                }
            }
        }

        private SnowChunk ensureLoaded(Chunk chunk) {
            seaLevels.put(chunk.getWorld().getUID(), chunk.getWorld().getSeaLevel());
            Key key = key(chunk);
            SnowChunk state = active.get(key);
            if (state == null) {
                state = new SnowChunk(key);
                state.admissionTick = ticks + 2;
                active.put(key, state);
                samples.addLast(key);
                if (nearPlayer(key)) surveyQueue.addFirst(key);
                else surveyQueue.addLast(key);
            }
            readCoverage(state);
            admitSnow(state);
            return state;
        }

        private boolean admitSnow(SnowChunk state) {
            if (state.admitted) return true;
            // Let the normal chunk load and terrain packet happen before any snow calculations.
            if (ticks < state.admissionTick) return false;
            if (admissions.deferred.containsKey(state.key)) {
                if (!admissions.ready(state.key)) return false;
            } else if (admissions.interestedPlayer(state.key) != null
                    && !admissions.ready(state.key)) return false;
            state.admitted = true;
            if (allowed.add(state.key)) queueRefresh(state.key);
            return true;
        }

        private void noteLoaded(Chunk chunk) {
            if (!enabled || chunk.getWorld().getEnvironment() != World.Environment.NORMAL) return;
            SnowChunk state = ensureLoaded(chunk);
            observeStorm(state, false);
            if (season() == Season.WINTER) requestPreload(state);
        }

        private void requestPreload(SnowChunk state) {
            if (!enabled || season() != Season.WINTER || initialStormActive()) return;
            readCoverage(state);
            if (state.preloading || (state.coverageFlags & (FULL_STORM | PRELOADED)) != 0) return;
            state.preloading = true;
            pendingPreloads.add(state.key);
            if (!state.ready) {
                surveyQueue.remove(state.key);
                surveyQueue.addFirst(state.key);
            }
            if (nearPlayer(state.key)) preloadQueue.addFirst(state.key);
            else preloadQueue.addLast(state.key);
        }

        private void discover(Chunk chunk) {
            if (!enabled || chunk.getWorld().getEnvironment() != World.Environment.NORMAL) return;
            ensureLoaded(chunk);
        }

        private boolean accumulating(Key key, long nowNanos, long nowMillis) {
            return nowMillis < lateFallUntilMillis || pendingPreloads.contains(key);
        }

        private boolean coldFor(Key key) {
            return coldHalf() || accumulating(key, System.nanoTime(), System.currentTimeMillis());
        }

        private int minimumSnowY(Key key) {
            return coldFor(key) ? coldSnowLine(key) : WARM_SNOW_MIN_Y;
        }

        private double accumulationChance(Key key, int y) {
            if (y < minimumSnowY(key)) return 0.0;
            return coldAccumulationChance(key, y)
                    * (coldFor(key) ? 1.0 : WARM_ACCUMULATION_MULTIPLIER);
        }

        private double coldAccumulationChance(Key key, int y) {
            SnowProfile profile = snowProfile;
            return profile == null
                    ? coverageProbability(y, coldSnowLine(key), 0.004, 0.335, 1.0)
                    : coverageProbability(
                            y,
                            coldSnowLine(key),
                            profile.minProbability,
                            profile.maxProbability,
                            profile.rateScale);
        }

        private void resetAdmissions() {
            for (Key key : allowed) queueRefresh(key);
            allowed.clear();
            active.clear();
            samples.clear();
            surveyQueue.clear();
            preloadQueue.clear();
            readyPreloads.clear();
            pendingPreloads.clear();
            captures.clear();
            preloadSerial++;

            lateFallUntilMillis = 0;
            lastAccumulationYear = -1;
            surveySerial++;
            installingSurvey = null;
            pendingMelt = null;
            meltSeconds = 0;
            lastMelt = System.nanoTime();
        }

        private void unload(Key key) {
            ownedCache.remove(key);
            SnowChunk leaving = active.get(key);
            if (leaving != null
                    && leaving.stormEnd != 0
                    && System.currentTimeMillis() >= leaving.stormEnd)
                completeStormCoverage(leaving, leaving.stormEnd);
            active.remove(key);
            allowed.remove(key);
            samples.remove(key);
            surveyQueue.remove(key);
            queuedRefreshes.remove(key);
            preloadQueue.remove(key);
            pendingPreloads.remove(key);
            captures.removeIf(capture -> capture.state.key.equals(key));
            readyPreloads.removeIf(plan -> plan.state.key.equals(key));
            if (pendingMelt != null && pendingMelt.state.key.equals(key)) pendingMelt = null;
        }

        private void cancelPreloads() {
            preloadSerial++;
            for (SnowChunk state : active.values()) state.preloading = false;
            pendingPreloads.clear();
            preloadQueue.clear();
            captures.clear();
            readyPreloads.clear();
        }

        private boolean validPreload(SnowChunk state, long winter) {
            World world = Bukkit.getWorld(state.key.world);
            return enabled
                    && season() == Season.WINTER
                    && state.preloading
                    && active.get(state.key) == state
                    && state.coverageWinter == winter
                    && winter == winterId()
                    && world != null
                    && world.isChunkLoaded(state.key.x, state.key.z);
        }

        private void startPreload() {
            if (season() != Season.WINTER
                    || initialStormActive()
                    || captures.size() + preloadsInFlight >= 2) return;
            ensureSnowProfile();
            for (Player player : Bukkit.getOnlinePlayers()) {
                Location location = player.getLocation();
                Key occupied =
                        new Key(
                                location.getWorld().getUID(),
                                location.getBlockX() >> 4,
                                location.getBlockZ() >> 4);
                if (preloadQueue.remove(occupied)) preloadQueue.addFirst(occupied);
            }
            int tries = Math.min(32, preloadQueue.size());
            while (tries-- > 0 && !preloadQueue.isEmpty()) {
                Key key = preloadQueue.removeFirst();
                SnowChunk state = active.get(key);
                if (state == null || !validPreload(state, state.coverageWinter)) continue;
                if (Weather.tridentRainActive(Bukkit.getWorld(key.world))
                        || !admitSnow(state)
                        || !leavesReadyForSnow(key)
                        || !state.ready) {
                    preloadQueue.addLast(key);
                    continue;
                }
                captures.addLast(
                        new SnowCapture(
                                state,
                                state.coverageWinter,
                                new ArrayList<>(state.snow.positions)));
                return;
            }
        }

        private void advanceCapture(long until, int[] changes) {
            int rounds = captures.size(), columns = SURFACE_COLUMNS_PER_TICK;
            while (rounds-- > 0 && !captures.isEmpty() && System.nanoTime() < until) {
                SnowCapture capture = captures.removeFirst();
                SnowChunk state = capture.state;
                if (!validPreload(state, capture.winter)) continue;
                if (Weather.tridentRainActive(Bukkit.getWorld(state.key.world))
                        || !leavesReadyForSnow(state.key)) {
                    captures.addLast(capture);
                    continue;
                }
                World world = Bukkit.getWorld(state.key.world);
                Snow data = (Snow) Material.SNOW.createBlockData();
                data.setLayers(1);
                while (capture.cursor < 256 && columns > 0 && System.nanoTime() < until) {
                    columns--;
                    int i = capture.cursor++;
                    Block top =
                            world.getHighestBlockAt(
                                    (state.key.x << 4) + (i & 15),
                                    (state.key.z << 4) + (i >> 4),
                                    HeightMap.WORLD_SURFACE);
                    // Calculate against the post-clear surface without changing the world.
                    // The old snow remains visible until the complete replacement is ready.
                    boolean replacing = top.getType() == Material.SNOW && !snowy(top.getBiome());
                    if (top.getY() + (replacing ? 0 : 1) >= world.getMaxHeight()) continue;
                    Block place = replacing ? top : top.getRelative(0, 1, 0);
                    if (replacing)
                        capture.surface.clear.add(pack(top.getX(), top.getY(), top.getZ()));
                    capture.surface.y[i] = place.getY();
                    capture.surface.threshold[i] = preloadThreshold(state.key, place.getY());
                    capture.surface.eligible[i] =
                            place.getY() >= coldSnowLine(state.key)
                                    && !snowy(place.getBiome())
                                    && (place.getType().isAir() || replacing)
                                    && place.getLightFromBlocks() < 10
                                    && place.canPlace(data);
                }
                if (capture.cursor < 256) {
                    captures.addLast(capture);
                    continue;
                }
                long serial = preloadSerial;
                long seed =
                        mix(
                                capture.winter
                                        ^ state.key.world.getMostSignificantBits()
                                        ^ Long.rotateLeft(
                                                state.key.world.getLeastSignificantBits(), 32));
                preloadsInFlight++;
                preloadWorker.execute(
                        () -> {
                            boolean[] plan =
                                    estimatePreload(
                                            capture.surface,
                                            state.key.x << 4,
                                            state.key.z << 4,
                                            seed);
                            onMain(
                                    () -> {
                                        preloadsInFlight--;
                                        if (serial == preloadSerial
                                                && validPreload(state, capture.winter))
                                            readyPreloads.addLast(
                                                    new SnowPreload(
                                                            state,
                                                            capture.winter,
                                                            capture.surface,
                                                            plan));
                                    });
                        });
            }
        }

        private boolean clearSnowForPreload(Block block) {
            rememberLeafOverlay(block);
            org.bukkit.block.BlockState replacement = block.getState();
            replacement.setType(Material.AIR);
            BlockFadeEvent event = new BlockFadeEvent(block, replacement);
            thawing = true;
            try {
                Bukkit.getPluginManager().callEvent(event);
            } finally {
                thawing = false;
            }
            if (event.isCancelled() || event.getNewState().getType() != Material.AIR) return false;
            block.setType(Material.AIR, true);
            forget(block);
            return true;
        }

        private static final class SnowCapture {
            final SnowChunk state;
            final long winter;
            final SnowSurface surface = new SnowSurface();
            int cursor;

            SnowCapture(SnowChunk state, long winter, List<Long> clear) {
                this.state = state;
                this.winter = winter;
                surface.clear.addAll(clear);
            }
        }

        private double preloadThreshold(Key key, int y) {
            return coverageThreshold(expectedCoverage(coldAccumulationChance(key, y)));
        }

        private static double expectedCoverage(double probability) {
            double events = SNOW_ACCUMULATION_MILLIS * 1_000_000.0 / DEPOSITION_INTERVAL_NANOS;
            double footprint = 1.0 + (CLUMP_EXTRA_MIN + CLUMP_EXTRA_MAX) * 0.5;
            return -Math.expm1(-events * footprint * probability / 256.0);
        }

        private static double coverageThreshold(double coverage) {
            coverage = Math.max(0, Math.min(1, coverage));
            int upper = Arrays.binarySearch(PRELOAD_COVERAGE_LEVELS, coverage);
            if (upper >= 0) return PRELOAD_NOISE_QUANTILES[upper];
            upper = -upper - 1;
            int lower = upper - 1;
            double fraction =
                    (coverage - PRELOAD_COVERAGE_LEVELS[lower])
                            / (PRELOAD_COVERAGE_LEVELS[upper] - PRELOAD_COVERAGE_LEVELS[lower]);
            return PRELOAD_NOISE_QUANTILES[lower]
                    + fraction * (PRELOAD_NOISE_QUANTILES[upper] - PRELOAD_NOISE_QUANTILES[lower]);
        }

        private static boolean[] estimatePreload(
                SnowSurface surface, int originX, int originZ, long seed) {
            boolean[] placed = new boolean[256];
            for (int i = 0; i < placed.length; i++)
                placed[i] =
                        surface.eligible[i]
                                && snowPatchNoise(originX + (i & 15), originZ + (i >> 4), seed)
                                        < surface.threshold[i];
            return placed;
        }

        private static double snowPatchNoise(int x, int z, long seed) {
            // Four-block patches share lattice corners across chunk boundaries, including at
            // negative coordinates. Only the winter/world seed changes the random field.
            int gx = x >> 2, gz = z >> 2;
            double tx = (x & 3) * 0.25, tz = (z & 3) * 0.25;
            tx = tx * tx * (3 - 2 * tx);
            tz = tz * tz * (3 - 2 * tz);
            double a = snowPatchCorner(gx, gz, seed), b = snowPatchCorner(gx + 1, gz, seed);
            double c = snowPatchCorner(gx, gz + 1, seed), d = snowPatchCorner(gx + 1, gz + 1, seed);
            double top = a + (b - a) * tx, bottom = c + (d - c) * tx;
            return top + (bottom - top) * tz;
        }

        private static double snowPatchCorner(int x, int z, long seed) {
            return (mix(seed ^ (long) x * 0x9e3779b97f4a7c15L ^ (long) z * 0xc2b2ae3d27d4eb4fL)
                            >>> 11)
                    * 0x1.0p-53;
        }

        private void applyPreloads(long until, int[] changes) {
            int rounds = readyPreloads.size();
            while (rounds-- > 0 && !readyPreloads.isEmpty() && System.nanoTime() < until) {
                SnowPreload plan = readyPreloads.removeFirst();
                SnowChunk state = plan.state;
                Key key = state.key;
                World world = Bukkit.getWorld(key.world);
                if (!validPreload(state, plan.winter)) continue;
                if (Weather.tridentRainActive(world)
                        || !admitSnow(state)
                        || !leavesReadyForSnow(key)) {
                    readyPreloads.addLast(plan);
                    continue;
                }
                // Clear and replace together, only after capture, estimation and tree work.
                // Both partial recipients and chunks with no coverage follow this transaction.
                // Never yield between the clear and placement; commit one chunk per tick.
                for (long position : plan.surface.clear) {
                    Block block = world.getBlockAt(x(position), y(position), z(position));
                    if (block.getType() == Material.SNOW
                            && !snowy(block.getBiome())
                            && clearSnowForPreload(block)) changes[0]++;
                }
                for (int i = 0; i < 256; i++) {
                    if (!plan.planned[i]) continue;
                    Block place =
                            world.getBlockAt(
                                    (key.x << 4) + (i & 15),
                                    plan.surface.y[i],
                                    (key.z << 4) + (i >> 4));
                    // Builds, plants, protected positions and naturally snowy biomes still win.
                    if (world.getHighestBlockAt(place.getX(), place.getZ(), HeightMap.WORLD_SURFACE)
                                            .getY()
                                    != place.getY() - 1
                            || snowy(place.getBiome())) continue;
                    if (form(place)) changes[0]++;
                }
                state.coverageFlags |= PRELOADED;
                writeCoverage(state);
                state.preloading = false;
                pendingPreloads.remove(key);
                state.nextDeposit = System.nanoTime() + DEPOSITION_INTERVAL_NANOS;
                queueRefresh(key);
                return;
            }
        }

        private static final class SnowSurface {
            final Set<Long> clear = new HashSet<>();
            final int[] y = new int[256];
            final double[] threshold = new double[256];
            final boolean[] eligible = new boolean[256];
        }

        private static final class SnowPreload {
            final SnowChunk state;
            final long winter;
            final SnowSurface surface;
            final boolean[] planned;

            SnowPreload(SnowChunk state, long winter, SnowSurface surface, boolean[] planned) {
                this.state = state;
                this.winter = winter;
                this.surface = surface;
                this.planned = planned;
            }
        }

        private void queueRefresh(Key key) {
            if (queuedRefreshes.add(key)) {
                if (nearPlayer(key)) refreshes.addFirst(key);
                else refreshes.addLast(key);
            } else if (nearPlayer(key)) {
                refreshes.remove(key);
                refreshes.addFirst(key);
            }
        }

        private void tridentRainChanged(World world, boolean overrideActive) {
            for (SnowChunk state : active.values()) {
                if (!state.key.world.equals(world.getUID())) continue;
                if (overrideActive && state.stormEnd != 0) state.fullStormCandidate = false;
            }
            for (Chunk chunk : world.getLoadedChunks())
                if (nearPlayer(key(chunk))) queueRefresh(key(chunk));
        }

        private void calendarChanged() {
            for (Key key : allowed) queueRefresh(key);
            lastCold = enabled && coldHalf();
        }

        private void startLateFall(long nowMillis) {
            long year = elapsed / (4 * SEASON_TICKS);
            if (season() != Season.FALL
                    || elapsed % SEASON_TICKS < (3 * SEASON_TICKS + 3) / 4
                    || year == lastAccumulationYear) return;
            ensureSnowProfile();
            lastAccumulationYear = year;
            lateFallUntilMillis = nowMillis + SNOW_ACCUMULATION_MILLIS;
            for (World world : Bukkit.getWorlds()) {
                if (world.getEnvironment() != World.Environment.NORMAL) continue;
                if (!Weather.startSeasonalThunder(world, STORM_DURATION_MILLIS)) {
                    world.setStorm(true);
                    world.setThundering(true);
                    world.setWeatherDuration(1200);
                    world.setThunderDuration(1200);
                }
                for (Chunk chunk : world.getLoadedChunks()) observeStorm(ensureLoaded(chunk), true);
            }
            saveAsync(null);
        }

        private void tick() {
            long now = System.nanoTime(), millis = System.currentTimeMillis();
            if (enabled
                    && (season() == Season.FALL || season() == Season.WINTER)
                    && (snowProfile == null || snowProfile.winter != winterId())) {
                ensureSnowProfile();
                saveAsync(null);
            }
            if (enabled) startLateFall(millis);
            if (lateFallUntilMillis != 0 && millis >= lateFallUntilMillis)
                finishAccumulation(lateFallUntilMillis);
            if (enabled && season() != lastSeason) {
                lastSeason = season();
                if (lastSeason == Season.WINTER) prepareLoaded(true);
                else cancelPreloads();
            }
            boolean cold = enabled && coldHalf();
            if (cold != lastCold) calendarChanged();
            for (int i = 0; i < REFRESHES_PER_TICK && !refreshes.isEmpty(); i++) {
                Key key = refreshes.removeFirst();
                if (!queuedRefreshes.remove(key)) continue;
                World world = Bukkit.getWorld(key.world);
                if (world != null && world.isChunkLoaded(key.x, key.z))
                    world.refreshChunk(key.x, key.z);
            }
            if (!enabled) return;
            installSurvey();
            startPreload();
            startSurvey();
            int rounds = Math.min(samples.size(), CHUNKS_PER_TICK);
            int[] changes = {0};
            long until = System.nanoTime() + SAMPLE_BUDGET_NANOS;
            int[] preloadChanges = {0};
            applyPreloads(until, preloadChanges);
            advanceCapture(until, preloadChanges);
            changes[0] += preloadChanges[0];
            while (rounds-- > 0
                    && changes[0] < SNOW_CHANGES_PER_TICK
                    && System.nanoTime() < until
                    && !samples.isEmpty()) {
                Key key = samples.removeFirst();
                SnowChunk state = active.get(key);
                if (state == null) continue;
                World world = Bukkit.getWorld(key.world);
                boolean forced = accumulating(key, now, millis);
                if (world == null || !world.isChunkLoaded(key.x, key.z)) {
                    unload(key);
                    continue;
                }
                samples.addLast(key);
                if (!admitSnow(state)) continue;
                observeStorm(state, false);
                reconcile(world, state);
                boolean deposit = !Weather.tridentRainActive(world) && (forced || world.hasStorm());
                if (deposit && !state.preloading && now >= state.nextDeposit) {
                    state.nextDeposit = now + DEPOSITION_INTERVAL_NANOS;
                    depositClump(world, key, changes);
                }
            }
            globalThaw(now, System.nanoTime() + SAMPLE_BUDGET_NANOS, changes);
        }

        private void depositClump(World world, Key key, int[] changes) {
            if (changes[0] > SNOW_CHANGES_PER_TICK - CLUMP_EXTRA_MAX - 1) return;
            ThreadLocalRandom random = ThreadLocalRandom.current();
            int x = (key.x << 4) + random.nextInt(16), z = (key.z << 4) + random.nextInt(16);
            Block seed = depositionSite(world, x, z);
            if (seed == null) return;
            double chance = accumulationChance(key, seed.getY());
            if (random.nextDouble() >= chance || !form(seed)) return;
            changes[0]++;
            growClump(seed, chance, random.nextInt(CLUMP_EXTRA_MIN, CLUMP_EXTRA_MAX + 1), changes);
        }

        private Block depositionSite(World world, int x, int z) {
            Key key = new Key(world.getUID(), x >> 4, z >> 4);
            // A clump may cross an admitted chunk boundary; it must never load a neighbor.
            if (!world.isChunkLoaded(key.x, key.z)
                    || !allowed.contains(key)
                    || (active.containsKey(key) && active.get(key).preloading)) return null;
            Block top = world.getHighestBlockAt(x, z, HeightMap.WORLD_SURFACE);
            if (top.getType() == Material.SNOW || top.getY() + 1 >= world.getMaxHeight())
                return null;
            Block place = top.getRelative(0, 1, 0);
            return place.getY() >= minimumSnowY(key) && !snowy(place.getBiome()) ? place : null;
        }

        private void growClump(Block seed, double seedChance, int extra, int[] changes) {
            World world = seed.getWorld();
            List<Long> frontier = new ArrayList<>();
            Set<Long> visited = new HashSet<>();
            visited.add(column(seed.getX(), seed.getZ()));
            addClumpFrontier(seed.getX(), seed.getZ(), frontier, visited);
            int attempts = 0;
            while (extra > 0
                    && !frontier.isEmpty()
                    && attempts++ < 64
                    && changes[0] < SNOW_CHANGES_PER_TICK) {
                int pick = ThreadLocalRandom.current().nextInt(frontier.size());
                long point = frontier.get(pick);
                frontier.set(pick, frontier.get(frontier.size() - 1));
                frontier.remove(frontier.size() - 1);
                int xx = (int) (point >> 32), zz = (int) point;
                if (Math.abs(xx - seed.getX()) > 4 || Math.abs(zz - seed.getZ()) > 4) continue;
                Block next = depositionSite(world, xx, zz);
                if (next == null || Math.abs(next.getY() - seed.getY()) > CLUMP_MAX_STEP) continue;
                // One grading roll starts the clump. Downhill additions cannot evade grading.
                if (ThreadLocalRandom.current().nextDouble()
                        >= Math.min(
                                1.0,
                                accumulationChance(
                                                new Key(world.getUID(), xx >> 4, zz >> 4),
                                                next.getY())
                                        / seedChance)) continue;
                if (!form(next)) continue;
                extra--;
                changes[0]++;
                addClumpFrontier(xx, zz, frontier, visited);
            }
        }

        private long column(int x, int z) {
            return ((long) x << 32) | (z & 0xffffffffL);
        }

        private void addClumpFrontier(int x, int z, List<Long> frontier, Set<Long> visited) {
            for (int[] d : new int[][] {{1, 0}, {-1, 0}, {0, 1}, {0, -1}}) {
                long point = column(x + d[0], z + d[1]);
                if (visited.add(point)) frontier.add(point);
            }
        }

        private void startSurvey() {
            if (surveying != null || installingSurvey != null) return;
            int attempts = 32;
            while (!surveyQueue.isEmpty() && attempts-- > 0) {
                Key key = surveyQueue.removeFirst();
                SnowChunk state = active.get(key);
                World world = Bukkit.getWorld(key.world);
                if (state == null || world == null || !world.isChunkLoaded(key.x, key.z)) continue;
                if (!admitSnow(state)) {
                    surveyQueue.addLast(key);
                    continue;
                }
                ChunkSnapshot snapshot =
                        world.getChunkAt(key.x, key.z).getChunkSnapshot(false, false, false);
                int minY = world.getMinHeight(), maxY = world.getMaxHeight();
                long serial = surveySerial;
                surveying = state;
                preloadWorker.execute(
                        () -> {
                            try {
                                List<Long> found = new ArrayList<>();
                                for (int y = minY; y < maxY; y++)
                                    for (int x = 0; x < 16; x++)
                                        for (int z = 0; z < 16; z++)
                                            if (snapshot.getBlockType(x, y, z) == Material.SNOW)
                                                found.add(
                                                        pack(
                                                                (key.x << 4) + x,
                                                                y,
                                                                (key.z << 4) + z));
                                onMain(
                                        () -> {
                                            if (surveying == state) surveying = null;
                                            if (serial != surveySerial
                                                    || active.get(key) != state
                                                    || !enabled
                                                    || !world.isChunkLoaded(key.x, key.z)) return;
                                            installingSurvey = new SnowSurvey(key, state, found);
                                        });
                            } catch (RuntimeException ex) {
                                plugin.getLogger()
                                        .log(Level.WARNING, "Could not index snow in " + key, ex);
                                onMain(
                                        () -> {
                                            if (surveying == state) surveying = null;
                                            if (active.get(key) == state) surveyQueue.addLast(key);
                                        });
                            }
                        });
                return;
            }
        }

        private void changed(Block block) {
            SnowChunk state = active.get(key(block.getChunk()));
            if (state == null) return;
            long position = pack(block.getX(), block.getY(), block.getZ());
            if (block.getType() == Material.SNOW || state.snow.slots.containsKey(position))
                state.dirty.add(position);
        }

        private void forget(Block block) {
            disown(block);
            SnowChunk state = active.get(key(block.getChunk()));
            if (state != null) removeSnow(state, pack(block.getX(), block.getY(), block.getZ()));
        }

        private void expectSnow(Block block) {
            SnowChunk state = active.get(key(block.getChunk()));
            if (state != null) state.dirty.add(pack(block.getX(), block.getY(), block.getZ()));
        }

        private void installSurvey() {
            SnowSurvey survey = installingSurvey;
            if (survey == null) return;
            World world = Bukkit.getWorld(survey.key.world);
            if (active.get(survey.key) != survey.state
                    || world == null
                    || !world.isChunkLoaded(survey.key.x, survey.key.z)) {
                installingSurvey = null;
                return;
            }
            if (!admitSnow(survey.state)) return;
            long until = System.nanoTime() + 500_000L;
            int checks = 0;
            // Merge live-validated entries in small batches; retain intervening snowfall.
            while (survey.cursor < survey.found.size()
                    && checks++ < 256
                    && System.nanoTime() < until) {
                long position = survey.found.get(survey.cursor++);
                if (world.getBlockAt(x(position), y(position), z(position)).getType()
                        == Material.SNOW) indexSnow(world, survey.state, position);
            }
            if (survey.cursor == survey.found.size()) {
                survey.state.ready = true;
                installingSurvey = null;
            }
        }

        private static final class SnowSurvey {
            final Key key;
            final SnowChunk state;
            final List<Long> found;
            int cursor;

            SnowSurvey(Key key, SnowChunk state, List<Long> found) {
                this.key = key;
                this.state = state;
                this.found = found;
            }
        }

        private void formed(Block block) {
            SnowChunk state = active.get(key(block.getChunk()));
            if (state != null)
                indexSnow(block.getWorld(), state, pack(block.getX(), block.getY(), block.getZ()));
        }

        private void reconcile(World world, SnowChunk state) {
            int checks = 0;
            for (var iterator = state.dirty.iterator(); iterator.hasNext() && checks++ < 32; ) {
                long position = iterator.next();
                iterator.remove();
                indexSnow(world, state, position);
            }
        }

        private void indexSnow(World world, SnowChunk state, long position) {
            Block block = world.getBlockAt(x(position), y(position), z(position));
            if (block.getType() != Material.SNOW) {
                removeSnow(state, position);
                return;
            }
            rememberLeafOverlay(block);
            state.snow.add(position);
            if (snowy(block.getBiome())) removeMeltable(state, position);
            else if (!state.meltable.slots.containsKey(position)) {
                state.meltable.add(position);
                state.meltCost += 1.0 / meltRate(y(position), false);
            }
        }

        private void removeMeltable(SnowChunk state, long position) {
            if (!state.meltable.slots.containsKey(position)) return;
            state.meltCost = Math.max(0, state.meltCost - 1.0 / meltRate(y(position), false));
            state.meltable.remove(position);
        }

        private void removeSnow(SnowChunk state, long position) {
            state.snow.remove(position);
            removeMeltable(state, position);
            state.vetoed.remove(position);
            if (pendingMelt != null
                    && pendingMelt.state == state
                    && pendingMelt.position == position) pendingMelt = null;
        }

        private void globalThaw(long now, long until, int[] changes) {
            double seconds = Math.max(0, (now - lastMelt) / 1_000_000_000.0);
            lastMelt = now;
            meltCandidates.clear();
            int contributors = 0;
            long logged = 0;
            double totalCost = 0;
            boolean indexing = false;
            if (!enabled || coldHalf() || System.currentTimeMillis() < lateFallUntilMillis) {
                meltSeconds = 0;
                pendingMelt = null;
                return;
            }
            for (SnowChunk state : active.values()) {
                World world = Bukkit.getWorld(state.key.world);
                if (!state.admitted
                        || state.preloading
                        || world == null
                        || world.hasStorm()
                        || !world.isChunkLoaded(state.key.x, state.key.z)) continue;
                if (!state.ready) {
                    indexing = true;
                    continue;
                }
                contributors++; // Empty loaded chunks still contribute: no sparse-snow slowdown.
                if (!state.meltable.positions.isEmpty()) {
                    meltCandidates.add(state);
                    logged += state.meltable.positions.size();
                    totalCost += state.meltCost;
                }
            }
            if (indexing || meltCandidates.isEmpty()) {
                meltSeconds = 0;
                pendingMelt = null;
                return;
            }
            double meanCost = totalCost / logged;
            double rate = thawQuota(logged, contributors / meanCost);
            double creditRate = rate * meanCost;
            // Preserve the previous elevation cost and minimum throughput; stop backlog bursts.
            meltSeconds = Math.min(meltSeconds + seconds * creditRate, 2.0 * creditRate);
            int initialChanges = changes[0];
            int checks = 256;
            while (checks-- > 0
                    && changes[0] < SNOW_CHANGES_PER_TICK
                    && changes[0] - initialChanges < MELT_MAX_CHANGES_PER_TICK
                    && System.nanoTime() < until) {
                if (pendingMelt == null) pendingMelt = chooseMeltTarget(meltCandidates);
                if (pendingMelt == null) {
                    meltSeconds = 0;
                    return;
                }
                MeltTarget target = pendingMelt;
                SnowChunk state = target.state;
                World world = Bukkit.getWorld(state.key.world);
                if (active.get(state.key) != state
                        || world == null
                        || world.hasStorm()
                        || state.preloading
                        || !world.isChunkLoaded(state.key.x, state.key.z)
                        || !state.meltable.slots.containsKey(target.position)) {
                    pendingMelt = null;
                    continue;
                }
                Block block =
                        world.getBlockAt(
                                x(target.position), y(target.position), z(target.position));
                if (block.getType() != Material.SNOW) {
                    removeSnow(state, target.position);
                    continue;
                }
                if (snowy(block.getBiome())) {
                    removeMeltable(state, target.position);
                    pendingMelt = null;
                    continue;
                }
                if (now < state.vetoed.getOrDefault(target.position, 0L)) {
                    pendingMelt = null;
                    continue;
                }
                double localRate = meltRate(block.getY(), false);
                if (localRate <= 0) {
                    state.vetoed.put(target.position, now + 1_000_000_000L);
                    pendingMelt = null;
                    continue;
                }
                double cost = 1.0 / localRate;
                if (meltSeconds + 1e-9 < cost) return;
                long before = melted;
                melt(block);
                pendingMelt = null;
                if (melted > before) {
                    meltSeconds = Math.max(0, meltSeconds - cost);
                    changes[0]++;
                    if (block.getType() != Material.SNOW) removeSnow(state, target.position);
                } else state.vetoed.put(target.position, now + 1_000_000_000L);
            }
        }

        private MeltTarget chooseMeltTarget(List<SnowChunk> candidates) {
            long total = 0;
            for (SnowChunk state : candidates) total += state.meltable.positions.size();
            if (total == 0) return null;
            long pick = ThreadLocalRandom.current().nextLong(total);
            for (SnowChunk state : candidates) {
                int size = state.meltable.positions.size();
                if (pick < size)
                    return new MeltTarget(state, state.meltable.positions.get((int) pick));
                pick -= size;
            }
            throw new IllegalStateException(
                    "Snow melt index changed during a main-thread selection");
        }

        private record MeltTarget(SnowChunk state, long position) {}

        private boolean snowy(Biome biome) {
            return vanillaSnowy.contains(biome) || snowyNames.contains(biome.getKey().toString());
        }

        private static double thawQuota(long logged, double previousRate) {
            return Math.min(
                    MELT_MAX_LAYERS_PER_SECOND,
                    Math.max(previousRate, MELT_FRACTION_PER_SECOND * logged));
        }

        private double meltRate(int y, boolean snowy) {
            return snowy ? 0.0 : MELT_RATE_MULTIPLIER * gradient(y, MELT_RATE_LOW, MELT_RATE_HIGH);
        }

        private double gradient(int y, double low, double high) {
            double fraction =
                    Math.max(
                            0, Math.min(1, (y - MELT_LOW_Y) / (double) (SNOW_HIGH_Y - MELT_LOW_Y)));
            return low + (high - low) * fraction;
        }

        private void readState(DataInputStream in) throws IOException {
            int first = in.read();
            if (first < 0) return;
            int magic =
                    (first << 24)
                            | (in.readUnsignedByte() << 16)
                            | (in.readUnsignedByte() << 8)
                            | in.readUnsignedByte();
            if (magic != SNOW_STATE_MAGIC) throw new IOException("Unknown snow-period state");
            lastAccumulationYear = in.readLong();
            lateFallUntilMillis = in.readLong();
            if (lastAccumulationYear < -1 || lateFallUntilMillis < 0)
                throw new IOException("Invalid snow-period state");
            lateFallUntilMillis =
                    Math.min(
                            lateFallUntilMillis,
                            System.currentTimeMillis() + SNOW_ACCUMULATION_MILLIS);
            int firstOwned = in.read();
            if (firstOwned >= 0) {
                int marker =
                        (firstOwned << 24)
                                | (in.readUnsignedByte() << 16)
                                | (in.readUnsignedByte() << 8)
                                | in.readUnsignedByte();
                if (marker != OWNED_SNOW_MAGIC) throw new IOException("Unknown owned-snow journal");
                int count = in.readInt();
                if (count < 0 || count > 5_000_000)
                    throw new IOException("Invalid owned-snow count");
                for (int i = 0; i < count; i++)
                    ownedChunks.add(
                            new Key(
                                    new UUID(in.readLong(), in.readLong()),
                                    in.readInt(),
                                    in.readInt()));
            }
            int profileFirst = in.read();
            if (profileFirst < 0) return;
            int profileMarker =
                    (profileFirst << 24)
                            | (in.readUnsignedByte() << 16)
                            | (in.readUnsignedByte() << 8)
                            | in.readUnsignedByte();
            if (profileMarker != SNOW_PROFILE_MAGIC) throw new IOException("Unknown snow profile");
            if (in.readBoolean()) {
                SnowProfile profile =
                        new SnowProfile(
                                in.readLong(), in.readDouble(),
                                in.readDouble(), in.readDouble());
                if (!(profile.minProbability > 0
                        && profile.minProbability <= profile.maxProbability
                        && profile.maxProbability <= 1
                        && profile.rateScale > 0
                        && profile.rateScale <= 2)) throw new IOException("Invalid snow profile");
                snowProfile = profile;
            }
        }

        private void writeState(DataOutputStream out) throws IOException {
            out.writeInt(SNOW_STATE_MAGIC);
            out.writeLong(lastAccumulationYear);
            out.writeLong(lateFallUntilMillis);
            out.writeInt(OWNED_SNOW_MAGIC);
            out.writeInt(ownedChunks.size());
            for (Key key : ownedChunks) {
                out.writeLong(key.world.getMostSignificantBits());
                out.writeLong(key.world.getLeastSignificantBits());
                out.writeInt(key.x);
                out.writeInt(key.z);
            }
            out.writeInt(SNOW_PROFILE_MAGIC);
            SnowProfile profile = snowProfile;
            out.writeBoolean(profile != null);
            if (profile != null) {
                out.writeLong(profile.winter);
                out.writeDouble(profile.minProbability);
                out.writeDouble(profile.maxProbability);
                out.writeDouble(profile.rateScale);
            }
        }

        private void status(CommandSender sender) {
            long remaining = Math.max(0, lateFallUntilMillis - System.currentTimeMillis());
            int preloads = pendingPreloads.size();
            long indexing =
                    active.values().stream()
                            .filter(state -> state.admitted && !state.ready)
                            .count();
            sender.sendMessage(
                    "§eTree normalization in progress: §f"
                            + winterNormalizations.size()
                            + "§e; snow indexes still building: §f"
                            + indexing
                            + "§e. Melting waits for the loaded-chunk index before sampling"
                            + " globally.");
            int full = 0, partial = 0, loaded = 0;
            for (SnowChunk state : active.values()) {
                readCoverage(state);
                if ((state.coverageFlags & FULL_STORM) != 0) full++;
                if ((state.coverageFlags & PARTIAL_STORM) != 0) partial++;
                if ((state.coverageFlags & PRELOADED) != 0) loaded++;
            }
            sender.sendMessage(
                    "§eThis winter, loaded chunks: full storm §f"
                            + full
                            + "§e, partial storm §f"
                            + partial
                            + "§e, preload completed §f"
                            + loaded
                            + "§e. Markers persist across chunk unloads and server restarts.");
            SnowProfile profile = snowProfile;
            if (profile != null)
                sender.sendMessage(
                        String.format(
                                Locale.ROOT,
                                "§eSnow profile: min %.5f, max %.5f, rate scale %.3f; upper Y%d.",
                                profile.minProbability,
                                profile.maxProbability,
                                profile.rateScale,
                                SNOW_HIGH_Y));
            for (World world : Bukkit.getWorlds()) {
                if (world.getEnvironment() != World.Environment.NORMAL) continue;
                Key key = new Key(world.getUID(), 0, 0);
                sender.sendMessage(
                        "§eCold-season snow line in §f"
                                + world.getName()
                                + "§e: §fY"
                                + coldSnowLine(key)
                                + "§e (sea level Y"
                                + seaLevel(key)
                                + ").");
            }
            int count = active.values().stream().mapToInt(s -> s.snow.positions.size()).sum();
            sender.sendMessage(
                    "§eSnow: §f"
                            + (!enabled
                                    ? "vanilla (seasons disabled)"
                                    : coldHalf()
                                            ? "cold half"
                                            : "warm half; half-rate snow above Y125; clear-weather"
                                                    + " thaw")
                            + "§e; late-fall accumulation: §f"
                            + (remaining + 999) / 1000
                            + "s§e; pending winter preloads: §f"
                            + preloads
                            + "§e; indexed snow blocks: §f"
                            + count
                            + "§e; surveys queued: §f"
                            + surveyQueue.size()
                            + "§e.");
            sender.sendMessage(
                    "§eSnow layers placed/melted this session: §f"
                            + formed
                            + "/"
                            + melted
                            + "§e; thaw: "
                            + MELT_FRACTION_PER_SECOND * 100.0
                            + "% of logged eligible snow/second, capped at "
                            + MELT_MAX_LAYERS_PER_SECOND
                            + "; previous minimum per chunk: §f"
                            + MELT_RATE_LOW * MELT_RATE_MULTIPLIER
                            + " at Y90, "
                            + MELT_RATE_HIGH * MELT_RATE_MULTIPLIER
                            + " at Y140+; snowy biomes never melt§e.");
        }

        private static final class SnowChunk {
            final Key key;
            final SnowIndex snow = new SnowIndex(), meltable = new SnowIndex();
            final Set<Long> dirty = new HashSet<>();
            final Map<Long, Long> vetoed = new HashMap<>();
            long nextDeposit, admissionTick, coverageWinter = Long.MIN_VALUE, stormEnd;
            int coverageFlags;
            double meltCost;
            boolean ready, admitted, preloading, fullStormCandidate;

            SnowChunk(Key key) {
                this.key = key;
            }
        }

        private static final class SnowIndex {
            final List<Long> positions = new ArrayList<>();
            final Map<Long, Integer> slots = new HashMap<>();

            void add(long position) {
                if (slots.putIfAbsent(position, positions.size()) == null) positions.add(position);
            }

            void remove(long position) {
                Integer slot = slots.remove(position);
                if (slot == null) return;
                long last = positions.remove(positions.size() - 1);
                if (slot < positions.size()) {
                    positions.set(slot, last);
                    slots.put(last, slot);
                }
            }

            long random() {
                return positions.get(ThreadLocalRandom.current().nextInt(positions.size()));
            }
        }

        private boolean form(Block block) {
            if (enabled && Weather.tridentRainActive(block.getWorld())) return false;
            if (!block.getType().isAir() || block.getLightFromBlocks() >= 10) return false;
            Snow snow = (Snow) Material.SNOW.createBlockData();
            snow.setLayers(1);
            if (!block.canPlace(snow)) return false;
            org.bukkit.block.BlockState state = block.getState();
            state.setBlockData(snow);
            BlockFormEvent event = new BlockFormEvent(block, state);
            formingSnow = true;
            try {
                Bukkit.getPluginManager().callEvent(event);
            } finally {
                formingSnow = false;
            }
            if (event.isCancelled() || event.getNewState().getType() != Material.SNOW) return false;
            if (!(event.getNewState().getBlockData() instanceof Snow newSnow)
                    || newSnow.getLayers() != 1) return false;
            rememberPlaced(block);
            block.setBlockData(event.getNewState().getBlockData(), true);
            rememberLeafOverlay(block);
            formed(block);
            formed++;
            return true;
        }

        private void melt(Block block) {
            if (snowy(block.getBiome()) || !(block.getBlockData() instanceof Snow snow)) return;
            rememberLeafOverlay(block);
            BlockData replacement;
            if (snow.getLayers() == 1) replacement = Material.AIR.createBlockData();
            else {
                snow.setLayers(snow.getLayers() - 1);
                replacement = snow;
            }
            org.bukkit.block.BlockState state = block.getState();
            state.setBlockData(replacement);
            // Allow protection plugins to veto our own thaw without our fade listener canceling it.
            BlockFadeEvent event = new BlockFadeEvent(block, state);
            thawing = true;
            try {
                Bukkit.getPluginManager().callEvent(event);
            } finally {
                thawing = false;
            }
            if (!event.isCancelled()) {
                disown(block);
                block.setBlockData(event.getNewState().getBlockData(), true);
                melted++;
            }
        }

        private boolean thawing;

        private void shutdown() {
            if (manager != null && listener != null) manager.removePacketListener(listener);
            // A login registry cannot be shrunk while a client stays connected. A plugin
            // unload (unlike /season disable) needs a reconnect to return to the server registry.
            for (UUID id : sessions.keySet()) {
                Player player = Bukkit.getPlayer(id);
                if (player != null && player.isOnline())
                    player.kickPlayer("Seasonal weather was unloaded. Please reconnect.");
            }
            sessions.clear();
            allowed.clear();
            active.clear();
            samples.clear();
            refreshes.clear();
            queuedRefreshes.clear();
            pendingPreloads.clear();
            captures.clear();
            preloadSerial++;
            preloadQueue.clear();
            readyPreloads.clear();

            meltCandidates.clear();
            pendingMelt = null;
            if (preloadWorker != null) preloadWorker.shutdownNow();
            surveyQueue.clear();
            surveySerial++;
            surveying = null;
            installingSurvey = null;
        }
    }

    private record BiomeSession(int[] snowIds, int[] rainIds, int globalBits) {}

    private static byte[] packetBytes(PacketContainer packet) throws IOException {
        Object buffer = packet.serializeToBuffer();
        try {
            Class<?> type = Class.forName("io.netty.buffer.ByteBuf");
            int length = (int) type.getMethod("readableBytes").invoke(buffer);
            byte[] bytes = new byte[length];
            type.getMethod("readBytes", byte[].class).invoke(buffer, (Object) bytes);
            return bytes;
        } catch (ReflectiveOperationException ex) {
            throw new IOException("Cannot read the login packet buffer", ex);
        } finally {
            releasePacketBuffer(buffer);
        }
    }

    private static PacketContainer packetFromBytes(PacketType type, byte[] bytes)
            throws IOException {
        Object buffer = MinecraftReflection.createPacketDataSerializer(bytes.length);
        try {
            Class.forName("io.netty.buffer.ByteBuf")
                    .getMethod("writeBytes", byte[].class)
                    .invoke(buffer, (Object) bytes);
            return new PacketContainer(type, PacketContainer.deserializeFromBuffer(type, buffer));
        } catch (ReflectiveOperationException ex) {
            throw new IOException("Cannot rebuild the login packet", ex);
        } finally {
            releasePacketBuffer(buffer);
        }
    }

    private static void releasePacketBuffer(Object buffer) {
        if (buffer == null) return;
        try {
            Class.forName("io.netty.buffer.ByteBuf").getMethod("release").invoke(buffer);
        } catch (ReflectiveOperationException ex) {
            throw new IllegalStateException("Cannot release packet buffer", ex);
        }
    }

    private static int bitsFor(int count) {
        return count <= 1 ? 0 : 32 - Integer.numberOfLeadingZeros(count - 1);
    }

    /** 1.18.2 section codec: block palettes are copied byte-for-byte; only biomes change. */
    private static byte[] rewriteBiomes(
            byte[] source,
            int minY,
            int sections,
            BiomeSession session,
            int minimumSnowY,
            boolean rainOverride)
            throws IOException {
        ByteArrayInputStream bytes = new ByteArrayInputStream(source);
        DataInputStream in = new DataInputStream(bytes);
        ByteArrayOutputStream target = new ByteArrayOutputStream(source.length + 512);
        DataOutputStream out = new DataOutputStream(target);
        boolean changed = false;
        for (int section = 0; section < sections; section++) {
            int start = source.length - bytes.available();
            in.readShort();
            skipBlockPalette(in);
            int end = source.length - bytes.available();
            out.write(source, start, end - start);
            int bits = in.readUnsignedByte();
            if (bits > 12) throw new IOException("Invalid biome palette width: " + bits);
            int[] palette = null;
            if (bits == 0) palette = new int[] {readVarInt(in)};
            else if (bits <= 3) {
                int count = readVarInt(in);
                if (count < 1 || count > (1 << bits))
                    throw new IOException("Invalid biome palette size");
                palette = new int[count];
                for (int i = 0; i < count; i++) palette[i] = readVarInt(in);
            }
            int longs = readVarInt(in), perLong = bits == 0 ? 0 : 64 / bits;
            if (longs != (bits == 0 ? 0 : (64 + perLong - 1) / perLong))
                throw new IOException("Invalid biome storage length");
            long[] packed = new long[longs];
            for (int i = 0; i < longs; i++) packed[i] = in.readLong();
            int[] cells = new int[64];
            for (int i = 0; i < 64; i++) {
                int value =
                        bits == 0
                                ? 0
                                : (int)
                                        ((packed[i / perLong] >>> ((i % perLong) * bits))
                                                & ((1L << bits) - 1));
                if (palette != null && value >= palette.length)
                    throw new IOException("Biome palette index out of bounds");
                int id = palette == null ? value : palette[value];
                // Client biome cells are 4 blocks high and may straddle the altitude threshold.
                int cellY = minY + section * 16 + (i >> 4) * 4;
                if (rainOverride && id >= 0 && id < session.rainIds.length) {
                    int rain = session.rainIds[id];
                    changed |= rain != id;
                    id = rain;
                } else if (cellY + 3 >= minimumSnowY && id >= 0 && id < session.snowIds.length) {
                    int snow = session.snowIds[id];
                    changed |= snow != id;
                    id = snow;
                }
                cells[i] = id;
            }
            changed |= bits > 3 && bits != session.globalBits;
            writeBiomePalette(out, cells, session.globalBits);
        }
        // 1.18.2 overallocates empty-section buffers: its size calculation uses
        // the element count for the storage-length VarInt. Vanilla ignores this zero padding.
        if (in.available() > sections * 2) throw new IOException("Excess chunk section padding");
        while (in.available() != 0)
            if (in.readUnsignedByte() != 0)
                throw new IOException("Unexpected trailing chunk section data");
        return changed ? target.toByteArray() : null;
    }

    private static void skipBlockPalette(DataInputStream in) throws IOException {
        int bits = in.readUnsignedByte();
        if (bits == 0) readVarInt(in);
        else if (bits <= 8) {
            int n = readVarInt(in);
            if (n < 1 || n > 256) throw new IOException("Invalid block palette size");
            for (int i = 0; i < n; i++) readVarInt(in);
        }
        if (bits > 16) throw new IOException("Invalid block palette width");
        int n = readVarInt(in);
        if (n < 0 || n > 4096) throw new IOException("Invalid block storage size");
        in.skipNBytes(n * 8L);
    }

    private static void writeBiomePalette(DataOutputStream out, int[] cells, int globalBits)
            throws IOException {
        Map<Integer, Integer> palette = new LinkedHashMap<>();
        for (int id : cells) palette.computeIfAbsent(id, k -> palette.size());
        int bits =
                palette.size() == 1
                        ? 0
                        : palette.size() <= 8 ? Math.max(1, bitsFor(palette.size())) : globalBits;
        out.writeByte(bits);
        if (bits == 0) {
            writeVarInt(out, cells[0]);
            writeVarInt(out, 0);
            return;
        }
        boolean indirect = bits <= 3;
        if (indirect) {
            writeVarInt(out, palette.size());
            for (int id : palette.keySet()) writeVarInt(out, id);
        }
        int perLong = 64 / bits, n = (64 + perLong - 1) / perLong;
        writeVarInt(out, n);
        for (int word = 0; word < n; word++) {
            long packed = 0;
            for (int j = 0; j < perLong; j++) {
                int i = word * perLong + j;
                if (i >= 64) break;
                int value = indirect ? palette.get(cells[i]) : cells[i];
                packed |= ((long) value) << (j * bits);
            }
            out.writeLong(packed);
        }
    }

    private static int readVarInt(DataInputStream in) throws IOException {
        int value = 0;
        for (int i = 0; i < 5; i++) {
            int b = in.readUnsignedByte();
            value |= (b & 127) << (i * 7);
            if ((b & 128) == 0) return value;
        }
        throw new IOException("Invalid VarInt");
    }

    private static void writeVarInt(DataOutputStream out, int value) throws IOException {
        do {
            int b = value & 127;
            value >>>= 7;
            out.writeByte(value == 0 ? b : b | 128);
        } while (value != 0);
    }

    private static final class SnowColors {
        private static final String GRASS_PNG =
                "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAAAABGdBTUEAALGPC/xhBQAAG6FJREFUeNrtXem6HMWRjexXmn3fx2Mb"
                    + "D8bGCzbGGIxZjI3BMtiAAEn3Mvs+45kXAYEsZHaNDMMr9fyQLre6KiIyIjMyq6rrHH39Sequzq0rT0WcjMjcfeb/fm0PAMA2sUtE"
                    + "9NlPfp0AANgedmf/AAkAwAYJIBHR2etzn/wGRgQAtmUBDCkg0ec/+U2MCgBs0QI4e90FEgCAbRLAGe765LcwOgBw/C6ADJAAAGyY"
                    + "AEACAHDsBLAnGr4S8/rCx7+NkQKA47QAxgoAJwuCBADgKAkgCVOee9398e9gxABgSxrAGHd//LsYNQDYogUAEgCAIycADcPrvggS"
                    + "AIBjcwHS4M9wwvN/7vn49zCCALBqC0BY+uNexLzu+ej3MYoAcBwWQBm+BBIAgOPXAMY6wPA7IAEAOBILIBW+vvzRH2BEAWBdBCDZ"
                    + "ALnFQKJp9CBIAABW7QJYYwE0y+Hej/4QIwsAa3UBInDvR3+E0QWANVoAlqe89L3h/78CEgCA9VkAFhfA6iKABABgyRbAPtH5i+jw"
                    + "/3deTHQgO+0nZd1+ffVXf4yRBoAtaQBjgAQA4Ag0AIsLIH32tV/9CUYcANasAdS+vn4LJAAAm3MBhgAJAMAiXYBzqS+xqcFpdA0J"
                    + "V0u2xPl79936U4w+AGzRAjjDfbf+DL8AACzHAogPC869vgESAIDlEcABhM1AcpuHsJ8x5YMEAGBhLoDVAii1EMb1fPPWn+PXAID+"
                    + "FoD0J7cnIE2ukuhDLufw/ftv/QV+EQBYggUwF0ACALA0DcBgwkcKifff+kv8MgCwFAugRgcoDS3+1v+CBABgcy7AECABAGjtAkzS"
                    + "f2maFkw0SfEdfv7p0uDkWX7+3kT4m5SRBunE9GmdD9z8DH4lANiiBXCGB27+FX4pAGhiAQT48BExA7m6QAIAMJMFYJ20EWKgVs63"
                    + "QQIA0N8CiMgNiLIWHrz5WfxqALAlDWAMkAAAhFkA0/BePmCXTMZ/yoT+nn9DDz2W67n994M3P4dfDwB6WQDRW4N5IJXxHZAAAGzP"
                    + "BRgCJAAANS5AJq9/nMdverLvDa8711nqzFkCD938PH5JANiiBXCGh27ehV8TANwWAEl5/6ScBKQt1hFZNhWVdxXQhUG5PKKHQQIA"
                    + "0M4CaHVWAFGcePjwhyABACi0AOaZ1KmiA1xZ3/3wC/hlASCaAOac1N42PQISAIBYF2BteOTDv8YvDAC6BWAX7NLkOU3Ms563AfSN"
                    + "R6e1WDYRPRcHpXYleuTDu/ErA0C1BeA4E8B8ToDXfSiML/jeByABANicCzAESAAAWBeg7XHgEaIgVdZ19t6jIAEA2KYFcIZHP/gi"
                    + "fnUAOLcA8unA3GfkTBMeX2s9LWgsP3pFy8S05dEP7sEvDwC1FkDPQKEIN2LY7sdAAgBQfzz4XJpAhD4AEgBgAWwcj33wJdwFACyA"
                    + "tT3Fc4q/5/U4SADYrAVwEEiTBi8aBdgk4XPmZCHKiYmjzw8CjLhTiu68T0k9oejTU4rU6ECeLh5//8u4GwC4AFsGSACAC1Bhgs8d"
                    + "LBThYjwBEgBgAWwbT7x/LwYBgAWwtqd3pFD4/fe/grsD2IIF4DHopWk0fd8esZd7/7Auef9AS0SjfOgId+2TIAEAFsA8QUJWK6O1"
                    + "9fLk+1/FXQIcMQF48vo9k8qzfwCVt8EMyz4CwrVPvgcSAI7WBQAsAAkAcAFoeQKhBVF9+MF7X8MdAxybBeAVAD36uv5ZmSgoCX5j"
                    + "cZDYM4mJSCjT9u8fvvd13DUAXIAtAyQAgABAAhgEABrAnFl8c+sRIAEABEDrFwm9GLb7qffuw10EHIsLkAm5EdKB2ReRIc04nf89"
                    + "aQcRJ0BOU4m19OBh/IB2PfHpzEy6cWLSp5969xu4kwBYAEuwFOZq149AAsD6LQCgBiABABbAxrUEkAAAC+DIkSOhp9/9JgYJWAsB"
                    + "eHP5qPBz7XvUqS4y1EUhdT397v24uwC4AMf4sgIkAMAF2DhAAgAsgI2/ngEJAIu1AHIbZYw3zfBeX4JebWrVfqb8Z975Fu42YIkW"
                    + "gO+k3aT+qUnxlf7N7fEnp/6WpPiWphnb3j//8+N3HsAdB0AD2DJAAgAIACSAQQCW4gJApJvjdQEkAMAC2DYuvPNtDAKwJALw7MBP"
                    + "5D0spC7iriaSz/K+pa1U+L7chgvvPIi7EIAFsG1LACQAzKUBeA4G2Vf4vd46StvUoS/FcRDKtRfe/g7uRmAGAiDE9HvRqj0/AQkA"
                    + "IIB+k3qJ7X8WJAD01QBqjvb0inVW8SxXpizeydGC3PslUY+WcocnEVuFwfP3n337IdyZAETALePZtx/GIADbdQGOBTVj8BxIANgK"
                    + "ASzJP18SQALAMl2APS0nbbdRCm/E8l5E20ACQEMC8OzBFxFxxwuJPsHNm37Mp/7yYqYvxVdvo1cYJOHfiZ57+7u4W4EFWQDADO7A"
                    + "IxgEYN0awJKwxtOLfvpLkACwQgJoPemWRDCt+wMSAFbnAqxx9WDJZPKzX34Pdy8ADWDLAAkAwS5ATsG2q+C+FQOi0rDh+hWDJCrz"
                    + "vk1B+bbY++UNez4jgUdxFwPL0gCI1ufbt2pjj36DBIByF8Ab0GN4ReT5jwNoqiZSSSBRwXeqJ7llLIX+PX8DJABAA9g0nr/xGAYB"
                    + "AAGABADArAFY/tiENf9+ALJBXBb6K4fc2k4ksop5434Q2UXP6We2fQoO26wJhs/feBx3NmAlgGUE+bTAnGJea+TqfwEkAPQgADpC"
                    + "8pgjIKkFQAJAcw1gzeQxF2m0+D5IAJiFAIDl44UbT2AQAMEF2Ceavsbrz8xnRET7NHrRnVeSPxNlLlvE3bBMuY2jz86Es730febf"
                    + "lItsJDIJgwfr+mf1DtuYmDX+QXzi5Psk9o9v7e3/vXDj+7jbgTgNIMpX7umf9/Lpe7sW1u++CBIA4AJsGy/eeBKDANQTwLFaDT2t"
                    + "hV5WAkgAgAUAgAQATgPwnYjj2yj08H0+ulCTBIcl2lJ/889F/flpEiLFGEGpb8PIxHG0ox75ZxnXcbk0aRWxbboIEgABLHUfwNLy"
                    + "l3Q4aK2pTtTejbh44weYBXABlutPz0kWPbSHmuuj+nDxxg8xE0AAwJYBEtiqC7Av3KTDcNKNZaOOcdnZdgwrKDidKMRyyY1Lbowc"
                    + "/fWMqfk3ENp68S2QwMY1gER1J/CMpTj7VPOUaztFiGi6ACm1S5MrKZuKaxNNiez7IubGhSYjQiRFUhK776FU7ksgAbgAEeJXK58/"
                    + "WnuglbYhV37NtSABEACwcbz01lMYBBAAABIANqQBxJipc7sKkfVHm+ap8tre9b/01o8wS46bAHKCmj0KL2WOuCajEJWEODo+elCL"
                    + "UNS9cj0Skb+a3yuQHFOLlNTncfwjieOjj7PWrnzM5eGx7UQvgwS2bQGo02u0HObd77/ofAFmSbDqSe6sm53ie8fyYOHTW73Guiy5"
                    + "V+pUfrOXrz+N2bJVDWDJR4jPYepHrQBEmfWl13nrfQUkABEQ2DZAAht1AaKejHMkF/V+WtfG/i/dMnjl+jOYOccpAlojAilzsq4m"
                    + "fuUP4JDSaZOwU980XZfImqZsFRYlcdRelyQASlF6JBy3Yj9JWI9k1MYgJzSCBOACAHAHQALbIICeZnuEmNfalJ/LjG9ZV+l1IAFY"
                    + "AMDmLYEfYxBWqwHsnWvYXIqtYe3flN5baR3k2kJKGw7KyfTZ0o+wp7Xhtxn3YVLP3tgnKhMSQQJrJgCqSwe2GOZaFB+R9WReXWyz"
                    + "fL8s4tCy1+C4H/L3kykSL9dXTYzk+poUwZIE54lG5fBy5VC0vXT9AmbUsbgAvfz+2iW6lrpC5BO9tI+tNYQSaGWABKABABvHpes/"
                    + "wSCs0wWID/6peXrXKP4RT865LIPIp3aPlQXuuyCBlRNA6wnc0rRfKjG0dBeiTHgS1QB/+ZdBAmtwAawpq1Zh0BYdWLrvHy+W2SIO"
                    + "p5+RKGzJh5vIp/DmxsEiqMnTndhoxGnaMDdWpAqAyVQ2CcKs/u/L15/FLIMGAGwZl68/h0EAAQAgAWB5GkBFEFBSglCqfPuCgCJ2"
                    + "swvjJh+UCwyK1Atq+sP0LRsgtI8JGTbrCMr9cvkXIIHlEQDFC4C9YwaI4sXKVmKeXW2IGR9q1BcPWRxYAiCBpbkAWkSbLR3YHh1Y"
                    + "ts9gLuJQ2sMwJzhq++lp38mn9MpTRI89JDElN2WuzAt8uTOXufaSs1xuH8PEkMBPMfOWbAG0ehqXWg2lT68WT8QW1oKnzJZP86jl"
                    + "RUt9IAGIgMDWhcFf/AyDsDYNoLdl4H1ipYr2tfC9ez6lW2gVEeOhfQ4SWKkIGDnxluwuRJv1qcGkiiYEMtZFQW2/AhJYigtQmbO2"
                    + "J6J9Yl6ez+7Uc7CElJSXdI1V1Mr1l/n3QZ1U36Z9YpbNtDKJ9NRhT3+16Z1G/R33mYR2ZcRQ5vtXroEEoAEA29YErj2PQVgCAfQ8"
                    + "6KOHBhGpFyzFLfA8xym43ZGaw8QdAAnMrwFETti0gMnXWn+ImlxUMblKl/ZaCpSl/b9y7QXMzKWKgD3IYYnWwpzlELWNV6AOJOYt"
                    + "5wQk0MsF8EXW5RJeOfHHlprLRdol5jCL3Gm3ekpxTiiTRsEbhSfvCSj1i5+a0t5/3N6Ktt+Be5/EsUnMv0gZR34fRa3PcptBAhAB"
                    + "gY0DJNDZBegl2HnN0FZm+Rw6RJSZXOoi9AoyyvXZTgIvYqY2I4B9fl//XJrwJI1WSXU177VPZVEJrhu/4EwENf3ZUwZzpkA3YjGk"
                    + "SUv9VQnB2OcSUjm5dhGztYcLMIdgVyJoRZBCK2sjqgyaoYzSp3dJ2d4yQALNRcDoKWc76MK+V21exJt+RhS3MJYM/SIqW4m3pBNL"
                    + "baj5HYi0g0FsY1n6W3jaBhKACAgAIIF1iIC1ZUSa3NFmdIRfvhSXoNQdiB4nbxkn117C7G1BABETmjqTgrcNPf371IlUSn3vltpA"
                    + "CmwfSGBFIuCaSKG2XdSIVHp/31tGL8sg9/2Tay9jFsdZANoJv3xsHL/LnuUgECJp7z19P8HERCbm+kCf1jaOVLO2y3bysbRvoC6S"
                    + "ye3SxoTM/cqJi9zBIIdtoKxoKUUlct/PHy4yLZe3ChJIACIgABCdXHsFg1BkAVQEAYnXt3QVDAEs5uAjmu7XT1pATC7Ip8CErTWB"
                    + "td9FGiezP964/9FjcvImSKCZCFjrJ0eSQpRfavn+kvx1qhiL2olHleNZI/Z5ygQJwAUAtu4OgARAAABIADARgOW8H8sx4bz2TWTL"
                    + "+z805oikHH2pXdZTiKho1YAO1gemJr2cB6/vtcBr/dNxmNZNTN28sUyTuqfv5R0yaV8CMtbPj66+X8L4PhiXmzt/6eTNS5jhXg3A"
                    + "6k+2iBWI1Bjm+G4LH3uuMajRJmr67NUFcpkbJ29exiy3EgAFT8Ql3dC1fbDcfNHtoBknZM33owXOWsHxFCRg0wDCn+odlhhd39Xq"
                    + "dUzqGhKytJ8My5va8eG5PQ/MdQZNwGqrQFnitC5DggQgAgIbB0iAdQE4OW/MxDZh0HbMuFVylKSdEgGO2FBlfbPQZDoaXA/PTWrY"
                    + "sSTs8UJoYsS//CabnLiYPyJ9Ot7TdshhvFzb/GHR+neTuC8CL0Oe/e/0zSuY9ZoI2FrE8xza4Smrh97QKkCpt1ZSY6KX9jvSLah1"
                    + "TUACHTQACiaSJa4qROgFc0zqqOjEUuIqmcARpDK85vTNE8x+aADAtjUBkAAIANg2CbyxbRLY8UKYJNWRSfwjt2io5/3nTvwhk4hH"
                    + "k7x3S368FkVHglBlE/iIphFy0/jAaf3+vRKmdedPBkpKFv6hwJiYHpEo8uk5/rKwxwuLvEip189oAhsmgWYiYKSf3mOr8hp/vaef"
                    + "XFJ/hBbiEexqhVFPXTyt+rWFrZLAzhtA4wpaIXvAjjXvnAtWqSUEt+iXC85xBPSU1GUOjNnHRdbVRkceQBgn8R4oFQcth7QMvnf6"
                    + "xik0AADYtiawLRLYRSQCRZj6rdbmo8rwugclZn7J07ikbiqsu8QtoMbt88RXWNt7+sarW9UAJIFOFveItK1DdVnQHoVnEf/k6D5t"
                    + "E1Nd9OTLoEzUIz8S+oailBU2rQJaXsDLpeYmxcPmN07lREZtK1D9SHO5fbKQSSSlKWtlTOs/K2MrJLCrFdh6iYglvqw3wCgFtLP0"
                    + "KV/brtIndWkmoLeuGsEvwiLwlrEVEoAGAACqJvAqCAAAtk0Cf7MNAuix20+ECBclGEab6hGmfbQLQRW/QYkbUbP82tJ98JYxvv5Y"
                    + "SWBwLkC6szaahJiANPg7MZ+lO2uuiVnj5U6f0c57kdN+cymkiUshHfXtcL05nbfxoI/j9ehBGZObZBQZd9D/NBjTxMQEcOOWmHVq"
                    + "m4A2Fr+s6bWUOX1nIvtO1tSn/ZiO3XT8POIg0WEd4u8ziB9Iwvgc3jvK/oODfp1e/dvtiIBkfFLMHUHY2gJpJYr1fHJqfShN5416"
                    + "WtdYO9425cRFizVxbCSwazk5e0/u6Dpq66OC62vcilK3pXb/w56ElZvE3vJLvn969e8gAgLApoXBIyGBnVVoW7pF0OLpWbvW7o3Y"
                    + "q4l1iHjKJlrHkzrChagRGNMRkcAuuY741vf0y6cEy+nBuei6lImu49rviRq0RwhyApIv8m96ILklvVcXydJE/POl1/Jkpe//xwuF"
                    + "Wvt8qcPSce2kiMdczbLIqbWGEwen0unp1b/frgYwl3VgYfqo7cxKdYhIH977pI/OEYj8XUrb5xH8onWB3HdfXTEJzKsB7Du9ete/"
                    + "dMzdx7nHtkF9a7UEIAICQJgwuD4SCBUBey23RS7NtRQie4t4UaZ56VJZhDgY2e8SYc/brqkw+A9rFQE1US6/V18yCWyagEeqgGdL"
                    + "q6VMunESj/uQ9u5LjBwkRY/l9gTUTkLOH3gi94MyAiQ/tlpqLCfATeVRbp9ASRwkoziYMgKcN8U3Ca21kIA/9DitjgS6iYDRKcbR"
                    + "YmHPa6NzAXpYBb2smxqxr/W1nn0G10IC0AAAoJkmsHwSmE0D6GERrOHaVsuTpddag5R6t2tJ13osmdOr/7gOAigRidb24yzp2lza"
                    + "rtdHjbo2wkwuFdvm6G9rXWDpJLCT5THKCEspExHI732nCXSUOUlYEoQS6ZFtsuBWKqCVCHOSoMWn6CZBPPMcWKKf7KtHXVLm9OFp"
                    + "1CUxezfK35XayB/zkZhP5eg8G4nJ0qynDVLtYyHz9Oo/LZQAegXj5IIs5q5/qVhav5cy7iv83U8WSAIQAQFgwySwixAAI66N1AYi"
                    + "BMalaAilolzptRSgTVjM8FrdpESf6HVtTkNYEgnsWqTpRiQIRdRfejN7SKxU9EvOG33OOADvhC7ps1cY9PaRGl/rHcOTq/+8FALI"
                    + "n+IryVnJEBdIRKaUW+703mkKqE+YS2RLSdZTdzkBjZMuSThWg5Mppdi6XJK0LA6Ssi+idprxVOjSxVZeTOTENSI+eTefnmsXESUi"
                    + "yIuslBH2NJuD2ytxrSSw85rQNU/EmoNAWprwJX2ztiXKtSm1ZErKr12KtMQMRFgc0eZ77dJpiQVxcvVfIAICwLaFwflIYBcdvVbq"
                    + "q/fUFEqj2mo3JKGAMSixIEraGyngtfLhl2RZlAY4zU0CuyScYU+Zc+iT8CLlnHf1uoaiYemkFglE6Jc2bslx3UGZBe2lwt9h/B22"
                    + "bxETVbmvpHtOawcFC46laco1JxLPRQI7S7ReChDWJHFPkmg8UYP5aL58hKCUlkqKvEfmyD8aSVyWCEEaiUxyMjVlowOnQmFOlLO2"
                    + "gwSRUj712dOOlJlY2h6AlG0DUT5a1PpUt7eB1Db0JgFoAACwOE3gX0EAAAASWKAI6BH9agXAkqVAonox0bLbb+u2egW8krI9WaA1"
                    + "gp+1vChhkBpd1yIaUvt/DxLY9YzYazUpS66jivLIOMlpISQYuQphXSEoWUmonWhrIQurwHibBP6tjwuQwmL/8mm99VGDubRlykh4"
                    + "+QNPpHRTLfWYlHaSEiU4ju5Lgvylp9wmpVRb6rAcCSnLdZboumRMm+VSnT0CWu4UYG7a5clCarV0tXw0C5lIeHrftSQBaAAAsApN"
                    + "oA0JNNMAIl2DAz40xidY1uMt17Hr0x59QFnTtsRNWGMGuHx3b3LOpE81bRDeT3u/LhBl5s/lWqj1G8bs7HXy+r/PowFEkkFuL7oW"
                    + "5UYJhhECXIkvXVK/tb8W8c/bhpo+e+uvKTeKLLztqik3mgRMyUAl1kGrFYTadOAaEa4mmtAyya0iXc2TqUYkjJw8pWRhKZcakJBX"
                    + "vGtZbiQJ7PIat2VqRunpuWlIlQ6GtZ1UQAfSLWY9epOc40GZ8bDUTY4pUUOP5OiHlb48FJCc1ESF96GFBkr7cIgrr/8HREAA2DIi"
                    + "SGAXbeZH+PBeE37OQKJafSPa160JMPLGLPR0F7xugFXbiNQMavpqdR3G7195/T/XIwLOGUzUKkLRqwv0ECdLxVAq1E16kEWJDx+h"
                    + "RXh1Fa+4GUFANSSwyy1n9RDhWqwYWG7+ljeoZaItfZL1ePq1mkD+gz3biH0173vqLiWBHe0T0T4N1nWT+Lp9LQ3WK7nr8p+fX3NW"
                    + "t/75sKzDG5WJB5z0Z9gWOujD+edyP6dtS8y67bDsUTkHP+p0V8DDm4CJCTtoaxqMyWE/D8ZI7SdNyqDR73a+R4N+uq90MMj0mvzB"
                    + "HlpN3AEc0zTl6XTiruc/H9cunROtTNjBmHP3yOHcGYy3mViSfI9UkABEQAA4Ilx2ksCuZPEv0rev0RGi3IKWIiA52lNbZqTLlRoL"
                    + "lDViaKQb0srl8bgmiWJdkMuv/1edBtBClCPDzeYVxWqIgDppCCUTpwcBWW6wUgGuRNn3CGCpkFisvnuEZlAyqWuDnA4tARsJuCIB"
                    + "vU/faLKgGdo1J1lEPI1q2pV7avVom4UEottVay1ETGpyTHapbAsJQAMAgKPWBH5uJYClhP2Wfr80pNYTqmrxmnPPLEuoU0moa25P"
                    + "Gkuoq6c+i03j6UtpKLLHA7fYBaXP9ZYhwt6yDsvUSMAlArbUBTzUYzXTWrUryl2IEgdbuzE5Cil1e0p9/ZzmERlzUOoqlIqDUe2y"
                    + "WgI77571uTz2XN695zwBy5kEk/97dAHn/v0l40AV1wz3HqgRnlpkwbWcwCV+t8umcOxhYN3noMZXj57sojD42s/tIiBVCnY1Kn5u"
                    + "EudukAirIOoJV5onRxnLLPK38Yy31rfoCVxKYnOQZsSqR6qc9JZrLr/23xABAWDTwuCABHbyoeDSgdn6ST+5jTZzW33Kh2wn5fho"
                    + "/shw6TQd/jBq/mBxbUNN/qwb/hQlIj7QVepVrgR+M05uI0rupB0pNFfa9pTYMrhDx/Obbyah3bl3xk9U/hkun8XEjTyRvgEp12bt"
                    + "vqRsKSnzjNZ7pR+9nrcIzv936Q4J7Eq3Aykx0z3iosctiBT2avzUWvM75z/2dmOIyoJ7ogKBItbQI1yLWr8+otwIbWF8zaXX/of+"
                    + "H659yQatHYmeAAAAAElFTkSuQmCC";
        private static final String FOLIAGE_PNG =
                "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAABBsUlEQVR42u19++92S3XXWvO8534/wDlwOAc4h3M451CoIJeAAkKr"
                    + "P/iLqT/4H5iY+IPGiolt6j1pNMagaWPqLRqjwYRobIUWKBcpQqkVWtJSrVSg0h6ppRSLpVLeZ48/PHv2nstaM2vNzN7P833fmTeT"
                    + "9333M/e9Z81an1kXfOSjYP/kf/shCJKxAACAdgoeI85/W/fEArqHYIO/cS201reTVw6Wumhtti0AAAPA/gYAMMEU/A8AwHrjt3jq"
                    + "w9qwnsUJ0mTnVo5RP379uP+j10/UWrCOUf/2GI7D+utjgUxzGYzmj0w5MqEFBFjmY4KRpWtiAGDy26PG5trCeI7peJexketlvfe9"
                    + "rqk/VlfPTl67Ubl4/H5f/phc+0iMOWiDqB+MEyZmsSf2NST9oE3GujwrfRdE2eR9RXXxxR89vffvWYjABGAw2rQ8AfCflwjAqe4x"
                    + "IQAAdiYCELVn05cINtms6+a3xMay5GYMn6ebegLrvThLbGZLbH5qg08kcbHeOkg3v/+xcJsfvbJIfQAZAoHRR4zxZsl9eNGGpggL"
                    + "Eh87cnP0+yKemXnzs2WJuceEJSYwbBmCsFAbv0QMWAJDEJZkI2NKcAAAjJnfteEJF0WUl/YQTn9+9Jk/ByONNNLNlQzOlAkB4Mee"
                    + "+fNZztE9t+hOu/KBkFJbk2WzwroomAIWnqOgHa6sUbQBTFn5HGzENE6KF+nzMNS/pW1YVlhZf7eCuhTzS83JKuYGgvUprdukKAPK"
                    + "MqV6VvlOXHtHawEsgrU2Gf/kmMdp5oiYjXmc5mzt0h5YDAkAAsB/eOZ7kw3rb9rwN+lGhqIMZBFFC+L37TKimcUJb/MZPPFH0SZb"
                    + "y+YICVYSG44QxP+GaNVDImBF0qOeOEg/SAkRscK+0KxtoJn/P2f3IfvjcL+F2BMCICZjwagdIPrw20LEJQNamOasIRaufUC7tGER"
                    + "lzwRz1xO5Nk5+/Nf2o/m7xMDl92z6xNNLHLJtUHu7Pc+/ReaNnXxg2SIir9QXD+TiBOQcAWS01vCLZTa1PafbrzcaTMpiIBVbFzJ"
                    + "7yUCYhtO7dz8ctyGVX0zck5Js9aleU6NY4k38TRzAo4bcM+stUtmRQDuh/c+/RczQ9IylxqGr+YzpMA2vv5UeJXc71QfcvQ/DwCu"
                    + "nJBN27I2oIjWA5pisIl84QQqT30Uri0kAEDLgYj+2AiwzC1BDLQlIJg3bwps8+e5EBjXDno5A5yW1owaUzwnau1cm5b9bmwIbmLU"
                    + "ltdXrv0cF414yq69pI2oXfd/E/Jf4bzf+9T3DpRkpJFuZBAwZGXT/N6n3pmV0X0cgDxVMiyIEwNKoKOWpZOBgNgg62PHV4BinqfE"
                    + "vlshj1YC7CYhWy7h5zQsvJavzIkINSy8RhSYFOOrASu1gOH1acUCHBhI4QULWAgrVAal/L4n35njSLtgBH49n9iEfWHD5pL8m6pr"
                    + "hISlBQOQz8sKP2IrKC+Rl0uqLZIPdWrY8LWIfAmH6CGH98QFoMN4/DZ9pN+Bgv4tQhEDiNP7nnxnhgtAwQa3xbo+t8BfM2qu90oE"
                    + "ARVEwAhgFC0RQAivGmvnld/gUwVoKNnAtWDbVEHkWq7vbCVXQBGRVkB2amjDKjkDkgOY95i7FhRxAC7/xJN/aQhNI410AyV8/CPG"
                    + "hz4BqVPRrr8CIPzxz//ttcaiHhxKoJw6b8osUCqOE1HehurRGNLFUO/fcRTHpK+JZcT8/8Uo8fVkvJPHZDs7g7AOLSlTqsiJPQDZ"
                    + "TswX8Cq74YLb0/0ydbNA8CUk2syUjcsjpZ8/j4Ean4nWwX1DlqiL3NmYUf2lfqfsCShu1UB6cwHE15RloT31XUrFmVL7LV3ZBUh+"
                    + "xvbBwgQHAUe+qAKnf/zTP/zz/qe+jwQDaba9lVVPAUc9aNcDqCvJ79Ln7Sx9TLJ6XMi2aAy2AGoaEaJ2zWrYf41s3wMr6KWhGIgA"
                    + "USaJCkZXf7nsCyDvf/L7SOqznr70ZuSRfcuWDwFCIJ/LlHukhKJVkaik9cfhCEb1QceIvBQRzxGBqYGIcP1r2pyUGIBU/ragxxZq"
                    + "wECpGnLLRq/FdChiYKAhvf/J788DfBltQuonp05R4vR8TiAlAlJNvlYi0MbN5ImAUREFycdTA1TVnMy12ngSAE46x97taggBNKxz"
                    + "K8GoIQYJCChlhl3+wJM/MJCUkUa6oslINnkpf1BEBHImJRpzk5Qur8CaLyJMSbmyCrANwD0foONAQsrfAOcAhPJRkFO1pbmkKbA/"
                    + "dy9wooAgtMwYLdluvD6TtWS72XXwVH9dRmtpXwBYVq+NgUZ/DhOl8uyp01rLz9tiRmkt005J7ZcdB/HM4ClLdPaXMt661qoN++Mh"
                    + "NAG1ZOBU9gMv/ysCsK78gefYRX59WmX4VrYelfW0Ykj4bqyA9ZPKmFr2toZtbtX8q73fnyrbnQp4hlb5p0Vk2QJMDEHAihOfyz/5"
                    + "xF8lwDpbNE2sIQLprUMNEUDh5iuBiznAD4X9g6A+ZgG8lmQFbdYAZlYgf0uVW7j+cwpGLZum5+btAWTWErhcWQOdk08ETjb5pxza"
                    + "77usdbSRBwTrAD9UbOoSIdBu9sKM53XybcpP/gxMunFm23f0co3NZlaV2Mkcs817YF/vyhP2/Da2zzfRh7l+EIs9fdyu5vT21yF+"
                    + "nlPq9P0LuP+77PqL5zwxmX+np7rWs/EP/Alw7RHjXsbr+TYIv5V0rPH76coBuE/9Q0/8tYGujDTSFUj49Iev2fjEwvg0s+lJhhSb"
                    + "bNGrhfDdX/jrWUeSRsCAGuaMSg+HKQJ7UsZyylxQTQRjuQKANgG+ZN5/Kft/13asSciNK1X/oR2bpl53fY+3YC259pNA8289vSwL"
                    + "BJoIPFxPGKJO4lGXAPlgYvm4WKRETB1shhZvtMYceuWD3+N1ZXwaJN9n7HwUbXZe1Hwob8jx2CRag5y34UQbEy3CmgHC/1MZ+HIR"
                    + "W/zhJ/5G1nIw/LiRLUOVKysCSdlvCTCIFew8CvGGGjEI1ex7/NtUAezVgI49gCupKKPFAaRKSr7rslq5vpduQA1mkHtH3TGAOH34"
                    + "ib9ZGJQVDt4yeIAVyPCgIAISYFDFZFUQBQ2IqR+T1G9AiUi0AmBacE16mzCBzhRYo1lXs17TRgCeduzUGE2LvF86+1z+yBN/awhb"
                    + "I410gcloNze3yUv5I48PIjDSSBcHAr7yQ7fYopxp02eYuf7CzHXad33xB0hm1EA+Uk8qs8ShyCgwLo3eQ/U9BZKx30bYxwoASp2G"
                    + "RlpkSIUs423iJgLI5ADAuC+TAQDdGykBUkkdtAmYRUW7KYU0K4F9/jNK09EQoNvyw0SMtQBqWgK0DF5lZh1zICKWQqkBE2KMAi2p"
                    + "NnPtFbQ/l/cXEgAf5c8TgNB3QLrRyVsCOCkCvONL359sRKPwPFzyHUATgAk4D3tTQnBsto3TcuRt73iiUiJMQPw2CQjA6Tf/7nya"
                    + "7dUtMCh9IfwW52cAKwlACUWn6nPh0IKP2O+PQOwXPwOmvA7IECksbDjXjgGZ74AJUn8IpTHk+maJYmFsm4OAVProy35QACrllUBo"
                    + "QFB6MwBQ5xTU/62gVVIFDHZh6oL2KEefUuUgSQwBSouvNbBJSePPVrYnAeF6mQZLblEk5XqpHXNj66oIpMkfI4jASCONtDcIKHEG"
                    + "It3YkfOQknORj730BwvUV68mXD5he1ztcUJJCUrVjCtu3wjLEZwR0DoCGpfj2pNWqnOgaVPDhUg5nBZVadtpE/Y2GtL0ia/+SQEG"
                    + "wBqmRCiARaZ8iAHEgOHbfvUvJ6/UzJIm/yn6MiSn+hJruuV+T812Q9kfsgCg+yQm4qabNr/lQMncuHwMIsYGgMAGJh6AI4Ati7Rc"
                    + "jgKBbeLApwKI5ofjthnfgekIpqQ/PwoRpS2HhjYJLsncZP+Etl8pfDiHh3B1tXI/BURS6xyChdDyB4iTL815X4MAH3/p3yFesBWd"
                    + "1FNG/u13Akv7wCxcKeNiNHMo4RBYdUpSAUBKUX653yRKRyVsQivXauXoWlxgaui/pj/tuEUYwKXIIh9/6d/tRARaRADsQAhiMcBs"
                    + "APTVg4Lxhm51FSb5wCmiMFWIHFPDxukZzadn/1NnIqYVAUyNph/3ubdYECIA/CeCCIw00kgbgoCtmxyUm7z0+yfOSgRmJjXyYUDZ"
                    + "vddxDQrCutj9eyvl/CuQ5RFwAyZjCdkeoLjpWpTs91V9Rn4NKBTZDyXvy/hxeSR8A9BrN4/f1cu+c3q+lK3/FJXlTmpqvjl7fsvM"
                    + "i1oXaryurrlEqvSJl/498ANwUIo6KZgXP0PGgGgF2XgfgVIZPBRCKJElF1Kc3nB+mGzK16EFSiWGXoPVR2HgSw5PChNTHJqaZcHL"
                    + "GoMWAI4ZsAuJ8OYuZFUQMnv+2w9rReEYlO+7yXuridjhYuP5zjMIf39+8sNqxWOY5vlOxLpwIb+D9ffX0StDhfEK2qP6igBHG62B"
                    + "ixVItWOkYB9tFpyaAxdNid15Fv3mvnL3/0++5F1qwpFzK66X9zW/9VLsKV1RauMQ5nmdAh+U2f552bIWsGqRrVtlfy3+sccYerd7"
                    + "IloVIsC50icfe1cGEKwFRFCwYTWuwDQRgCRahBKfgrkAo/LbDU1kXo19u9a+v9cm1d7N+6d57xuDXhp+W7TrBwjZTROwFjD86cfe"
                    + "BSONNNJGIGCvzQ2diABV5lOP/f0Mi1jLxu/F1hsFW68VF+LrxrhdnzMo2y7UxMNrCTuu5d5aNPBq7su3nEvL2knalcQF7EYAtuAW"
                    + "4rQSAVtBBIQsMRtYJLdBfAAQIwCQ96HHAYArwLMCgG4OlLnxCgAeCaDu6LWRAnhI+qxLgTYbgU5UoIxgdSJgkQwuQkXL9TQB8y7I"
                    + "Y7hzIq0TE8ASbQCKTQygSINr8Zqk5bkAIEe0pObfEhQmmu+RABL9enGgFX9MyzhtOoYjrqNegpNcJXblU4/9g0pOAKDeHoDjT2pT"
                    + "S11DAIEowDLaT6CSsXbpZJYbe7edyFpd/R6KPz1dfEnKt2AJ8f4xwjuAYshwZJ9iUEcmSLh/pX9+5rEfGoLbSCNdEgZQ656yFlv4"
                    + "z4/9sLyPKECCTLmnJXkGVbMyTxqswQS5hzIROReDAMaUGYnKk8TOSkF+jpVg5sGdgn74z6gAIfLJBu356xtzAP7v5Hpl3Nb7sIlr"
                    + "j/pulkAshq5Lrp0rj/a8BOCqUq5PPfbD8wdgFWCd1kZAgy30ZPVL9SWiABaAxz6vvsRus9F7GkC1nqa4WpGoVpehB/DKlfXBPm17"
                    + "+MYP3m75DylCyNgNELkKs0Jf+xbTICScGbL1jY/Xv9/wa3/Wo2SpJlzsIiuWSFewjXfdNRXdf/kBRJCoy0fdOwFBkwc+HklQLPfp"
                    + "THA8cRp2IurSfgzTNvMOuyfCRDcX0CTuKw7CQYKADpxkgL9FJTYyPSYDfkR1pePkyK3UTx9VLmu2S/zfMJGL4xN7yszBFHwQAtqr"
                    + "zQG49LOP/kPmdWqAPWl5UABwUOA2cld4WzByJUHNdD0JW0BATbBQrn5PLboW5R/penIn+rHytJcChUYj3cu9BMhAQ2T9BdDPuFb+"
                    + "y6M/MtCckUa6BBBway1BruynH/2RSpdirbhAjVOR0mluhJxFLWfTz4KRch5iG+q39L+1PUDP9dKko2L+Wi7EXIrqLyjqcJ/8Zx79"
                    + "R6Q0O6mIQAELqSIsNaCfaRBZKEKinbce1CppCNZsdm18vdr29xIHasdZ0ujTvLPAVPnNH7xDCAICAOkGjAb30s8MM+WowCLRc0v1"
                    + "R5UDeN1zfyYjhdoI6KMDdoQAGybP4rb9aL80OMgDTkv/QXATvq5U6299ZhPgMZ1Tiq+7KMs5k97wvU0pFFsAylj0ggDbgqjCJCiH"
                    + "RaCOihdAXcX5mGkOAAx8DuZA21zMAKKNuC7XLmbA1KQfB/wxvgtvmPTpR/5xZU3pSVvS79+O5a5P/tzKPgSpZ720z6TPe4Fq0NhH"
                    + "TzuHLTmSGpDRYFF7LwfiQVHzD0UQIETaghphIOUeEAA+88g/GQjPSCMVQUBJXIDInz8o62CsnkU5qM/kxZGIpB+PLPzcI/90vOGR"
                    + "RiogRTd0WolAqwFPzMZLtOlMB1GgFoSUzqlfkuoO2I3Yfds47j1Egl4GQbk6R5CbA+NbPnCnFX0Ulo/4m4J7QIODCYgIjIZh2i6y"
                    + "oGG5PgLAa5770wtLkQaHmCLgJPSx5+NlU6BlHoJlKahGS340AHlyRhoCkVIAcErAvsXUFI8JpubPaSKcf61rMUW+CPlL1kTbzovY"
                    + "u5i2RiAVZ7qLDKglifjLlbMUCEdp3OWiCxMBR7IBTwvjnYh2QVAXMwAp1wY5vpuBA3Dp5x/5ZwpQr3RaItD6+LUnsZZpMzud7Cbb"
                    + "d2x00+tU5jT5ep6+kquyPbmFLWMAFN5w/Y28BABMIwnFv4JYuxAA1P35fX72kX8+hL6RRgpAQLh87T+JEpC07mcf+RfEeWOzJsP5"
                    + "09pkWFFDj96YNbt2TQMzFrQVH9anf0RWu3XMgDON9c1vZ283zh++835jPfNYlc46weDYyNTWN/GlzHO3kNclp30Sz4AYb/B9ZOIV"
                    + "BO3GdZ0ptVllfD9eQLxe6/d4WiffNbo5xybuWb+mjV948b8sbOBazwY14F1vVWJOVCj7BKwTKdI2pd51evrdK23SHqy0xkhKKh5M"
                    + "nefaKuTdNCklAih4AVOyMULT4dDpxQl0MRGWutYL/f6lUYlTtVwb9OWfDKe2kPBriOympYKpxAEslkz4A4zXxl+faQ48MnkAoO/L"
                    + "zpI4M69xN2X8BAb+9bw2fPDOZgDAxRffBPR8XaQezx/fEuCD8dtHmfsmaxv59lvGFfWf1PWCiOQChsQE4zpMcD1aPXMuVr71FK/1"
                    + "QsQTgZFGuhkxgFK0nyXqTyHiz5JLZaM6gLOiEBLZiejoXUOWkAAPKiTnFo71cy/6V+MrGOnmJQBjCcAjAluF9ZLK31Q5Ca+DF7em"
                    + "lFOPnldoJY+5W8jQW1ztTdAnYpAmdY8MtEXqPaZS+V964bsFwBcqiUAvoE1TTuMevKeWoR5g3NJOv5bY9AoR1ou41RKbSfHWRprT"
                    + "L73w3UxE4XSDWHtMQLupsOwhyHXaMGkgEurl+qEwpgQoo02BgeUkQsAOV/DP2rmNeWzWHy9NXtMoyybRtHTBLnzuIGjDReuFyGcd"
                    + "phGCQ7wsBOR8gCyQ9YhIyMtYppPpL04pCLlcl0Go+ZeUgzCoRwL82QKYSkUS9jgoF9TjGAN/yPQ113OgXwz++WW7E4At3Ivv2d4v"
                    + "v/DfDEo40k2T8Lvef7fMIUji6CP/b7QS91quXYCsk49Ip688XoS8TUI6Bozm9oqv/CniJJ6IM2yKrucgOaEX/XzMOSM5KdNMpOkG"
                    + "70U4/wxIZpAeR+7ZMcPVTESfqVOUwIPwFL2JjLfgkt2A37aB1OttXM6wKxvaM8R2A6S3Xy60GjEGzNguTFG/yfeDlh0DNZblFTK2"
                    + "AP5zc2mafr1l+9p2//sL3yOUhzUeeSX1KVmaskTsFWS0J89XBxRK5F+p7HxOObw3drFHPbU/gFofANmy2g2b8TPAtqsZw/zs8w+/"
                    + "RwmUoWLTlDYvRwhqwEPN5s2ZPhu4BNgoHzi0P1jYo24rsKcN+qGBbkfKpM8//B4PhCtvNlILDKfQ7BfiSMTHBezLtz0l7Hr4DL3+"
                    + "l2BWp+ceUBaOgxpb+owDJ0P2EsE3pT79fgqNRn39bjwO3DoS0XW5KEKUOS744F0EyiXReSGN9mtikMxbMwkA58pM8xhocXDdpJRm"
                    + "HgViol3X5BhrRLr1mmDJMIOX/roemcjFZu+Q3+cILd7a5hce/reDEo50QyajifEb/gaET7+cqW7qHbjFz6CsPAYuSNJ+c/MJfRV+"
                    + "8eF/N76WkW48AjCWQJ54ItAjEGiNIpAGgNPI8X45PPtnk5Ofe4GDW467Rzs90nEQgB5E4N8XNl9s+x85UVls1/PP6M0Y9kGGql5C"
                    + "jmvOADPXTUOMh+HM3e927p8aG0dg+umMTpG/geW5ZyO/3DBEocSpTbnYybvfiSkkZfyMuGRyvG5cTqFnzpR9/mLP78/BhGPwsz9m"
                    + "l3M0/xiVNecOCbYXNtBTdfmLD//ooIQj3SgYwPljA+IVWzQEgC/NRGBV3KFJGuXkk3LEmd4ArO35aserso+vbLP6HVhvAVbSH/td"
                    + "db+HikNOTThVYFrLrCrGFoFUa3WYenDrMNmEzFsiio+N1G7jEQR2/wRa7vwPmGAGExke3ALA0VOrjm8VYvVjqp3llPbWYXJIO6We"
                    + "TLD2cZuLHwWPK4jVof2bC2oMR0Lt2DK+AwxthpvLEJroclmsFhT9FvST9rmYECcmv0CYM0Nodgw50+TI9BmANY924/nSQz/Wgc2t"
                    + "De3NiQs9yFsNWZYoNMnmXus6W4IZ9MYXJG32CrPu6wSU3H1Lx3AxHEAvTmHv8Xz5oR9XbDzsAKphR+imN+9loKxEZDYeQxtB6bGp"
                    + "tYQGvA29JWA5QMCN0pcfeq8QUW89ZSUbWaJ9QY1Fqo3Y49PhVJ3T/ii/ApdCLLZSE27hYCYBEejuD+AqcQhbcQm/9tCPD0o40gAB"
                    + "bxQiUUNAfv0FIRGwSFHsOCgiZC0AQ+u8FDgM1XFzln8+iJc+p4HIEHwLYB7CQtBZtfkWgisA6I9pDccet8lZHlpLW/clkyiAf5P3"
                    + "x1+jHGDHgYgAsKjpxkAkBZD6vCAH4s2NLm1jALBOic8JCgwlHZAyvgPMdsq8FIvaW4EYlPWgoU9ZX8899IEKWV9iAVgjz1/q/YrU"
                    + "MhJIcSBmda1CVOgN0LUClpryW4gcNyUHsDUH8dxDH4hWVoa2rwo36+UMmMOaq97uTFwSHM4p//jBQjTyfis+gPOcYoWoAxl4RKTE"
                    + "aOarRLRRG/4a5wOJrAW9U91T9IkVfpIAIJmgHMHmdm3N9aiAIv7LmZjxujpBmLao7Tj7azBAwI3Sc89//4bIe41Zbk5rz3/ORDNi"
                    + "n3OErpfpMN/O3rb6LX2Xykuu9nL1ajmRwQFsmL/ygg8OSjjSRSf8E++7z/Kyeu4Ey7vuotEwYYjxbMhwok+Fq7KgL8u1yTzPujkj"
                    + "/j2P6+Gv/rEAJAu1+KaA46Pdi1HahMcIDDqyy55qAlIA3jHp1+87BJGoeUSailPkxBQzIB6zHgl8GmkNxk4tLdosgGgL4b2RcAHG"
                    + "ApHODVnBbVgoBvBrQLr5YoBIW/A1gCXntCEw2dv5lrZ8aVNJwDsQtpMjQFLQUkrI1jq/8fwPqbCA/HNOzm712lMaX+mZKWAFubFJ"
                    + "0BW6De09uNZHv+ZeXetmbAvX4zUC1kg7pBMRkMjNtRu1x6s9961Bn/41MQG2kPe3xBxq/B5mVYHH1twv/ebzPwr99PVbgLZeNgs5"
                    + "LcfSLYG5iE9Su7G27L9lg2sAwxtaE/DS81ef/5FBCUe6HBDwe953vy3LxDkgTgCKiUBAH9ST4AFx+Vw4LMyAehIMQFO+BE6e/n7w"
                    + "t/5IBoiLAZtYG3AiTYrTejYTechGoNuUAc9y4OGstYYTo0k4Je2s45mSthAx6YsCyiwes4CbXxcJwC/nu58LXR6AjtSYYl6GMHXG"
                    + "uB4DAhpITaHj8frjyWkrxm34MQRMvVf/ErjWot0HoB8XbFS3J2C4/va15/2Uom+BBkxWm7CXbG8KYF+vOvHYtYpIdSyz5B6+BiDc"
                    + "Cseg2Hpt2wMDOGP62vM+BuWbl9KmMpUbAwttmkoCsVWdGgKzvVwukb99M9+towBTtxJ9/QHUBAmBHcpDQz1lebDCTPFkUf7agx8b"
                    + "lHCksyUzdPorgJPO+bcf/CklC96LfW9B6yX9SEWS2AsxVo7HdFor3Ulfi8pPlePoeS1pbuZNfUnj/vqDH2dAOEw+gRRsM0Gd2Ocf"
                    + "7Y/OGaOmn1PoI4+OEBT7/suZEqcA3DFpJ40yZNg5WETWz94pPLkXCelkURUAiS7i0NEz350srfm3mNV6dY5oT56HozDeyfrFJrqR"
                    + "ubFFC9ftKfsyPOXnz48StIRFB97sGaL6zlfgMY0MJAm+gYVgIVQ9ENbNtcH1xiP9moAh+mAjpbGmwUXkGpYAv/PgTwtk2pypcY08"
                    + "XZL9t4gHqJHbe3In+yXKd59Uhq+R8TUp0AMYUtBlpd958BMhf2Z8s1YJQNhxkxgT/ttlkMcfIMsZXMydfRPoNc4AMY+kf2fSSxAw"
                    + "w68F4mHOuHITc042U2H5JkQaLCLqOX/9NZGJp/wCL+bCLruTnqPrvumxuWqs/M0gZnzDJwIjjbQlCHipA7vZPQ//3wc/Ob7OkXYg"
                    + "ANIrrQTpqKhX0w/sMD5tX1A5PmX63Qd+JgK6LGkuvII+E6yBN/IAIEf7AwDONwWe1uwAtbUdwwJQrlzo+y83h9Ws+FR2mnPqY4+a"
                    + "m68hGPjFW8bignJP5FjBA/oCEC3yq+feRsymW5D76fNDfbPgowNZCaAyAFY9OHWZhxca3MrCg2MFAFj/R66h12p6nLuCSn+vAwwl"
                    + "UY3jCMkZ9eb5/9988GcVfEiOZ5G0IQUcNX1swWxKri65Mgcv54X8Wh9+W4GKNebKUAAgBwh4BRJPBDQbsoVQcJtMqoJN1au96z+P"
                    + "lFvjTLRFFVg7Nkm6CGvAc8j5NwK+8XtVRGCkkQrkce9NeI7NfqMQlN978NOVpKaFcyix1aU+LoHJLOkdGOhjC8GfvDWncy2Hoqlv"
                    + "rvppv+Vmhx0IijZ964HPMOBdCJ6tIFkYROQE3CEDwK0aaqc8tzWtWoFOMzD13WciAOtU9wQArpGSQ7NkBzbaNPhIFIk4CRkWaAt6"
                    + "uhIEaLcCgMcAlSWDgCx1QnPkVYNw/UNt2mANC1p4QEChHFi3bnQisIkfYAROZsiGCAxCzXdgAFcwfeuBn2uSnXkFGgxjCWRIX+xb"
                    + "342Bfl46hkIln+VoCsYjPNSJZ+yYMof+qjB0AF+BqFUeTyIZR+MK4gyYNTsCQ8U1gDjmgFkVj0rrYOpUfKGIfpfVckGAoKdtxB+k"
                    + "To0ZsuONEfnyfKGo4lxyVippgxr37z/w84MSjnQhEOmOcvcliyhbrEMunYiA2fAV1wgqNY5LpJyMRE7PldlW1udO+VKZFk/BGpVi"
                    + "+hbAVtr4E7m7MpBXr8oHAaz2/lS7tT4COAWf5k0uGWNU99ukODDSSGfmAEbaL337/s8uAKAPrK0ngSXBvhD8Ws1+A623KQ3s4TQA"
                    + "nalt/BlNHjmkA19MHoDna/a5sRzJsZa0AcO+1rMvjMNLrQG1ZinYNsF1BoC1pObhcvJ65sMJvSc0BhcQcYIlr6fPmq7DlGoU+uBh"
                    + "fJ4QGoqDANwg6foDvwDH+38xALHWz/tQpPVozQzuGUDf7NBZ33nPDJzQ9hBQWgmB8fpCazzgMT130K5jc0XWZ2YB4ZI2Jn+ec1l7"
                    + "IEHOdf6HCAjViigH0GgSbilCcEl7jWj0dv/tyr8le/t+qr8x2AZKABJI9d0yYMfPmRo/Dy5yACQA53jUJwIjjSQgAJcB0MEG7ZwT"
                    + "1DxnO9NCBEwFCKcF5nrV38vBx9VhejkA76IIANwAxONGIBjJx3P/L85srru3D8LN5zeCIRxsmJCAcHf9q6OP9L46vFtn5ks4EEFP"
                    + "0SfUGeAVAXzR4PR//7pcchsgZ/VjnQFfH8Kf/xQ57vA3t9fYOlBmaItHIMTT3ya6+5/rJPYLkU5Bsy0AXHHi0Xuz7kUwpPXt/Z+L"
                    + "AD5fw84DvxYtuthcdxW2/eAergztk2/15Z/6+jsuOQXu1nHFoOWUkYitPQbabjQ4eEwAztBH4DHxU+jDZ+s8TAThQQIc5kDEBDic"
                    + "x2GY3jigc6k3a/wFfgLRLjt+aAKOBPDAf4U+3oR7sd+97+Al7WkCq/QSVXwOQs/qawC/GvPgVQSwCOUM6TMQlgt+8yAvVZ8eiOZ5"
                    + "lljLQL4td3LauD4xvqg/yneBRutwJe1IZAj/Dk7RiKf2ypLvgoAWXR2875cHIRypPyJyDrZ7rz57sejnFC2C4FqDCIx0pSHRkZrT"
                    + "4f7PC0iG9JOQkK7WMGNbOAeRsOZGOT4DsZ5BuawRiwXTlgTgKkTVaQXqLpVbqKnXTgR+BXwtvSRYheUiFJvAR19Zrg2BRFr78BS4"
                    + "ww/k4ddbQTTe56BvvruYRFsa/LJIzSscs68xSMBxEJsSO5PnU7kjCSImY7Y2ACZJE99I63GC1MR40R708zRjA7FPQw5IHOfiTcoJ"
                    + "+Ga/iektcVKZmUSZNPv2+KwZsTFpBhCZD5Pmy4z5bk9w0b/eO7W9Zs4cer2CLDE1rp3176Ae8Rr8q7z4Om8xFzarSbFfNsgeZ2HK"
                    + "GnvQoA8IAkeY5fNO12MM1EEhMlCqq1cy/YVkZjIHojHAJzGVBnYVgNEYBJCEOD/c+/lBCUfaxyXYnmDYluz+1iw+nK2ONlSXxCS3"
                    + "x5uTjKOJF9oQBjsQWYN9HC6PAOwlT18Ksdi6PDaWbyUQt9z3K3DLff9DuFItUYK3xKAlfgFgB2KiJQo1RKSc1MZAgwka6dZ7v5AB"
                    + "AE9+AE8ad8AChO5TSoGzUMUhBaUMiXKHGoQrBkD5+nMgYwoM+pGSV4KwPo/BvpNOnu9XMQUMnb4ewrT4Vlx1+FJNSg90CzQh1zoh"
                    + "qEn1PQdHQVMOVuL9FuMDLhJx4D+wp0OQ2GlG0WEH4WRD4ujDB2VVzkp6cQhWMXbqRFbMlxyTwlEJN/647K33fGFQwpsTA5BCfADb"
                    + "mA4DCZdx4BiAJuZQDNTloUMZYw3Jv3P+EvmysjGUohCFNSRlkSkLcPu9v7rVZwZ1rsBqcYkeuIBRlPdZdI3K8XkY8OgWoL9sfu6y"
                    + "sHHZ3qDkFoBfbdntiMBIF8kBjCUYCYpEwOz8SW7pWFTDMWhPbLPBfEvA4GEQgJG2IAL/cwkOEgN5AeAUaKI55ZhZWy4x0T2mwBiG"
                    + "rsUoECyoE4CIqS+/QDMQ0/Ys2lWxxliYTCbiLhLBNfAEKPpKOykweVJ08pWj0nbcuGwEPBqi/FoWEUjTZzcuChgk11GrCXhu/QA4"
                    + "U5uaNahNPfqHDcreec+XByW88UFAWXhwzbbK+8jjIEXaSx5ky6YBQzT+BiVae6W1STUWoTBDgHJYcAq8BGGAFMp3YAlYpPo//f+u"
                    + "e39dyQ5LjYO2Zj6NIGvEih7jybHtkhgGObGAEhHK9U3TlR4o4wLE11/QcI1o6wC00rWe5HqOPD0F13LSq0FRnATBHEBylerPgyl/"
                    + "1z3PKSVIDXp/aYi5xnJvbyS/1RtxWu+s4cF7oOe9Wf2eaH3PPnuIFLXiDALAPXf/rwZQricItsUYtiIakhO/HchrGe8AAUcSJ58I"
                    + "+Jp0vtW67zvQ/9BWbb4YSDwGgJ3fRgJaWcsAkamvQkqTz1IRdycGAPQBSxsGKqGCgMQ+CE/+Fa+v2YasXqr5txKLWOMPllWOTYY9"
                    + "U+rE319qDpyYR1u7LwegObF7cAm9T/XeYF2vMj05Ax6NSInASDcECFgb3CPVYcuDZfIAHDkQUbZlQARplgBLPngHEOBjSb+Pijgc"
                    + "ay1CVAaZoCKQBUJTgDEXNAXYQCThr+u/7r37K2Pn3CgEYCzBSDXpvnv+t8dmx846UpnWOdBI76k1YB9RJtEePpD9h85DnL7CYXZO"
                    + "QrUTIvKIJ9ZcFHQYqPn7cQnKU6ViKCROSPx4DW7ey/wPxDMP+Zvz7iBgK7ve8y6+diw92thCHNhDP8FP99/9m7CdmfAluvrWEqxe"
                    + "cQS3O6cHBzBSU7r/7t9IAbnARNgEIFYIzDktOYjARQ9M83znJaCetWBtzkw4BPdW/3qr7z9Ss5AA4ajowicA7xiNy+/T9yE4Bz9B"
                    + "Z5p8AH+YYcASykTYkGbACTA6WYCJMRPGdG5GfGefuRNvMg3uDMIVTYKZe3VQtCG5W5eMgTMbLrXD6lQ0tCE1l6bW/sQJjHRDgYB6"
                    + "rb8aELEM14We+3iz37JZMIg0DvMAWt53X94Ut1wfsnPl1pyKOgxZf4n0rABKZs85EPGBu7+6EYOqxQdaRA+Ofc8xyy2GOdox9Y+m"
                    + "ZPZQ7DkXLtCrfg95eSu8oVf9Huvw4D2/dUVw7S0Vh/aIwExZBNZpTQ4MYKSu6Xl3f22H0/lcRKXFp59GPbqHua+sjU2jA7ci8S39"
                    + "b1kfOsyt5VTe+vdSmTIR+O1BCa8OBnAerb8WsQE6bd4t295bXNBsWK0moHb8FBGY4HqCSp/Q73zY8ORmwI9ihB6CTqL5kYPQ2AY/"
                    + "coLqqxPPT5abglMb19fMODql1JZdJKCTinAUiYlQz03bck5BI3Vnf5wL+p+WWW4AqPDgek3AuhAhmvoy4DHvNS9vDIxCkK4UcASK"
                    + "UGYOPIMEoMyZL0NWg1A2ZiQ2rAR0pMFbro2VCHy9yylFKr+YzJG2RDkKI/lQ7fp5fQ6z442ZYBi//1TRyJX3u2CjHTGiejKOQNEo"
                    + "VuQBuZqEX8akykEDAxhpY0zg64KvVmq3r70Z0AB2Wrv7S8ctBgg40sUQgf9TAQye81PXgm/SiMOtAF9/02FTo/yDAgcXTfK7VpHH"
                    + "HzfwTjLEyj0gVzACrYJTy3wCgTXtu+SAZEscwB8XtUYvuOsbgxJeFRCwBeHe6s6/FXzTttsDZe+Nru89VqwEFrnfHrrrGxEAxocN"
                    + "pwFDH1jj/QSEkX/8CDxxZCAHUObCknt1SLt7CNrhgUEu2tAhGFPQTwBi+s5APQ5iMqE/BA5U9NfUCwxg6oC7PAnQeOTTBR2hTXbL"
                    + "UXz5z5yK7JvTPAQom/5S5rw5zclcZGIJCchpFlJRi4EZCQ9OQsH0Gxi9zFRL8eG7f7eCLa9x3y0x0tlCDGl112UIvEFTVycmmK1O"
                    + "8h6nsOSUrj3Ztzhl9/gNKuYgZd+x00lf6u/hu79ZuXljxZrem1YSyFQqw8ebUivrS7EFCS7Bj3mAgCOdJS1EQOx/E3lML7j6m4kO"
                    + "gucr3wRXbNSV3fq7Se3ul/4PyRjCPg7h1eEyJktONLD3J+YQEFE80Itl2gie2UI/vydnANAPL2jBEXphCND4W6+x13I8NWPkxvOi"
                    + "u745KOElgoB7BPpoIQxXQVzoDThuDSZKWf0eooWfHrnz9xLQzHcwumrhRZF1Zi0+Lox3GKJ8SkKC++BfCJYdvf4o7cD1uiN+5ms7"
                    + "Ltp7swYflVitQiK6T+hLYQ36HWhUIqRahH5bs7agi4g0GQumH0bvjyLODoxFQZ77Ccpr6vvtQDQ2bRtI2MrH4wFlO4TvPkvNF6Nr"
                    + "PWKNWNNlAF77UGr6TI0PiLkDMS7IjCGd1yN3/L8KIK3Wi0/Psq0AIGXJVyvf16MfI4109vTiO78lQPd73gAcNiQGBtp8BLQCmQpz"
                    + "4EtyB94iGtSw5C3seg0C3xNDkIoENbcGPcYgvRUIicDvD0q4NwbQS/beQ17vSRRq++85Lg2x6PW8x1XilsRqEIELAAF7A3PnCjdW"
                    + "a1Z7LqKAHTd4b92CViKmef7ond+egazJy8cUGCRMcleQLAUGSynQoAvaPgbgHxBag2HEHje+Y+I0lAL7YhDS/ZtqOwZMkza4Pj3w"
                    + "L6sJyJm8SvwEppFp3YuVRAemnpcDhkBBJw8YA14ugi6nhZcPGEKZ7lK6iLyvvbxWITIafjVzSEE5LuIwDSICAKlxST0HoLQD03bS"
                    + "wCeP3XU9L9tH9+X+Xf7J627K68bIeHq3DvRdvDFL9u/9436DsUXmyA4LWOqyegxpPABdYpR/zDUSLhgg4EgXm15y57EB9KMCdUo2"
                    + "j/Z2QQsq+n1VbubqRGgCnoMFvzS2fI8+e7HcPZ73xgtqWX0JaEgTgZH6YQAC019xhtXktSXWAGViTJm9asxzyQ9fOT4omT8LxgiC"
                    + "mAI9Nxn5XDhXKMQsSAVbWQwEDdECC/CSO6ZWXJs5UUvt1N7ra8u3uiyvFxPM3ld8PVH8HteALeCd5pTFija25A5aNQF7cAYSDsA9"
                    + "e9ntNgQGbajpt/65TgKDYflVi47S9gt8+OGRBROnJIJP6PcvBg5TP4GrVuPqE5HSZIzBQz/seBxmnE4xSLlGBuqi6V/69EC5FbVb"
                    + "n/e1Vz8fyRw4sGyrOeSBxD5zkI4JFesgaaf0DODxOwB4N2G9U43srVVKquU2hibgSDdpevx27MAW91D3rRUNNJqKmjnVBQoxe9/X"
                    + "bwHOaUWIHIvamxUvle9h4LPFvHuuE3QYn//bE7fjoITdQMANZH3YmSi0ovU1Mrt0I2o2Vq9bBI3srVXl7YkNaPqL0xO3S64ABWOx"
                    + "oX0+TPPdPhU0Fq8FozFwAGvt6mfAOn8DnE3/NWfoeLrrtwe2vElmfVjGiNb3e+D6zomPAAauLZyE35+p3WBbgoWtRGHLzb8XaLgl"
                    + "l7LFFWPr2DTcwkoEZrgMrefkwwf2fKUds4JxWcNNA9YaAlBLwyifyhiwFhMT3lUpKeOvjwl9HvootMS46TkkoCPxe6wMZTgdOYmf"
                    + "P2gKFgJAa/fJNQe5zyfXW6ypRvsEBHH/OT1ETuOuFLVY0n/Or2EOSEy1/uh3ABkfkEjqekJWI5IHACEqR7XLcQUIT9ze1032vqnF"
                    + "3VcfcHOAgCNd+fTy265tIR0rAb9WRL42VHhboBSxIpBKmQfqlYlAoGSkHSdIlI2Y/kH4jFNw2YoFpsYdj4tVdAKhHkDH+dcqYEnb"
                    + "fPlttwxKuCUIuIVMXosJaGXFWmS6hwzdsma1894Cr2gt2wIYSsHCJ28dRKCG7xhppBsmPXnbbSSw5tj0FRA0ITgWRewl61pDaw5i"
                    + "HIzk1P4EGIJ4jP8+tw0nOMIER4+V5wON+M+5eXLBQXwtxEEARrrh0lO33rbDubmF3n7cbqu2XxkbaAgPTuPRdTcIPiuXItXle4C6"
                    + "0fIjp8Niy575owbhTUbKXJduLHLrBQBkVB7qWcho0z4T6FhMfLupjT8UoxbR4wh7SX0MpMKBK/v0bXcMSrg1BtCCFfTUJ2h9Votj"
                    + "aHGIFnn4HGtQi0NAp2cgkP9z83j6tjvoIB/ECen0CBBLu2U9ScNgIoW6wYnujd8TKXznImRgEnM4ZY8rYMsvdTB1UGIOPAbQc9Np"
                    + "gLk9NnovgnDuTbnHhpRuQIA+wKUWxJXO4xW33g76azzplRpXZsuwYS0iRlrPVF+hSez5t7piBPm1oHgM5yJWwqtQSfhwcg6C9ktX"
                    + "cEUilLl+JJ9pCZPw2+Te4StuvXUG/WwUgGRNRf97eAr2EdbxNfbWjTjB9cUsOee/z7URy/qxia/rm4tMvJb3XZYBCQLG0ZQHCDjS"
                    + "TZGevu32SlCt5rRudd1ldtuaphY4qwHgpCBe2elorDILKpVfuj2N6nF+LUCligwiYC9VlU1BvFR1l1I9ljph5QDGshovD+5iYWzA"
                    + "QKNpOWodSh4Vnrl1AIPdQMAaYE/KFtf011tW3xovgI5jb5GRpZZ5W/epeVaLjwAAPHvbnY0nbYuDkD2TzKeA2RLt38qSsPZWAToR"
                    + "pZ54QS+AdQu8ohY07A0C9r4xCInATc4BjCUY6WZMz9521wqioQHEa0ten9PRgX2QL05TZL7rruAC34KkCa9vqpuaM3PmvGGOtAyp"
                    + "CMFQ8Acw0kg3S3rKPLkzS37O+rRYYFq0/nIwmgzEk9vYl2z1pRqIaSybFGSibNtTzT9kADMgNNt4kCvXF5I2+NRaQwbOowBLic19"
                    + "Dtjjn0FWIxEARNqEMbQpBxF5/cBUFLjl2lfglbfcM0DAXgE8tgANe/VVK9e3yusawKoVwOwpp2vb7okL7AkOAgB8x7V7mJOydJKC"
                    + "ElDMKRpJvQdz4F4dh2CaFX6kATRaFYAyyiqtBEENBAoVakQKPaWNTrQFgr5yikLkOmTeRVFxSAuMMvNgfQ/UEovMNxavz6uu3VPB"
                    + "dnMIf42eAUC98c+BGM9B3PtII40EAN9x7d5QA89eDzboqvkXRwi23m9mBuuOidYhpWkYgIJR5OOwfi5QiNPwgzXjdXaegTlw7xh/"
                    + "e17tqU9uYT9SdrhVXKhhl6Xt9royhEaxoEYE0rRbM09ubAgAr7rlvpsNA5Bo/wEDv8l0AUuagyDsX6tTSAFoWvNlaRtyB6L0anLk"
                    + "inOimgPaSmBd3oEo5dCTbps38U3B0VIUIZnpMDBjwwzYJwVk12evvnY/wyBr/QDEcv+e6SAlAJeh7NMbRGzhIGq5kJ4neCtmIT1R"
                    + "e1kflvpq0STUjF+CFZQ4AgSAV1974ObgAIbkN9JIdPrOW55HbhWLhyDzNvyHgGnI+yZIMUXEw5LXvq4RR7grH/s0YMKM5fwBjDTS"
                    + "SCkR4KL1niINQ2rCay3AtGYuCEig4eeBeOABi1PsGzAyE6bBSAL8882R5/rmHKx5K/veCzBsBcq086gFF1tZ8tpxadj0EvgIndZY"
                    + "02aN3QZVPuQEbjQQcLlzxejvOPu/I/vsRFr8v32dgBhWAwJGg6xpKjBtZAGeaE6O/LmxQ3ZeEM0LEkAs0RC0ELS/9gHEs7j8Oiaw"
                    + "Je1Cd4fvrzk1r3AO4TP3fuJ28+bH8TxgmQd4752ZWwDZlWL/RBqD7DwwueMHZg7ZecVg4tzma669oFGSPhDAYI8gIi3RhQ46DgBg"
                    + "H+2/Hj4CNSeK5lTWnlo1wKB0TLl1lc6hRhMQOnIA2GFtS6d9yxWl/3+aCGhvCg4MYTiPrcDu4cFbxIVaVL4F1W+ZUy1aryUW2k0p"
                    + "Xa+aPrcUDaCTGCAlAlT917KcQI1qbwEFVG/ygzCPW4CRRqpOrz08tMgHFPi3An0HXssv8PU3ET4KDbFpj6xfQwr4S8yF7fVT9sZj"
                    + "NKfjFiG/tCe05vTUntYtoJ6WLS9xG1rRolU0gQIHJj2pe4gALdwNCPuvBQcXTmAhAlcdBGSCVNR6+CuZDms0D1u9DWrMiMvhuHlv"
                    + "iNLQ5XntwlJ7kITG4IKTcH7zkIDeaCAWs8ArRM+4Lc6ZUOc09yQhwzkQEYn+Oa0/zkyZE4YorcPXHl7o+dz3hGr///7duwnv4Ony"
                    + "c48Y3+t7nEDg69+VFwg05tope+2bPU7n3txBDTagPWn2wiF6AoaaE1QiO+/RX82VHyhP+164AFX2deZFV5sDOGvvdqe8d/97z/sc"
                    + "636u9773dydIeiLQ6ii09ebA8wg0IJ2RRmpPrzs8svr4mzhQMNQE9E2GY9BuLe/Mex2QZwCm656GYeqzcG0r9WvoTIudxqDZyxBI"
                    + "A4CV+u7ZF8B2xkASkKknCNgihvQA8HqAg1JWvWYdNX2BQqRxz15vHrnKIGB7pN3adkq+AkHka1AD8WFG85A2uQUCLCsBZRzQxgFa"
                    + "+SAiKFofLAKM/JxSwJIeWwmAy/vpk4ORKRCIWa1IKAB78Rq0Ehyq79ebFytZ8VoWPhYnqgnANoo+l6Bc1ApotZzePdrdYg49tQm3"
                    + "AAe3Autq261x3PL6a491kOe1Mn4chESmdjwwgJFG2iC94fAY9Ik61AoW5ts3e53M5+AIrtrcJKfMXtyNFjfpgbFcKodWq6L8hsOL"
                    + "L55QGcmCXaWXc1VEA6xsd282txVA07LUW7HqW6yjJL3x2ktm5Z9DgsrHqH34/zifHIKEKP+K9J+iD6Xtp45FQ38BJo4cW68DKKvd"
                    + "HmWYMx1GQlMOCcAIhf78IIHb5OAkVVcSbASyvv9kbfD+A6UgIm2MndM8BNE4kNEAhAio40A8ACCAyFoiwJsII1kSmboc4Lj++kbz"
                    + "6AVzAHsp45SULM7d/55j0aRz97/FeHqkc/ev5QTMo9A3vFcLYDhAwJFG2p8I4GMREGcatmEfbUCzhR1AD0CtRS7vAeBdGubRAp71"
                    + "8B7cGwOoAT6xQoYHRdkemEOpzTeZl1yWCLAn8q1BWHsEHGnZqL3606D6mg99L3Cz1zxq5qUhIBrUfiswVUosTkTAAXMu9Pd6ogdR"
                    + "gRygt6j+RuAfeGAfo/brg38OAFz8AbSY21JgVylYB4ri3tIASwm0q4UxaQCPD7ZBaQ3SIT1ApMEomxMHDpaBOsgAdSmAhYX1pmAy"
                    + "YAA+HkCLwWcqYjBfA5lNKdUazAF7kOmPMzNGNbfxJvOyDc5zvVhgLvFePHdS9+Q2tLoEmpOv9/VkD5GjdKpJuZvSyboFC59rY4uT"
                    + "uvXqVNLmmw+Pk74AAE7+/4MYAGp9oNQVWNDm7E9ggIAjjXTG9CZ8vHRGQxg9uBenEMGPe5/WvUE86TxqQbFaWbtVK65GrpecQFIv"
                    + "xFoZuxYErJHhtVzBlsBgi83Dm80TZwQBMzHnMRPfHgUZFO0mG0YRp556nvt/cV4lwsa0XRpvrhy7VjU3BhVrQ9Uh59bjhiKzBuL1"
                    + "qSAKGpGpRlTQWg/6z99sngiAvTSU+GF16BmDfw4AJLT+KGDQRSmaJYGytl6Nrz/IgIZAgmi6aMO0cWcedMyb3XIxefPmyLzWIK3d"
                    + "lwfr8n4E86AhB34BA6ZCMqoc4IiM10GAfBARGkADdhxcJODypsoBjtLAIJC8Ix0GwMGB6bwoIPEP4cv35wCGFDbSSJeT8kRA5utf"
                    + "AxAOAjDSSFeKCPTGAJTg27nMdgHqQELo3Lb2uhCEoKAUIMzJuTXOPwBkXoE142gFNyUAnBbEk44VFGOoAQSl2MIfxqcuhwDUAj41"
                    + "9+Ktm7L1xkAyhto5aG4HtB+8ZA6gHGsN4i41adbqJmjQfA1RgEZQsBZwlMznLfhUAOwF4F9i+msB8QCIhxT8y5ghG72+HFZCgnIP"
                    + "flAEF6nSXNRhyI4AMvMq+enjAC0Qmg4jA9ohCUZhAlNxeoOpzp5W2w6Lpr/AAKxls1lgNekoU2fI6gHm58EDiciCfdx2LQcRyQUn"
                    + "KROBdKVOT99qnlbI9dS/Bwg40khXOr3FPFNRiwMKY5dgwjt97b2/9h4+aYsTNSr0E0Cgm8DVJ+/2NfiAQjcgdz9f0hmIdQck4kEJ"
                    + "iwHmvebGKtEx0IoAEhFCi19oWPFNMYDM+/TzW/CZTYiL6amzrwX5NDKxBnPYq90aAE5bf6t2JR9rrfyvwQVqcAWtrN2qyNOKAbTa"
                    + "Dbi/3wrPEie8lisI6zerAm9lzNPiO6BGPbhHu1KEvba+Vh23pt0W0FELoLUSmz3ahcr+ap+Xyr0Vnp1BwVOob8dmxmBh8P8oOhEA"
                    + "wATfhgm+DWY7Gz/ouPW38BpQwmVbLjEhs9Uk20/SpuTTld7HaLeEhk8p1Zc8y62Tpk2Nf9+ad1nbppRcnNLb8JXQ7hFogIAjjXRl"
                    + "09vgGYa1l6ZrAHDN9wrc96zeg9Wuld9B0GdvvEHDsmvYas3aSmTNlvZqdQhK7HAvMaCF56kFAWuUmaRzColARxAQdiYI5wwGAh2J"
                    + "lXaOe4ObGi0+LSGQ4gs9wcxexEUzvh4gYC1oiSQReHbdyS57/0dMMwAA4ikbyUcGwg9Z+/FrCM4WH/+5P9CtN1nNB1bjTUd7+vVC"
                    + "8bVXhLUn7ZbPQcht5J6/DV7JgoB+Wn9fy+K7//Wz9oQj4ownpkO28/8t84ptNCS7/B2WtUEduk3LfEKlNpdxW3pMkMzPn3OuzXQM"
                    + "3Pwl843X2EZrnLRtC/Ml/m/Zd5MbJ71mNpk7Eu8GmXFQa4eCdx9/T/l2cnPmvyck3im1vqXvCZeBWfJ95NqkSYPNri3/Pf1H+Ny8"
                    + "BY5grZlPeq+t+dbAEYABAo400g2U3g6vKoCCnYODauRugP4Xfr3Egp5KOFqrtxpsoBYw1LRZ6g+E7H2uTI383iJutGAANZ6EWtqs"
                    + "FSlWItAAAp7jdr4GLOthtQcbEIJaogCNhKZ280Jlu5IPvYfWQSvY1ouwSGV3zY2Btk0JXvB2KyECjZqALZsVoC8y37JxNUBmy41B"
                    + "7XilH27L5sVKlFy7qbQEqzcw2EpYtgARpZtay3G8A14dAn/WCyoy+wW0eBwYwEgj3ajpHfDq1au4ifn+hQPocSvfKgSUGEeoqA9Q"
                    + "fym5hXqtZEzS+hrGXnKeldRspW2A4P1J5weFdyCtL2XCNaY79Wq88rlphQR6vd8xfacMA2jZ/r3Z9b0AwhIwpsUrtOPqBQ7WaOaB"
                    + "AhzUkNeeGECt5mSLck8PYK6nfgJUkKWEE8gQAVPy5Q+dfQX0rkP5ixcTGoGPAKkdPwhiIkja4HwPtIBvWmAQGjYwdMYAUHhOSm4h"
                    + "ln8L/CqU4hQg4eOgF7HZAkN4+/QHdLcA0HjSagG41mvEnmOtOcFrwLaaG4MeV5FaZ57aDSyds3YD10QdqrXRr1Ev3puzUAOD02tS"
                    + "AjCgkpFGuomAwem1QShxowmpTUXE0YTl5kJN804/+fg+uThCXKhvzulkKfx52AYwMXnyq+DTZ8qhqWRWeWeWtLNRLhIReKsfl+Ji"
                    + "7gCAIOpRLiIREKOg4+VwMYGQcU1Kn6h0ZCAg30ZcH9mxIluba5d2gJrnCMqgqZwDCet/9/QHyyJAjeJOD1CvRiyQgGY1+L1UrtUq"
                    + "/UhYXynrrVHwKcnZ2vciuXOQ3k/0uhfQ3BdIRYutRYhalyIt2MIfPZ6IgGHwkGJ2KX7W0hYo24JCWWDaLs0HCm1I27PMvIDpL7cG"
                    + "NXMFwXpBw3vh5sCNCQpzgUK7wPwfFP1J3kuuLVsooykrWS9oWFsJERgcwOAABgdwE3IALv1/LJUrJaCTi04AAAAASUVORK5CYII=";
        private static final int[] GRASS = decode(GRASS_PNG), FOLIAGE = decode(FOLIAGE_PNG);

        private static int[] decode(String png) {
            try {
                BufferedImage image =
                        ImageIO.read(new ByteArrayInputStream(Base64.getDecoder().decode(png)));
                return image.getRGB(0, 0, 256, 256, null, 0, 256);
            } catch (IOException ex) {
                throw new ExceptionInInitializerError(ex);
            }
        }

        private static int color(boolean grass, double temperature, double humidity) {
            int x = (int) ((1.0 - temperature) * 255);
            int y = (int) ((1.0 - humidity * temperature) * 255);
            return (grass ? GRASS : FOLIAGE)[(y << 8) | x] & 0xffffff;
        }
    }

    private static final class Canopy {
        final int minY;
        final int[] positions;
        final short[] offsets, stateIds, logIds;
        final byte[] distances, flags;
        final float[] survivalChances;
        final String[] states, logTypes;
        final boolean[] seasonalStates;
        final Map<Integer, BlockData> dataCache = new HashMap<>();
        final Map<Integer, DiscardInfo> discards = new HashMap<>();
        final Map<Integer, Material> legacyOverlays = new HashMap<>();
        int cursor;
        boolean dirty;
        long preservationSeed;
        int preservationPolicy;

        Canopy(int minY, int size, String[] states, String[] logs) {
            this.minY = minY;
            this.states = states;
            seasonalStates = new boolean[states.length];
            for (int i = 0; i < states.length; i++) {
                String id = states[i].split("\\[", 2)[0];
                seasonalStates[i] =
                        id.equals("minecraft:oak_leaves") || id.equals("minecraft:birch_leaves");
            }
            logTypes = logs;
            positions = new int[size];
            offsets = new short[size];
            stateIds = new short[size];
            logIds = new short[size];
            distances = new byte[size];
            flags = new byte[size];
            survivalChances = new float[size];
            Arrays.fill(survivalChances, Float.NaN);
        }

        int size() {
            return positions.length;
        }

        boolean canShed(int i) {
            return seasonalStates[stateIds[i] & 0xffff];
        }

        int index(Block b) {
            return Arrays.binarySearch(
                    positions, ((b.getY() - minY) << 8) | ((b.getZ() & 15) << 4) | (b.getX() & 15));
        }

        BlockData data(int i) {
            int id = stateIds[i] & 0xffff;
            return dataCache.computeIfAbsent(id, k -> Bukkit.createBlockData(states[k]));
        }

        Row row(int i) {
            return new Row(
                    positions[i],
                    offsets[i],
                    states[stateIds[i] & 0xffff],
                    logTypes[logIds[i] & 0xffff],
                    distances[i],
                    flags[i]);
        }

        static Canopy fromRows(int minY, List<Row> rows) {
            rows.sort(Comparator.comparingInt(Row::position));
            Map<String, Integer> states = new LinkedHashMap<>(), logs = new LinkedHashMap<>();
            for (Row r : rows) {
                states.computeIfAbsent(r.data, k -> states.size());
                logs.computeIfAbsent(r.log, k -> logs.size());
            }
            Canopy c =
                    new Canopy(
                            minY,
                            rows.size(),
                            states.keySet().toArray(String[]::new),
                            logs.keySet().toArray(String[]::new));
            for (int i = 0; i < rows.size(); i++) {
                Row r = rows.get(i);
                c.positions[i] = r.position;
                c.offsets[i] = r.offset;
                c.stateIds[i] = (short) (int) states.get(r.data);
                c.logIds[i] = (short) (int) logs.get(r.log);
                c.distances[i] = r.distance;
                c.flags[i] = r.flags;
            }
            return c;
        }

        byte[] encode() throws IOException {
            ByteArrayOutputStream bytes = new ByteArrayOutputStream();
            try (DataOutputStream out = new DataOutputStream(new GZIPOutputStream(bytes))) {
                out.writeInt(MAGIC);
                out.writeInt(minY);
                out.writeInt(size());
                out.writeInt(states.length);
                for (String s : states) out.writeUTF(s);
                out.writeInt(logTypes.length);
                for (String s : logTypes) out.writeUTF(s);
                for (int i = 0; i < size(); i++) {
                    out.writeInt(positions[i]);
                    out.writeShort(offsets[i]);
                    out.writeShort(stateIds[i]);
                    out.writeShort(logIds[i]);
                    out.writeByte(distances[i]);
                    out.writeByte(flags[i]);
                }
                out.writeInt(DISCARD_MAGIC);
                out.writeInt(discards.size());
                for (Map.Entry<Integer, DiscardInfo> entry : discards.entrySet()) {
                    DiscardInfo info = entry.getValue();
                    out.writeInt(entry.getKey());
                    out.writeLong(info.timeMillis);
                    out.writeUTF(info.reason);
                    out.writeUTF(info.leaf);
                    out.writeUTF(info.log);
                }
                out.writeInt(PRESERVATION_CANOPY_MAGIC);
                out.writeLong(preservationSeed);
                out.writeInt(CANOPY_POLICY_MAGIC);
                out.writeInt(preservationPolicy);
                out.writeInt(SURVIVAL_CENSUS_MAGIC);
                out.writeInt(size());
                for (float chance : survivalChances) out.writeFloat(chance);
                // Preserve ownership only while reading/migrating an older saved chunk.
                if (!legacyOverlays.isEmpty()) {
                    out.writeInt(LEGACY_OVERLAY_MAGIC);
                    out.writeInt(legacyOverlays.size());
                    for (Map.Entry<Integer, Material> entry : legacyOverlays.entrySet()) {
                        out.writeInt(entry.getKey());
                        out.writeUTF(entry.getValue().name());
                        out.writeLong(1L);
                    }
                }
            }
            return bytes.toByteArray();
        }

        static Canopy decode(byte[] bytes) throws IOException {
            try (DataInputStream in =
                    new DataInputStream(new GZIPInputStream(new ByteArrayInputStream(bytes)))) {
                if (in.readInt() != MAGIC) throw new IOException("Unknown canopy format");
                int minY = in.readInt(), count = in.readInt(), n = in.readInt();
                if (count < 0 || count > 1048576 || n < 0 || n > 4096)
                    throw new IOException("Invalid canopy size");
                String[] states = new String[n];
                for (int i = 0; i < n; i++) states[i] = in.readUTF();
                int m = in.readInt();
                if (m < 0 || m > 4096) throw new IOException("Invalid log palette");
                String[] logs = new String[m];
                for (int i = 0; i < m; i++) logs[i] = in.readUTF();
                Canopy c = new Canopy(minY, count, states, logs);
                for (int i = 0; i < count; i++) {
                    c.positions[i] = in.readInt();
                    c.offsets[i] = in.readShort();
                    c.stateIds[i] = in.readShort();
                    c.logIds[i] = in.readShort();
                    c.distances[i] = in.readByte();
                    c.flags[i] = in.readByte();
                    if ((c.stateIds[i] & 0xffff) >= n
                            || (c.logIds[i] & 0xffff) >= m
                            || c.distances[i] < 1
                            || c.distances[i] > 6
                            || (i > 0 && c.positions[i] <= c.positions[i - 1]))
                        throw new IOException("Invalid leaf record");
                }
                // Optional trailer: old saved canopies have no reasons. A damaged or
                // unknown debug extension must never make the original canopy unreadable.
                try {
                    int first = in.read();
                    if (first >= 0) {
                        int marker =
                                (first << 24)
                                        | (in.readUnsignedByte() << 16)
                                        | (in.readUnsignedByte() << 8)
                                        | in.readUnsignedByte();
                        if (marker == DISCARD_MAGIC) {
                            int entries = in.readInt();
                            if (entries < 0 || entries > count)
                                throw new IOException("Invalid discard count");
                            Map<Integer, DiscardInfo> details = new HashMap<>();
                            for (int nEntry = 0; nEntry < entries; nEntry++) {
                                int position = in.readInt();
                                DiscardInfo info =
                                        new DiscardInfo(
                                                in.readLong(),
                                                in.readUTF(),
                                                in.readUTF(),
                                                in.readUTF());
                                int row = Arrays.binarySearch(c.positions, position);
                                if (row >= 0 && (c.flags[row] & INVALID) != 0)
                                    details.put(position, info);
                            }
                            c.discards.putAll(details);
                            if (in.readInt() == PRESERVATION_CANOPY_MAGIC) {
                                c.preservationSeed = in.readLong();
                                if (in.readInt() == CANOPY_POLICY_MAGIC) {
                                    c.preservationPolicy = in.readInt();
                                    if (in.readInt() != SURVIVAL_CENSUS_MAGIC
                                            || in.readInt() != count)
                                        throw new IOException("Missing full-canopy census");
                                    float[] chances = new float[count];
                                    for (int i = 0; i < count; i++) {
                                        chances[i] = in.readFloat();
                                        if (!Float.isNaN(chances[i])
                                                && (!Float.isFinite(chances[i])
                                                        || chances[i] < 0
                                                        || chances[i] > 1))
                                            throw new IOException("Invalid survival chance");
                                    }
                                    System.arraycopy(chances, 0, c.survivalChances, 0, count);
                                }
                            }
                        }
                    }
                } catch (IOException ignored) {
                    c.preservationPolicy = 0;
                    // Leaf restoration still uses the already-validated original rows.
                }
                boolean needsLegacyOwnership = false;
                for (byte flag : c.flags)
                    if ((flag & LEGACY_OVERLAY_FLAG) != 0) needsLegacyOwnership = true;
                try {
                    // Older canopies may have no overlay trailer. Keep their survivor census valid.
                    int extension = in.read();
                    if (extension >= 0) {
                        int marker =
                                (extension << 24)
                                        | (in.readUnsignedByte() << 16)
                                        | (in.readUnsignedByte() << 8)
                                        | in.readUnsignedByte();
                        if (marker != LEGACY_OVERLAY_MAGIC)
                            throw new IOException("Unknown legacy overlay extension");
                        int entries = in.readInt();
                        if (entries < 0 || entries > count)
                            throw new IOException("Invalid legacy overlay count");
                        for (int j = 0; j < entries; j++) {
                            int position = in.readInt();
                            Material material;
                            try {
                                material = Material.valueOf(in.readUTF());
                            } catch (IllegalArgumentException ex) {
                                throw new IOException("Invalid legacy overlay material", ex);
                            }
                            long expires = in.readLong();
                            int i = Arrays.binarySearch(c.positions, position);
                            if (i < 0
                                    || (c.flags[i] & (INVALID | REMOVED | LEGACY_OVERLAY_FLAG))
                                            != (REMOVED | LEGACY_OVERLAY_FLAG)
                                    || !(material == Material.HORN_CORAL_BLOCK
                                            || material == Material.FIRE_CORAL_BLOCK
                                            || material == Material.ORANGE_CONCRETE_POWDER)
                                    || expires <= 0)
                                throw new IOException("Invalid legacy overlay record");
                            c.legacyOverlays.put(position, material);
                        }
                    }
                    for (int i = 0; i < count; i++)
                        if ((c.flags[i] & LEGACY_OVERLAY_FLAG) != 0
                                && !c.legacyOverlays.containsKey(c.positions[i]))
                            throw new IOException("Missing legacy overlay ownership record");
                } catch (IOException | RuntimeException ex) {
                    if (needsLegacyOwnership)
                        throw new IOException("Cannot recover legacy overlay ownership", ex);
                    c.legacyOverlays.clear();
                    c.preservationPolicy = 0;
                }
                return c;
            }
        }
    }
}
