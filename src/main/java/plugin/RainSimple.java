package plugin;

import org.bukkit.Bukkit;
import org.bukkit.ChatColor;
import org.bukkit.command.Command;
import org.bukkit.command.CommandExecutor;
import org.bukkit.command.CommandSender;
import org.bukkit.command.PluginCommand;
import org.bukkit.entity.Player;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.scheduler.BukkitTask;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Locale;

/** Sets the rain level shown to players without changing server weather. */
public final class RainSimple implements CommandExecutor {
    private static final String LEVEL_PATH = "rain-simple.visual-level";
    private final JavaPlugin plugin;
    private final PacketBridge packets;
    private Float visualLevel;
    private Object cachedPacket;
    private BukkitTask task;
    private boolean sendErrorLogged;

    public RainSimple(JavaPlugin plugin) {
        this.plugin = plugin;
        PacketBridge bridge = null;
        try {
            if (!"1.18.2".equals(plugin.getServer().getMinecraftVersion())) {
                throw new IllegalStateException(
                        "This packet implementation requires Minecraft 1.18.2.");
            }
            bridge = new PacketBridge(plugin);
        } catch (ReflectiveOperationException | IllegalStateException e) {
            plugin.getLogger()
                    .severe("RainSimple could not initialize the 1.18.2 packet bridge: " + e);
        }
        packets = bridge;
        Object saved = plugin.getConfig().get(LEVEL_PATH);
        if (saved instanceof Number number) {
            double value = number.doubleValue();
            if (Double.isFinite(value) && value >= 0.0 && value <= 1.0) {
                visualLevel = (float) value;
                if (packets != null) cachedPacket = packets.newRainPacket(visualLevel);
            } else {
                plugin.getLogger()
                        .warning("Invalid saved visual rain level; using normal weather.");
            }
        } else if (saved != null) {
            plugin.getLogger().warning("Invalid saved visual rain level; using normal weather.");
        }
    }

    /** Call once from the main plugin's onEnable. */
    public void register() {
        PluginCommand command = plugin.getCommand("rainlevel");
        if (command == null) {
            throw new IllegalStateException("The rainlevel command is missing from plugin.yml.");
        }
        command.setExecutor(this);
        if (packets != null) {
            // Weather and dimension packets can otherwise overwrite the visual level.
            task = Bukkit.getScheduler().runTaskTimer(plugin, this::refreshPlayers, 1L, 1L);
        }
    }

    /** Call from onDisable so players return to their world's normal weather. */
    public void shutdown() {
        if (task != null) task.cancel();
        if (visualLevel != null && packets != null) restoreOnlinePlayers();
    }

    @Override
    public boolean onCommand(CommandSender sender, Command command, String label, String[] args) {
        if (!command.getName().equalsIgnoreCase("rainlevel")) return false;
        if (args.length != 1) {
            sender.sendMessage(ChatColor.YELLOW + "Usage: /rainlevel <0 to 1|reset>");
            return true;
        }
        if (packets == null) {
            sender.sendMessage(
                    ChatColor.RED + "Rain level packets are unavailable; see the server log.");
            return true;
        }
        if (args[0].equalsIgnoreCase("reset")) {
            visualLevel = null;
            cachedPacket = null;
            plugin.getConfig().set(LEVEL_PATH, null);
            plugin.saveConfig();
            restoreOnlinePlayers();
            sender.sendMessage(ChatColor.GREEN + "Visual rain now follows each world's weather.");
            return true;
        }
        final double value;
        try {
            value = Double.parseDouble(args[0]);
        } catch (NumberFormatException e) {
            sender.sendMessage(ChatColor.RED + "Enter a number from 0 to 1, or reset.");
            return true;
        }
        if (!Double.isFinite(value) || value < 0.0 || value > 1.0) {
            sender.sendMessage(ChatColor.RED + "The rain level must be between 0 and 1.");
            return true;
        }
        Object newPacket = packets.newRainPacket((float) value);
        if (newPacket == null) {
            sender.sendMessage(
                    ChatColor.RED + "Could not create a rain packet; see the server log.");
            return true;
        }
        visualLevel = (float) value;
        cachedPacket = newPacket;
        plugin.getConfig().set(LEVEL_PATH, value);
        plugin.saveConfig();
        refreshPlayers();
        sender.sendMessage(
                ChatColor.GREEN
                        + "Visual rain level set to "
                        + String.format(Locale.ROOT, "%s", value)
                        + ".");
        return true;
    }

    private void refreshPlayers() {
        if (cachedPacket == null) return;
        for (Player player : Bukkit.getOnlinePlayers()) send(player, cachedPacket);
    }

    private void restoreOnlinePlayers() {
        Object clear = packets.newRainPacket(0.0f);
        Object rain = packets.newRainPacket(1.0f);
        for (Player player : Bukkit.getOnlinePlayers()) {
            Object packet = player.getWorld().hasStorm() ? rain : clear;
            if (packet != null) send(player, packet);
        }
    }

    private void send(Player player, Object packet) {
        try {
            packets.send(player, packet);
        } catch (ReflectiveOperationException | RuntimeException e) {
            if (!sendErrorLogged) {
                sendErrorLogged = true;
                plugin.getLogger().severe("Could not send visual rain packets: " + e);
            }
        }
    }

    /** Reflection keeps NMS classes out of the Gradle compile classpath. */
    private static final class PacketBridge {
        private final JavaPlugin plugin;
        private final Constructor<?> packetConstructor;
        private final Object rainLevelReason;
        private final Method getHandle;
        private final Field connectionField;
        private final Method sendPacket;

        PacketBridge(JavaPlugin plugin) throws ReflectiveOperationException {
            this.plugin = plugin;
            Class<?> packetClass =
                    firstClass(
                            "net.minecraft.network.protocol.game.PacketPlayOutGameStateChange",
                            "net.minecraft.network.protocol.game.ClientboundGameEventPacket");
            Class<?> packetInterface = Class.forName("net.minecraft.network.protocol.Packet");
            Constructor<?> selected = null;
            for (Constructor<?> constructor : packetClass.getConstructors()) {
                Class<?>[] params = constructor.getParameterTypes();
                if (params.length == 2 && params[1] == float.class) {
                    selected = constructor;
                    break;
                }
            }
            if (selected == null) throw new NoSuchMethodException("game event packet constructor");
            packetConstructor = selected;
            Class<?> reasonType = selected.getParameterTypes()[0];
            rainLevelReason = findRainReason(packetClass, reasonType);

            String craftPackage = plugin.getServer().getClass().getPackage().getName();
            Class<?> craftPlayer = Class.forName(craftPackage + ".entity.CraftPlayer");
            getHandle = craftPlayer.getMethod("getHandle");
            Class<?> handleType = getHandle.getReturnType();
            Class<?> connectionType =
                    firstClass(
                            "net.minecraft.server.network.PlayerConnection",
                            "net.minecraft.server.network.ServerGamePacketListenerImpl");
            Field selectedField = null;
            for (Field field : handleType.getFields()) {
                if (connectionType.isAssignableFrom(field.getType())) {
                    selectedField = field;
                    break;
                }
            }
            if (selectedField == null) throw new NoSuchFieldException("player connection");
            connectionField = selectedField;
            Method selectedMethod = null;
            for (String name : new String[] {"sendPacket", "send", "a"}) {
                try {
                    selectedMethod = connectionType.getMethod(name, packetInterface);
                    break;
                } catch (NoSuchMethodException ignored) {
                    // Try another 1.18.2 mapping.
                }
            }
            if (selectedMethod == null) throw new NoSuchMethodException("send packet");
            sendPacket = selectedMethod;
        }

        private static Class<?> firstClass(String... names) throws ClassNotFoundException {
            for (String name : names) {
                try {
                    return Class.forName(name);
                } catch (ClassNotFoundException ignored) {
                }
            }
            throw new ClassNotFoundException(String.join(" or ", names));
        }

        private static Object findRainReason(Class<?> packetClass, Class<?> reasonType)
                throws ReflectiveOperationException {
            for (String name : new String[] {"RAIN_LEVEL_CHANGE", "RAIN_GRADIENT_CHANGED", "h"}) {
                try {
                    Field field = packetClass.getField(name);
                    if (Modifier.isStatic(field.getModifiers()) && field.getType() == reasonType) {
                        return field.get(null);
                    }
                } catch (NoSuchFieldException ignored) {
                }
            }
            throw new NoSuchFieldException("rain level change reason");
        }

        Object newRainPacket(float level) {
            try {
                return packetConstructor.newInstance(rainLevelReason, level);
            } catch (ReflectiveOperationException e) {
                plugin.getLogger().severe("Could not create a visual rain packet: " + e);
                return null;
            }
        }

        void send(Player player, Object packet) throws ReflectiveOperationException {
            Object handle = getHandle.invoke(player);
            Object connection = connectionField.get(handle);
            sendPacket.invoke(connection, packet);
        }
    }
}
