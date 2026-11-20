package dev.npclife;

import org.bukkit.Bukkit;
import org.bukkit.entity.Entity;
import org.bukkit.entity.Player;
import org.bukkit.plugin.Plugin;

import java.lang.reflect.Method;

/** Plays Citizens' PlayerAnimation (item-use poses etc.) via reflection, since it is not part of the public API. */
final class AnimUtil {
    private static Class<?> cls;
    private static Method play;
    private static boolean withRadius, tried;

    private static void init() {
        if (tried) return;
        tried = true;
        try {
            Plugin c = Bukkit.getPluginManager().getPlugin("Citizens");
            cls = Class.forName("net.citizensnpcs.util.PlayerAnimation", true, c.getClass().getClassLoader());
            try { play = cls.getMethod("play", Player.class); }
            catch (NoSuchMethodException ex) { play = cls.getMethod("play", Player.class, int.class); withRadius = true; }
        } catch (Throwable ex) { play = null; }
    }

    static boolean available() { init(); return play != null; }

    static boolean play(Entity e, String name) {
        init();
        if (play == null || !(e instanceof Player p)) return false;
        try {
            Object constant = cls.getField(name).get(null);
            if (withRadius) play.invoke(constant, p, 64); else play.invoke(constant, p);
            return true;
        } catch (Throwable ex) { return false; }
    }
}
