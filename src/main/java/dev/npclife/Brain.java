package dev.npclife;

import dev.npclife.ActionType.Channel;
import net.citizensnpcs.api.CitizensAPI;
import net.citizensnpcs.api.ai.Navigator;
import net.citizensnpcs.api.trait.trait.Equipment;
import net.citizensnpcs.trait.SneakTrait;
import org.bukkit.Bukkit;
import org.bukkit.GameMode;
import org.bukkit.Location;
import org.bukkit.Material;
import org.bukkit.Sound;
import org.bukkit.SoundCategory;
import org.bukkit.Tag;
import org.bukkit.World;
import org.bukkit.block.Block;
import org.bukkit.block.BlockFace;
import org.bukkit.block.Lidded;
import org.bukkit.block.data.Bisected;
import org.bukkit.block.data.BlockData;
import org.bukkit.block.data.Openable;
import org.bukkit.block.data.Powerable;
import org.bukkit.block.data.type.Door;
import org.bukkit.block.data.type.Switch;
import org.bukkit.entity.Entity;
import org.bukkit.entity.LivingEntity;
import org.bukkit.entity.Player;
import org.bukkit.event.player.PlayerTeleportEvent;
import org.bukkit.inventory.ItemStack;
import org.bukkit.util.Vector;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * Runtime decision-making for one NPC.
 *
 * Actions occupy CHANNELS (HEAD, MOVE, JUMP, SPRINT, SNEAK, HAND). Actions in different channels run in
 * parallel (walk + look around + jump). An action can only take a busy channel from a LOWER-priority action,
 * so NPCs don't constantly interrupt themselves. Every action has a hard timeout, and walking has stuck detection,
 * so nothing can loop forever.
 */
final class Brain {
    static final class Active {
        final ActionType type; final Channel primary;
        long end, next; int phase, kind, prio;
        boolean orig, changed, ret, done;
        Entity ent; Location loc; Block block;
        Active(ActionType t, long end) { type = t; primary = t.channels[0]; this.end = end; prio = t.priority; }
    }

    private enum LookMode { ANGLES, ENTITY, LOC }

    private static final Set<Material> BAD = EnumSet.of(Material.CACTUS, Material.MAGMA_BLOCK, Material.CAMPFIRE,
            Material.SOUL_CAMPFIRE, Material.FIRE, Material.SOUL_FIRE, Material.SWEET_BERRY_BUSH,
            Material.WITHER_ROSE, Material.POWDER_SNOW, Material.COBWEB, Material.LAVA);

    private static final Set<Material> UTILITY = EnumSet.of(Material.CRAFTING_TABLE, Material.FURNACE, Material.BLAST_FURNACE,
            Material.SMOKER, Material.ANVIL, Material.CHIPPED_ANVIL, Material.DAMAGED_ANVIL, Material.SMITHING_TABLE,
            Material.GRINDSTONE, Material.LOOM, Material.CARTOGRAPHY_TABLE, Material.STONECUTTER, Material.ENCHANTING_TABLE,
            Material.BREWING_STAND, Material.LECTERN, Material.FLETCHING_TABLE);

    private final LifeTrait t;
    private final Random rng = new Random();
    private final EnumMap<Channel, Active> slots = new EnumMap<>(Channel.class);
    private final EnumMap<ActionType, Long> cooldown = new EnumMap<>(ActionType.class);

    boolean near = true;
    private long now, nextThink, nextJump, nextSpam, nextBoundary, outsideSince = -1, lastPosTick;
    private double forcedSec = -1;
    private boolean manualSneak, manualSprint, manualHop, autoSneak, lookOn, appliedSneak, appliedSprint;
    private LookMode lookMode = LookMode.ANGLES;
    private float curYaw, curPitch, velYaw, velPitch, tYaw, tPitch;
    private Entity lookEnt;
    private Location lookLoc, lastPos;
    private int hotbarIdx = -1;
    private boolean sprintJump, useCont, lookHold, seqLoop, seqCombine, seqChecked;
    private long useUntil, nextUse, nextHomeCheck, homeOutsideSince = -1, homeWalkStart = -1, seqWaitUntil, nextSJ;
    private List<String> seq;
    private int seqIdx;
    private Location seqOrigin;
    private Active seqBlock;

    Brain(LifeTrait t) { this.t = t; }

    // ---------------------------------------------------------------- helpers
    private Personality p() { return t.personality(); }
    private Entity ent() { return t.getNPC().isSpawned() ? t.getNPC().getEntity() : null; }
    private Navigator nav() { return t.getNPC().getNavigator(); }
    private static long ticks(double sec) { return Math.max(1L, (long) (sec * 20.0)); }
    private double rand(double a, double b) { return b <= a ? a : a + rng.nextDouble() * (b - a); }
    private long dur(ActionConfig c) { return ticks(forcedSec > 0 ? forcedSec : rand(c.durMin, c.durMax)); }
    private static boolean valid(Entity e) { return e != null && e.isValid() && !e.isDead(); }
    private static double dist(Entity a, Entity b) {
        return a.getWorld() == b.getWorld() ? a.getLocation().distance(b.getLocation()) : Double.MAX_VALUE;
    }
    private boolean isMoving() {
        Active m = slots.get(Channel.MOVE);
        return m != null && (m.type == ActionType.WALK || m.type == ActionType.APPROACH || m.type == ActionType.FLEE);
    }
    private boolean onGround(Entity e) {
        if (e.isOnGround()) return true;
        return e.getLocation().clone().subtract(0, 0.08, 0).getBlock().getType().isSolid() && e.getVelocity().getY() <= 0.1;
    }
    private boolean insideRadius(Location l) {
        Location c = t.center();
        if (c == null) return true;
        double r = limit() - 1;
        return c.getWorld() == l.getWorld() && c.distanceSquared(l) <= r * r;
    }

    // ---------------------------------------------------------------- main tick
    void tick(long tickNow) {
        now = tickNow;
        Entity e = ent();
        if (e == null) return;
        if (!near) return;
        t.ensureCenter();
        if (!seqChecked) { seqChecked = true; t.resumeSequence(); }
        if (now >= nextHomeCheck) { nextHomeCheck = now + 20 + rng.nextInt(10); homing(e); }
        boolean busy = !slots.isEmpty() || lookOn || manualHop || sprintJump || seq != null || useCont || useUntil > 0;
        if (!t.isEnabled() && !busy) return;

        lookTick(e);
        seqTick(e);
        if (useUntil > 0 && !useCont && now >= useUntil) { useUntil = 0; AnimUtil.play(e, "STOP_USE_ITEM"); }
        if ((useCont || useUntil > 0) && now >= nextUse) { nextUse = now + 15; AnimUtil.play(e, "START_USE_MAINHAND_ITEM"); }
        if (manualHop && now >= nextJump && onGround(e)) { jump(e); nextJump = now + 9 + rng.nextInt(6); }
        if (sprintJump) sprintJumpTick(e);
        if (t.isEnabled() && now >= nextBoundary) { nextBoundary = now + 20 + rng.nextInt(10); boundary(e); }

        for (Channel ch : Channel.values()) {
            Active a = slots.get(ch);
            if (a != null && a.primary == ch && !a.done) update(a, e);
        }
        if (t.isEnabled() && (seq == null || seqCombine) && now >= nextThink) {
            nextThink = now + ticks(rand(p().thinkMin, p().thinkMax));
            think(e);
        }
    }

    void shutdown() {
        for (Active a : new LinkedHashSet<>(slots.values())) finish(a, true);
        slots.clear();
        lookOn = false; autoSneak = false;
        syncPose();
    }

    // ---------------------------------------------------------------- decisions
    private static final class Ctx { boolean scanned; Entity player, npc; }

    private void scan(Ctx c, Entity e) {
        if (c.scanned) return;
        c.scanned = true;
        double r = p().awareness, bp = Double.MAX_VALUE, bn = Double.MAX_VALUE;
        for (Entity o : e.getNearbyEntities(r, Math.min(r, 16), r)) {
            if (!(o instanceof LivingEntity) || !valid(o)) continue;
            double d = o.getLocation().distanceSquared(e.getLocation());
            if (CitizensAPI.getNPCRegistry().isNPC(o)) {
                if (d < bn) { bn = d; c.npc = o; }
            } else if (o instanceof Player pl && pl.getGameMode() != GameMode.SPECTATOR) {
                if (d < bp) { bp = d; c.player = o; }
            }
        }
    }

    private Entity pickTarget(Ctx c, Entity e) {
        scan(c, e);
        if (c.player == null) return c.npc;
        if (c.npc == null) return c.player;
        return rng.nextDouble() < p().npcAffinity ? c.npc : c.player;
    }

    private void watchNearestPlayer(Entity e, Ctx c, long durTicks) {
        scan(c, e);
        if (c.player == null || !canOccupy(ActionType.WATCH, forcedSec > 0)) return;
        Active w = open(ActionType.WATCH, durTicks);
        w.ent = c.player;
        lookEntity(e, c.player);
    }

    private Entity groupTarget(Entity e) {
        String g = t.group();
        if (g == null || rng.nextDouble() > 0.7) return null;
        List<Entity> m = NPCLifePlugin.get().brains().members(g, t);
        return m.isEmpty() ? null : m.get(rng.nextInt(m.size()));
    }

    private void think(Entity e) {
        Ctx c = new Ctx();
        List<ActionType> order = new ArrayList<>(Arrays.asList(ActionType.values()));
        Collections.shuffle(order, rng);
        int started = 0;
        for (ActionType ty : order) {
            if (started >= 2) break;
            ActionConfig cfg = p().cfg(ty);
            if (!cfg.enabled || cfg.probability <= 0) continue;
            if (now < cooldown.getOrDefault(ty, 0L)) continue;
            if (rng.nextDouble() * 100.0 >= cfg.probability) continue;   // independent roll every think
            if (!canOccupy(ty, false)) continue;
            if (tryStart(ty, cfg, e, c)) started++;
        }
    }

    private boolean canOccupy(ActionType ty, boolean force) {
        if (force) return true;
        for (Channel ch : ty.channels) {
            Active o = slots.get(ch);
            if (o != null && o.prio >= ty.priority) return false;
        }
        return true;
    }

    private Active open(ActionType ty, long durTicks) {
        for (Channel ch : ty.channels) { Active o = slots.get(ch); if (o != null) finish(o, true); }
        Active a = new Active(ty, now + durTicks);
        for (Channel ch : ty.channels) slots.put(ch, a);
        return a;
    }

    private void setCooldown(ActionType ty) {
        ActionConfig c = p().cfg(ty);
        cooldown.merge(ty, now + ticks(rand(c.cdMin, c.cdMax)), Math::max);
    }

    /** Returns true if the action actually started. */
    private boolean tryStart(ActionType ty, ActionConfig cfg, Entity e, Ctx c) {
        switch (ty) {
            case LOOK_AROUND -> {
                float base = lookOn ? curYaw : e.getLocation().getYaw();
                float yaw = base + (rng.nextBoolean() ? 1 : -1) * (20 + rng.nextInt(95));
                float pitch = -20 + rng.nextInt(45);
                open(ty, dur(cfg));
                lookAngles(e, yaw, pitch);
                return true;
            }
            case TURN_AROUND -> {
                float base = lookOn ? curYaw : e.getLocation().getYaw();
                open(ty, dur(cfg));
                lookAngles(e, base + 180f + (rng.nextFloat() - 0.5f) * 50f, 0f);
                return true;
            }
            case WATCH -> {
                Entity tgt = pickTarget(c, e);
                if (tgt == null) return false;
                Active a = open(ty, dur(cfg));
                a.ent = tgt;
                lookEntity(e, tgt);
                return true;
            }
            case IDLE -> { open(ty, dur(cfg)); return true; }
            case WALK -> {
                Location dest = pickWander(e);
                if (dest == null) { cooldown.put(ty, now + 100); return false; }
                long to = ticks(Math.max(forcedSec > 0 ? forcedSec : rand(cfg.durMin, cfg.durMax),
                        e.getLocation().distance(dest) / 2.5));
                go(e, ty, dest, to, false);
                return true;
            }
            case APPROACH -> {
                Entity tgt = groupTarget(e);
                if (tgt == null) tgt = pickTarget(c, e);
                if (tgt == null || dist(e, tgt) < 4.5 || !insideRadius(tgt.getLocation())) return false;
                Active a = open(ty, dur(cfg));
                a.ent = tgt; lastPos = e.getLocation(); lastPosTick = now;
                syncPose();
                nav().getLocalParameters().distanceMargin(2.5);
                nav().setTarget(tgt, false);
                return true;
            }
            case FLEE -> {
                scan(c, e);
                if (c.player == null || dist(e, c.player) > Math.min(p().awareness, 9)) return false;
                Vector away = e.getLocation().toVector().subtract(c.player.getLocation().toVector()).setY(0);
                if (away.lengthSquared() < 0.01) away = new Vector(rng.nextDouble() - 0.5, 0, rng.nextDouble() - 0.5);
                away.normalize();
                Location here = e.getLocation();
                for (int i = 0; i < 6; i++) {
                    Vector v = away.clone().rotateAroundY((i % 2 == 0 ? 1 : -1) * i * 0.35);
                    double d = 8 + rng.nextInt(8);
                    Location dest = findStandable(here.getWorld(), here.getX() + v.getX() * d, here.getZ() + v.getZ() * d, here.getBlockY());
                    if (dest != null && insideRadius(dest)) {
                        go(e, ty, dest, ticks(Math.max(dur(cfg) / 20.0, d / 2.0)), false);
                        if (p().cfg(ActionType.SPRINT).enabled && slots.get(Channel.SPRINT) == null && slots.get(Channel.SNEAK) == null) {
                            open(ActionType.SPRINT, ticks(3 + rng.nextInt(3)));
                            syncPose();
                        }
                        return true;
                    }
                }
                return false;
            }
            case JUMP -> {
                if (!onGround(e)) return false;
                open(ty, dur(cfg));
                jump(e); nextJump = now + 9 + rng.nextInt(6);
                return true;
            }
            case SPRINT -> {
                if (!isMoving() || slots.get(Channel.SNEAK) != null || manualSneak) return false;
                open(ty, dur(cfg)); syncPose();
                return true;
            }
            case SNEAK, SNEAK_SPAM -> {
                if (slots.get(Channel.SPRINT) != null) return false;
                long sd = dur(cfg);
                open(ty, sd);
                autoSneak = true; nextSpam = now + 3 + rng.nextInt(2);
                syncPose();
                if (ty == ActionType.SNEAK_SPAM) watchNearestPlayer(e, c, sd);
                return true;
            }
            case GREET -> {
                scan(c, e);
                if (c.player == null || dist(e, c.player) > Math.min(p().awareness, 8)) return false;
                Active a = open(ty, dur(cfg));
                a.ent = c.player;
                lookEntity(e, c.player);
                autoSneak = true; nextSpam = now + 3 + rng.nextInt(2);
                syncPose();
                return true;
            }
            case INTERACT -> { return startInteract(e, cfg); }
            case SWAP_ITEM -> {
                if (t.hotbar().size() < 2) return false;
                swapItem(); setCooldown(ty); return true;
            }
            case SWING -> {
                if (e instanceof LivingEntity le) le.swingMainHand();
                setCooldown(ty); return true;
            }
        }
        return false;
    }

    // ---------------------------------------------------------------- per-tick action updates
    private void update(Active a, Entity e) {
        switch (a.type) {
            case LOOK_AROUND, TURN_AROUND, IDLE, SNEAK -> { if (now >= a.end) finish(a, false); }
            case SNEAK_SPAM -> {
                if (now >= a.end) finish(a, false);
                else if (now >= nextSpam) { autoSneak = !autoSneak; syncPose(); nextSpam = now + 3 + rng.nextInt(2); }   // ~3 crouches/second
            }
            case GREET -> {
                if (!valid(a.ent) || now >= a.end || dist(e, a.ent) > p().awareness * 1.6) finish(a, false);
                else if (now >= nextSpam) { autoSneak = !autoSneak; syncPose(); nextSpam = now + 3 + rng.nextInt(2); }
            }
            case WATCH -> { if (!valid(a.ent) || now >= a.end || dist(e, a.ent) > p().awareness * 1.6) finish(a, false); }
            case WALK, FLEE -> {
                if (!nav().isNavigating() || now >= a.end) { finish(a, false); return; }
                if (now - lastPosTick >= 40) {              // stuck detection: < 0.5 block in 2 s
                    Location here = e.getLocation();
                    if (lastPos != null && lastPos.getWorld() == here.getWorld() && lastPos.distanceSquared(here) < 0.25) {
                        a.ret = false; a.loc = null;        // counts as "could not reach"
                        cooldown.put(a.type, now + 100 + rng.nextInt(200));
                        finish(a, false); return;
                    }
                    lastPos = here; lastPosTick = now;
                }
            }
            case APPROACH -> {
                if (!valid(a.ent) || now >= a.end || !nav().isNavigating() || !insideRadius(a.ent.getLocation())) { finish(a, false); return; }
                if (dist(e, a.ent) < 3.2) {
                    nav().cancelNavigation();
                    Entity target = a.ent;
                    finish(a, false);
                    if (canOccupy(ActionType.WATCH, false)) {
                        Active w = open(ActionType.WATCH, ticks(3 + rng.nextInt(4)));
                        w.ent = target; lookEntity(e, target);
                    }
                    return;
                }
                if (now - lastPosTick >= 60) {
                    Location here = e.getLocation();
                    if (lastPos != null && lastPos.getWorld() == here.getWorld() && lastPos.distanceSquared(here) < 0.25) { finish(a, false); return; }
                    lastPos = here; lastPosTick = now;
                }
            }
            case JUMP -> {
                if (now >= nextJump && onGround(e)) { jump(e); nextJump = now + 9 + rng.nextInt(6); }
                if (now >= a.end) finish(a, false);
            }
            case SPRINT -> {
                if (now >= a.end || !isMoving()) finish(a, false);
                else if (now % 10 == 0) syncPose();         // re-assert in case Citizens resets the flag
            }
            case INTERACT -> interactUpdate(a, e);
            default -> finish(a, false);
        }
    }

    private void finish(Active a, boolean interrupted) {
        if (a.done) return;
        a.done = true;
        for (Channel ch : a.type.channels) if (slots.get(ch) == a) slots.remove(ch);
        Entity e = ent();
        switch (a.type) {
            case SPRINT -> syncPose();
            case SNEAK, SNEAK_SPAM -> { autoSneak = false; syncPose(); }
            case GREET -> { autoSneak = false; syncPose(); if (lookEnt == a.ent) lookOn = false; }
            case WATCH -> { if (lookEnt == a.ent) lookOn = false; }
            case WALK, FLEE, APPROACH -> {
                if (nav().isNavigating()) nav().cancelNavigation();
                if (!interrupted && !a.ret && e != null && a.loc != null && e.getLocation().distanceSquared(a.loc) > 16) {
                    // Couldn't reach the destination: back off and react with a quick look around.
                    cooldown.put(a.type, now + 100 + rng.nextInt(200));
                    if (canOccupy(ActionType.LOOK_AROUND, false)) {
                        open(ActionType.LOOK_AROUND, ticks(1.5));
                        lookAngles(e, e.getLocation().getYaw() + (rng.nextBoolean() ? 70 : -70), -5);
                    }
                }
            }
            case INTERACT -> { undoInteract(a); lookOn = false; lookHold = false; }
            default -> { }
        }
        if (!interrupted || a.type == ActionType.INTERACT) setCooldown(a.type);
    }

    // ---------------------------------------------------------------- movement
    private void jump(Entity e) {
        Vector v = e.getVelocity();
        v.setY(0.42);
        e.setVelocity(v);
    }

    private Active go(Entity e, ActionType ty, Location dest, long timeout, boolean ret) {
        Active a = open(ty, timeout);
        a.loc = dest; a.ret = ret;
        if (ret) a.prio = 10;                                // returning home can't be interrupted by ordinary actions
        lastPos = e.getLocation(); lastPosTick = now;
        syncPose();                                          // sets speed on the local parameters first
        nav().getLocalParameters().range((float) Math.max(30.0, e.getLocation().distance(dest) * 1.5));
        nav().setTarget(dest);
        return a;
    }

    private Location pickWander(Entity e) {
        Personality p = p();
        Location here = e.getLocation(), c = t.center();
        World w = here.getWorld();
        double R = limit();
        for (int i = 0; i < 12; i++) {
            double ang = rng.nextDouble() * Math.PI * 2, d = rand(p.walkMin, p.walkMax);
            double x = here.getX() + Math.cos(ang) * d, z = here.getZ() + Math.sin(ang) * d;
            if (c != null && c.getWorld() == w) {            // clamp into the hard boundary
                double dx = x - c.getX(), dz = z - c.getZ(), hd = Math.hypot(dx, dz), lim = R - 2;
                if (hd > lim) { x = c.getX() + dx / hd * lim; z = c.getZ() + dz / hd * lim; }
            }
            Location s = findStandable(w, x, z, here.getBlockY());
            if (s == null || s.distanceSquared(here) < 4 || !insideRadius(s)) continue;
            return s;
        }
        return null;
    }

    private Location findStandable(World w, double x, double z, int y0) {
        int bx = (int) Math.floor(x), bz = (int) Math.floor(z);
        if (!w.isChunkLoaded(bx >> 4, bz >> 4)) return null;
        int[] order = {0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6};
        for (int dy : order) {
            int y = y0 + dy;
            if (y < w.getMinHeight() + 1 || y > w.getMaxHeight() - 3) continue;
            Block floor = w.getBlockAt(bx, y - 1, bz), feet = w.getBlockAt(bx, y, bz), head = w.getBlockAt(bx, y + 1, bz);
            if (!floor.getType().isSolid() || BAD.contains(floor.getType())) continue;
            if (!feet.isPassable() || feet.isLiquid() || BAD.contains(feet.getType())) continue;
            if (!head.isPassable() || head.isLiquid()) continue;
            return new Location(w, bx + 0.5, y, bz + 0.5);
        }
        return null;
    }

    /** Hard boundary enforcement. Runs ~once per second per NPC. */
    private void boundary(Entity e) {
        Location c = t.center();
        if (c == null || c.getWorld() != e.getWorld()) return;
        double R = t.effectiveRadius();
        double hm = t.homeDistance();
        if (hm > 0 && hm <= R) return;                      // the return-home rule is stricter and handles it
        Location here = e.getLocation();
        if (c.distance(here) <= R) { outsideSince = -1; return; }
        if (outsideSince < 0) outsideSince = now;
        if (now - outsideSince > 20 * 15) {                  // could not walk back: snap to the safe side
            Location safe = findStandable(c.getWorld(), c.getX(), c.getZ(), c.getBlockY());
            t.getNPC().teleport(safe != null ? safe : c, PlayerTeleportEvent.TeleportCause.PLUGIN);
            outsideSince = -1; return;
        }
        Active m = slots.get(Channel.MOVE);
        if (m != null && m.ret) return;                      // already heading back
        Vector dir = here.toVector().subtract(c.toVector()).setY(0);
        if (dir.lengthSquared() < 0.01) return;
        dir.normalize();
        for (double f : new double[]{R - 3, R * 0.8, R * 0.5, 0}) {
            Location back = findStandable(c.getWorld(), c.getX() + dir.getX() * f, c.getZ() + dir.getZ() * f, here.getBlockY());
            if (back != null) { go(e, ActionType.WALK, back, ticks(30), true); return; }
        }
    }

    // ---------------------------------------------------------------- pose (sneak / sprint / speed)
    private void syncPose() {
        Entity e = ent();
        if (e == null) return;
        boolean sneak = manualSneak || autoSneak;
        boolean sprint = !sneak && (manualSprint || slots.get(Channel.SPRINT) != null);
        if (e instanceof Player pl) {
            if (sneak != appliedSneak) { t.getNPC().getOrAddTrait(SneakTrait.class).setSneaking(sneak); appliedSneak = sneak; }
            if (pl.isSprinting() != sprint) pl.setSprinting(sprint);
            appliedSprint = sprint;
        }
        float m = (float) p().speedMod;
        if (sneak) m *= 0.3f; else if (sprint) m *= 1.3f;
        nav().getLocalParameters().speedModifier(m);
    }

    // ---------------------------------------------------------------- head / look
    private void beginLook(Entity e) {
        if (!lookOn) {
            Location l = e.getLocation();
            curYaw = l.getYaw(); curPitch = l.getPitch(); velYaw = 0; velPitch = 0;
        }
        lookOn = true;
    }

    private void lookAngles(Entity e, float yaw, float pitch) {
        beginLook(e); lookHold = false; lookMode = LookMode.ANGLES;
        tYaw = HeadUtil.wrap(yaw); tPitch = (float) Personality.clamp(pitch, -80, 80);
    }
    private void lookEntity(Entity e, Entity tgt) { beginLook(e); lookHold = false; lookMode = LookMode.ENTITY; lookEnt = tgt; }
    private void lookLoc(Entity e, Location l) { beginLook(e); lookHold = false; lookMode = LookMode.LOC; lookLoc = l; }

    private void lookTick(Entity e) {
        if (!lookOn) return;
        float ty, tp;
        if (lookMode == LookMode.ANGLES) { ty = tYaw; tp = tPitch; }
        else {
            Location tl;
            if (lookMode == LookMode.ENTITY) {
                if (!valid(lookEnt) || lookEnt.getWorld() != e.getWorld()) { lookOn = false; return; }
                tl = lookEnt instanceof LivingEntity le ? le.getEyeLocation() : lookEnt.getLocation().add(0, 1.6, 0);
            } else tl = lookLoc;
            Location eye = e instanceof LivingEntity le2 ? le2.getEyeLocation() : e.getLocation().add(0, 1.6, 0);
            Vector d = tl.toVector().subtract(eye.toVector());
            ty = (float) Math.toDegrees(Math.atan2(-d.getX(), d.getZ()));
            tp = (float) Math.toDegrees(-Math.atan2(d.getY(), Math.hypot(d.getX(), d.getZ())));
        }
        float dy = HeadUtil.wrap(ty - curYaw), dp = tp - curPitch;
        float max = (float) p().lookSpeed;
        float desY = Math.max(-max, Math.min(max, dy * 0.22f));
        float desP = Math.max(-max * 0.6f, Math.min(max * 0.6f, dp * 0.22f));
        velYaw += (desY - velYaw) * 0.4f;                    // ease-in / ease-out: no instant snapping
        velPitch += (desP - velPitch) * 0.4f;
        curYaw = HeadUtil.wrap(curYaw + velYaw);
        curPitch = (float) Personality.clamp(curPitch + velPitch, -85, 85);
        HeadUtil.apply(e, curYaw, curPitch, nav().isNavigating());
        if (lookMode != LookMode.ENTITY && !lookHold && Math.abs(dy) < 0.4f && Math.abs(dp) < 0.4f) lookOn = false;
    }

    // ---------------------------------------------------------------- hands / items
    private void swapItem() {
        List<Material> h = t.hotbar();
        int i;
        do { i = rng.nextInt(h.size()); } while (i == hotbarIdx && h.size() > 1);
        hotbarIdx = i;
        hold(h.get(i));
    }

    void hold(Material m) {
        t.getNPC().getOrAddTrait(Equipment.class).set(Equipment.EquipmentSlot.HAND, new ItemStack(m));
    }

    // ---------------------------------------------------------------- block interaction
    private int kind(Block b) {
        Material m = b.getType();
        if (m == Material.IRON_DOOR || m == Material.IRON_TRAPDOOR) return 0;
        BlockData d = b.getBlockData();
        if (d instanceof Openable) return 1;
        if (d instanceof Switch) return 2;
        if (m == Material.CHEST || m == Material.TRAPPED_CHEST || m == Material.BARREL || m == Material.ENDER_CHEST || Tag.SHULKER_BOXES.isTagged(m)) return 3;
        if (UTILITY.contains(m)) return 4;                   // crafting table, furnace, anvil...: look + arm swing only
        return 0;
    }

    private Block findInteractive(Entity e) {
        Location l = e.getLocation();
        World w = l.getWorld();
        List<Block> found = new ArrayList<>();
        for (int dx = -3; dx <= 3; dx++) for (int dz = -3; dz <= 3; dz++) {
            int x = l.getBlockX() + dx, z = l.getBlockZ() + dz;
            if (!w.isChunkLoaded(x >> 4, z >> 4)) continue;
            for (int dy = -1; dy <= 2; dy++) {
                Block b = w.getBlockAt(x, l.getBlockY() + dy, z);
                if (kind(b) != 0) found.add(b);
            }
        }
        return found.isEmpty() ? null : found.get(rng.nextInt(found.size()));
    }

    private boolean startInteract(Entity e, ActionConfig cfg) {
        Block b = findInteractive(e);
        if (b == null) return false;
        Active a = open(ActionType.INTERACT, dur(cfg) + 100);
        a.block = b; a.phase = 0; a.next = now + 12 + rng.nextInt(10);
        a.orig = false;
        a.kind = kind(b);
        lookLoc(e, b.getLocation().add(0.5, 0.5, 0.5));
        lookHold = true;                                     // keep staring at the block until it is closed again
        a.prio = 4;                                          // not interruptible by ordinary actions
        return true;
    }

    private void interactUpdate(Active a, Entity e) {
        if (a.phase == 0 && now >= a.next) {
            doInteract(a, e);
            a.phase = 1;
            ActionConfig c = p().cfg(ActionType.INTERACT);
            a.next = now + ticks(forcedSec > 0 ? forcedSec : Math.max(1.5, rand(c.durMin, c.durMax)));
        } else if (a.phase == 1 && now >= a.next) {
            if (e instanceof LivingEntity le) le.swingMainHand();
            undoInteract(a);
            a.phase = 2; a.next = now + 12;
        } else if (a.phase == 2 && now >= a.next) finish(a, false);
        else if (now >= a.end + 200) finish(a, false);       // absolute safety net
    }

    private void doInteract(Active a, Entity e) {
        if (e instanceof LivingEntity le) le.swingMainHand();
        Block b = a.block;
        boolean mod = NPCLifePlugin.get().getConfig().getBoolean("modify-world", true);
        a.kind = kind(b);
        switch (a.kind) {
            case 1 -> {
                if (!mod) return;
                a.orig = ((Openable) b.getBlockData()).isOpen();
                setOpen(b, !a.orig); sound(b, !a.orig); a.changed = true;
            }
            case 2 -> {
                if (!mod) return;
                Powerable pw = (Powerable) b.getBlockData();
                a.orig = pw.isPowered();
                if (Tag.BUTTONS.isTagged(b.getType())) {
                    if (a.orig) return;
                    setPowered(b, true); sound(b, true);
                    long delay = Tag.WOODEN_BUTTONS.isTagged(b.getType()) ? 30L : 20L;
                    Bukkit.getScheduler().runTaskLater(NPCLifePlugin.get(), () -> setPowered(b, false), delay);
                } else { setPowered(b, !a.orig); sound(b, !a.orig); a.changed = true; }
            }
            case 3 -> { if (b.getState() instanceof Lidded l) { l.open(); a.changed = true; } }
            default -> { }
        }
    }

    private void undoInteract(Active a) {
        if (!a.changed || a.block == null) return;
        a.changed = false;
        Block b = a.block;
        switch (a.kind) {
            case 1 -> { setOpen(b, a.orig); sound(b, a.orig); }
            case 2 -> { setPowered(b, a.orig); sound(b, a.orig); }
            case 3 -> { if (b.getState() instanceof Lidded l) l.close(); }
            default -> { }
        }
    }

    private void setOpen(Block b, boolean open) {
        BlockData d = b.getBlockData();
        if (!(d instanceof Openable o)) return;
        o.setOpen(open);
        b.setBlockData(d, true);
        if (d instanceof Door door) {                        // doors are two blocks tall
            Block other = door.getHalf() == Bisected.Half.BOTTOM ? b.getRelative(BlockFace.UP) : b.getRelative(BlockFace.DOWN);
            BlockData od = other.getBlockData();
            if (od instanceof Openable oo) { oo.setOpen(open); other.setBlockData(od, true); }
        }
    }

    private static void setPowered(Block b, boolean on) {
        BlockData d = b.getBlockData();
        if (d instanceof Powerable pw) { pw.setPowered(on); b.setBlockData(d, true); }
    }

    private void sound(Block b, boolean open) {
        Material m = b.getType();
        Sound s;
        if (Tag.DOORS.isTagged(m)) s = open ? Sound.BLOCK_WOODEN_DOOR_OPEN : Sound.BLOCK_WOODEN_DOOR_CLOSE;
        else if (Tag.TRAPDOORS.isTagged(m)) s = open ? Sound.BLOCK_WOODEN_TRAPDOOR_OPEN : Sound.BLOCK_WOODEN_TRAPDOOR_CLOSE;
        else if (Tag.FENCE_GATES.isTagged(m)) s = open ? Sound.BLOCK_FENCE_GATE_OPEN : Sound.BLOCK_FENCE_GATE_CLOSE;
        else s = Sound.BLOCK_LEVER_CLICK;
        b.getWorld().playSound(b.getLocation().add(0.5, 0.5, 0.5), s, SoundCategory.BLOCKS, 1f, 0.9f + rng.nextFloat() * 0.2f);
    }

    // ---------------------------------------------------------------- homing: return to the spawn point
    private double limit() {
        double r = t.effectiveRadius(), h = t.homeDistance();
        return h > 0 ? Math.min(r, h - 1) : r;
    }

    /** Further than home-distance for 20 s -> walk back; if not back within 2 min -> teleport. Runs for ALL NPCs. */
    private void homing(Entity e) {
        double h = t.homeDistance();
        Location c = t.center();
        if (h <= 0 || c == null || c.getWorld() != e.getWorld() || seq != null) { homeOutsideSince = -1; homeWalkStart = -1; return; }
        Location here = e.getLocation();
        double d = c.distance(here);
        if (d <= h) { homeOutsideSince = -1; homeWalkStart = -1; return; }
        if (homeOutsideSince < 0) homeOutsideSince = now;
        long wait = ticks(NPCLifePlugin.get().getConfig().getDouble("return-wait-seconds", 20));
        if (now - homeOutsideSince < wait) return;
        if (homeWalkStart < 0) homeWalkStart = now;
        long limit = ticks(NPCLifePlugin.get().getConfig().getDouble("return-timeout-seconds", 120));
        if (now - homeWalkStart >= limit) { teleportHome(c); return; }
        Active m = slots.get(Channel.MOVE);
        if (m != null && m.ret) return;                      // already walking back
        Vector dir = c.toVector().subtract(here.toVector()).setY(0);
        if (dir.lengthSquared() < 0.01) { teleportHome(c); return; }
        dir.normalize();
        for (double step : new double[]{Math.min(d, 24), 16, 10, 5}) {   // walk back in hops of up to 24 blocks
            Location hop = findStandable(c.getWorld(), here.getX() + dir.getX() * step, here.getZ() + dir.getZ() * step, here.getBlockY());
            if (hop != null) { go(e, ActionType.WALK, hop, ticks(35), true); return; }
        }
    }

    private void teleportHome(Location c) {
        Location safe = findStandable(c.getWorld(), c.getX(), c.getZ(), c.getBlockY());
        t.getNPC().teleport(safe != null ? safe : c, PlayerTeleportEvent.TeleportCause.PLUGIN);
        homeOutsideSince = -1; homeWalkStart = -1;
    }

    // ---------------------------------------------------------------- sprint-jump
    private void sprintJumpTick(Entity e) {
        if (nav().isNavigating()) {
            if (now >= nextJump && onGround(e)) { jump(e); nextJump = now + 10; }
        } else if (slots.get(Channel.MOVE) == null && now >= nextSJ) {
            nextSJ = now + 20;
            force(ActionType.WALK, -1);                      // keep travelling so it really sprint-jumps forward
        }
    }

    void setSprintJump(boolean v) { sprintJump = v; setManualSprint(v); nextSJ = 0; }
    boolean sprintJump() { return sprintJump; }

    // ---------------------------------------------------------------- use item (right-click hold poses)
    void setUseContinuous(boolean v) { useCont = v; nextUse = 0; if (!v) stopUse(); }
    boolean useContinuous() { return useCont; }
    void useFor(double sec) { useUntil = now + ticks(sec); nextUse = 0; }
    void stopUse() {
        useCont = false; useUntil = 0;
        Entity e = ent();
        if (e != null) AnimUtil.play(e, "STOP_USE_ITEM");
    }

    // ---------------------------------------------------------------- sequences
    private static double[] parseRange(String s) {
        String[] p = s.split("-");
        double a = Double.parseDouble(p[0]), b = p.length > 1 ? Double.parseDouble(p[1]) : a;
        return new double[]{Math.min(a, b), Math.max(a, b)};
    }

    void startSequence(List<String> steps, boolean loop, boolean combine, Location origin) {
        stopSequence();
        seq = new ArrayList<>(steps); seqIdx = 0; seqLoop = loop; seqCombine = combine;
        seqOrigin = origin; seqWaitUntil = 0; seqBlock = null;
    }

    void stopSequence() {
        if (seq == null) return;
        seq = null; seqBlock = null;
        Active m = slots.get(Channel.MOVE);
        if (m != null && m.prio == 50) finish(m, true);
        stopLook();
        manualSneak = false; manualSprint = false; manualHop = false;
        syncPose();
        stopUse();
    }

    /** Called when the NPC despawns: forget runtime state but keep the persisted sequence name on the trait. */
    void clearSequenceState() { seq = null; seqBlock = null; seqChecked = false; }

    private void seqTick(Entity e) {
        if (seq == null || now < seqWaitUntil) return;
        if (seqBlock != null) { if (!seqBlock.done) return; seqBlock = null; }
        for (int guard = 0; guard < 40; guard++) {
            if (seqIdx >= seq.size()) {
                if (seqLoop && !seq.isEmpty()) { seqIdx = 0; seqWaitUntil = now + 10; }
                else stopSequence();
                return;
            }
            seqExec(e, seq.get(seqIdx++).trim());
            if (seq == null || seqBlock != null || now < seqWaitUntil) return;
        }
    }

    /** Step grammar: [?NN] [IFNEAR] COMMAND args...   (?NN = NN% chance to run, IFNEAR = only if a player is close) */
    private void seqExec(Entity e, String line) {
        if (line.isEmpty() || line.startsWith("#")) return;
        String[] tk = line.split("\\s+");
        int i = 0;
        while (i < tk.length) {
            if (tk[i].startsWith("?")) {
                double pr;
                try { pr = Double.parseDouble(tk[i].substring(1)); } catch (NumberFormatException ex) { return; }
                if (rng.nextDouble() * 100 >= pr) return;
                i++;
            } else if (tk[i].equalsIgnoreCase("IFNEAR")) {
                Ctx c = new Ctx(); scan(c, e);
                if (c.player == null) return;
                i++;
            } else break;
        }
        if (i >= tk.length) return;
        String cmd = tk[i].toUpperCase(Locale.ROOT);
        String[] a = Arrays.copyOfRange(tk, i + 1, tk.length);
        try {
            switch (cmd) {
                case "WAIT" -> { double[] r = a.length > 0 ? parseRange(a[0]) : new double[]{1, 1}; seqWaitUntil = now + ticks(rand(r[0], r[1])); }
                case "WALK", "WALKABS" -> {
                    if (a.length < 3) return;
                    double x = Double.parseDouble(a[0]), y = Double.parseDouble(a[1]), z = Double.parseDouble(a[2]);
                    if (cmd.equals("WALK") && seqOrigin != null) { x += seqOrigin.getX(); y += seqOrigin.getY(); z += seqOrigin.getZ(); }
                    Location dest = findStandable(e.getWorld(), x, z, (int) Math.floor(y));
                    if (dest == null) return;
                    Active wk = go(e, ActionType.WALK, dest, ticks(Math.max(10, e.getLocation().distance(dest) / 2.0 + 5)), false);
                    wk.prio = 50;
                    seqBlock = wk;
                }
                case "LOOK" -> { if (a.length >= 2) manualLookAngles(Float.parseFloat(a[0]), Float.parseFloat(a[1])); }
                case "LOOKAT" -> { if (a.length >= 3) manualLookAt(new Location(e.getWorld(), Double.parseDouble(a[0]), Double.parseDouble(a[1]), Double.parseDouble(a[2]))); }
                case "LOOKPLAYER" -> { Ctx c = new Ctx(); scan(c, e); if (c.player != null) manualLookEntity(c.player); }
                case "LOOKFREE" -> stopLook();
                case "JUMP" -> jumpNow();
                case "HOP" -> force(ActionType.JUMP, a.length > 0 ? Double.parseDouble(a[0]) : 2);
                case "SPRINT" -> setManualSprint(a.length > 0 && a[0].equalsIgnoreCase("on"));
                case "SNEAK" -> setManualSneak(a.length > 0 && a[0].equalsIgnoreCase("on"));
                case "SPAM" -> force(ActionType.SNEAK_SPAM, a.length > 0 ? Double.parseDouble(a[0]) : 2);
                case "SWING" -> swing(false);
                case "WAVE" -> wave();
                case "INTERACT" -> { if (force(ActionType.INTERACT, -1)) seqBlock = slots.get(Channel.MOVE); }
                case "HOLD" -> { Material m = a.length > 0 ? Material.matchMaterial(a[0]) : null; if (m != null) hold(m); }
                case "USE" -> { if (a.length > 0 && a[0].equalsIgnoreCase("off")) stopUse(); else setUseContinuous(true); }
                default -> { }
            }
        } catch (RuntimeException ex) {
            // malformed step: skip it rather than breaking the whole sequence
        }
    }

    // ---------------------------------------------------------------- manual API (used by commands)
    void setManualSneak(boolean v) { manualSneak = v; syncPose(); }
    void setManualSprint(boolean v) { manualSprint = v; syncPose(); }
    void setManualHop(boolean v) { manualHop = v; }
    boolean manualSneak() { return manualSneak; }
    boolean manualSprint() { return manualSprint; }
    boolean manualHop() { return manualHop; }

    void jumpNow() { Entity e = ent(); if (e != null && onGround(e)) jump(e); }

    void swing(boolean offhand) {
        Entity e = ent();
        if (e instanceof LivingEntity le) { if (offhand) le.swingOffHand(); else le.swingMainHand(); }
    }

    void wave() {
        for (int i = 0; i < 4; i++)
            Bukkit.getScheduler().runTaskLater(NPCLifePlugin.get(), () -> swing(true), i * 7L);
    }

    /** Start an action right now (ignores probability/cooldown, interrupts lower things). */
    boolean force(ActionType ty, double seconds) {
        Entity e = ent();
        if (e == null) return false;
        now = Math.max(now, 0);
        forcedSec = seconds;
        try { return tryStart(ty, p().cfg(ty), e, new Ctx()); } finally { forcedSec = -1; }
    }

    private Active manualHead() {
        Active a = open(ActionType.LOOK_AROUND, ticks(3600));
        a.prio = 99;
        return a;
    }
    void manualLookAngles(float yaw, float pitch) { Entity e = ent(); if (e == null) return; manualHead(); lookAngles(e, yaw, pitch); }
    void manualLookAt(Location l) { Entity e = ent(); if (e == null) return; manualHead(); lookLoc(e, l); }
    void manualLookEntity(Entity tgt) { Entity e = ent(); if (e == null) return; Active a = manualHead(); a.ent = tgt; lookEntity(e, tgt); }
    void stopLook() {
        Active a = slots.get(Channel.HEAD);
        if (a != null) finish(a, true);
        lookOn = false;
    }

    void stopAll() {
        stopSequence();
        for (Active a : new LinkedHashSet<>(slots.values())) finish(a, true);
        lookOn = false; manualHop = false; manualSneak = false; manualSprint = false; sprintJump = false;
        stopUse();
        if (ent() != null) nav().cancelNavigation();
        syncPose();
    }

    String describe() {
        StringBuilder sb = new StringBuilder();
        for (Channel ch : Channel.values()) {
            Active a = slots.get(ch);
            if (a != null && a.primary == ch) sb.append(a.type.name().toLowerCase()).append("(").append(Math.max(0, (a.end - now) / 20)).append("s) ");
        }
        if (manualHop) sb.append("[manual-hop] ");
        if (manualSneak) sb.append("[manual-sneak] ");
        if (manualSprint) sb.append("[manual-sprint] ");
        if (sprintJump) sb.append("[sprint-jump] ");
        if (useCont) sb.append("[use-continuous] ");
        if (seq != null) sb.append("[sequence ").append(seqIdx).append("/").append(seq.size()).append("] ");
        return sb.length() == 0 ? "nothing" : sb.toString().trim();
    }
}
