import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation

# ================================================================
# PARAMETERS
# ================================================================

GRID_W = 120
GRID_H = 60

BALL_RADIUS = 6
BALL_CENTER = (30, GRID_H // 2)

PROBE_POS = [GRID_W - 5, GRID_H // 2]

NUM_SPIDERS_PER_CELL = 5

# phases encoded as ints
SOLID = 0
LIQUID = 1
PLASMA = 2

# hole configuration
HOLE_X = 60
HOLE_TOP = 20
HOLE_BOTTOM = 40
HOLE_GAP = 4  # size of each hole

# screen x-position (where plasma hits are recorded)
SCREEN_X = 5


# ================================================================
# INITIALIZATION
# ================================================================

# grid storing spider phase and counts
spider_phase = np.full((GRID_W, GRID_H), SOLID, dtype=np.int8)
spider_count = np.zeros((GRID_W, GRID_H), dtype=np.int32)

# screen hit recorder
screen_hits = np.zeros((GRID_H,), dtype=np.int32)

# world background mask (0 = empty, 1 = wall)
world = np.zeros((GRID_W, GRID_H), dtype=np.int8)


# ------------------------------
# Create BALL of solid spiders
# ------------------------------
for x in range(GRID_W):
    for y in range(GRID_H):
        dx = x - BALL_CENTER[0]
        dy = y - BALL_CENTER[1]
        if dx*dx + dy*dy <= BALL_RADIUS * BALL_RADIUS:
            spider_count[x, y] = NUM_SPIDERS_PER_CELL
            spider_phase[x, y] = SOLID


# ------------------------------
# Create WALL with TWO HOLES
# ------------------------------
for y in range(GRID_H):
    # default wall
    world[HOLE_X, y] = 1

# carve holes
for y in range(HOLE_TOP, HOLE_TOP + HOLE_GAP):
    world[HOLE_X, y] = 0

for y in range(HOLE_BOTTOM, HOLE_BOTTOM + HOLE_GAP):
    world[HOLE_X, y] = 0


# ================================================================
# HELPERS
# ================================================================

def shift_world_background():
    """Shift WALL to the right by 1 (makes ball appear to move left)."""
    global world
    world = np.roll(world, shift=1, axis=0)


def hit_ball_with_probe():
    """Check if probe touches ball; if yes → all spiders become LIQUID."""
    px, py = PROBE_POS
    if px < 0 or px >= GRID_W:
        return False

    # if any spiders in that location
    if spider_count[px, py] > 0:
        # metamorphosis: make ALL ball spiders LIQUID
        mask = spider_count > 0
        spider_phase[mask] = LIQUID
        return True
    return False


def move_probe():
    """Probe moves left by 1."""
    PROBE_POS[0] -= 1


def liquid_flow():
    """Each liquid spider randomly moves to a neighbor cell."""
    global spider_count, spider_phase

    new_counts = np.zeros_like(spider_count)
    new_phase = np.copy(spider_phase)

    for x in range(GRID_W):
        for y in range(GRID_H):
            if spider_phase[x, y] == LIQUID:
                count = spider_count[x, y]
                for _ in range(count):
                    # choose random neighbor
                    nx = x + np.random.choice([-1, 0, 1])
                    ny = y + np.random.choice([-1, 0, 1])
                    if 0 <= nx < GRID_W and 0 <= ny < GRID_H:
                        new_counts[nx, ny] += 1
                        new_phase[nx, ny] = LIQUID
            else:
                # keep spiders in place
                new_counts[x, y] += spider_count[x, y]

    spider_count = new_counts
    spider_phase = new_phase


def liquid_to_plasma_near_hole():
    """If liquid spider touches a hole boundary → become plasma."""
    for y in range(GRID_H):
        if world[HOLE_X, y] == 0:  # hole cell
            # left side of hole
            for dy in [-1, 0, 1]:
                yy = y + dy
                if 0 <= yy < GRID_H:
                    x = HOLE_X - 1
                    if spider_phase[x, yy] == LIQUID:
                        spider_phase[x, yy] = PLASMA


def plasma_spray():
    """Plasma spiders move randomly outward (entropy expansion)."""
    global spider_count, spider_phase, screen_hits

    new_counts = np.zeros_like(spider_count)
    new_phase = np.copy(spider_phase)

    for x in range(GRID_W):
        for y in range(GRID_H):
            if spider_phase[x, y] == PLASMA:
                count = spider_count[x, y]
                for _ in range(count):
                    # spray outward (biased leftwards)
                    nx = x + np.random.choice([-1, -1, -2])
                    ny = y + np.random.choice([-1, 0, 1])

                    # SCREEN HIT
                    if nx == SCREEN_X and 0 <= ny < GRID_H:
                        screen_hits[ny] += 1
                        continue

                    # otherwise move plasma
                    if 0 <= nx < GRID_W and 0 <= ny < GRID_H:
                        new_counts[nx, ny] += 1
                        new_phase[nx, ny] = PLASMA
            else:
                # keep spiders in place
                new_counts[x, y] += spider_count[x, y]

    spider_count = new_counts
    spider_phase = new_phase


# ================================================================
# VISUALIZATION SETUP
# ================================================================

fig, ax = plt.subplots(figsize=(10, 5))
img = ax.imshow(world.T, cmap="gray_r", origin="lower", vmin=0, vmax=3)
ax.set_title("Spider Ball Metamorphosis")


def frame(_):
    shift_world_background()
    move_probe()
    hit_ball_with_probe()
    liquid_flow()
    liquid_to_plasma_near_hole()
    plasma_spray()

    # build draw grid: combine world + spider phases
    draw = world.copy().astype(float)
    draw += (spider_phase > SOLID) * 0.5  # show phases lightly

    img.set_data(draw.T)
    return [img]


ani = FuncAnimation(fig, frame, interval=60)
plt.show()

# After the animation, show the screen hit pattern
plt.figure(figsize=(6,4))
plt.plot(screen_hits)
plt.title("Screen Hits (Plasma Spray Density)")
plt.xlabel("Screen Y-position")
plt.ylabel("Hits")
plt.show()
