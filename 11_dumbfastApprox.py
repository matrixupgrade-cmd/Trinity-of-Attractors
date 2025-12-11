import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from IPython.display import HTML

# =============================
# Villager with Symmetry Gene
# to show metamorphis theorem can quickly approximate believable behavior
# but without mounds of calculation just approximating what occurs in 3 states
# solid they stabalize, liquid they follow a gradient, entropy they wonder
# the symmetric score gives them alternatives
# villagers between symmetries end up forming thier own village with a dumb fast approximator
# end gold of coupling games end in one of those 3 states.
# =============================
class Villager:
    def __init__(self, pos, symmetry_score=None):
        self.pos = np.array(pos, dtype=float)
        self.symmetry_score = symmetry_score if symmetry_score is not None else np.random.rand()
        # 0.0 = pure selfish noise, 1.0 = pure cooperative gradient-follower
        self.phase = "plasma"

    def move(self, field):
        x, y = self.pos.astype(int)
        x, y = np.clip(x, 1, field.shape[1]-2), np.clip(y, 1, field.shape[0]-2)

        # Compute simple centered gradient
        gx = field[y, x+1] - field[y, x-1]
        gy = field[y+1, x] - field[y, x-1]
        grad = np.array([gx, gy])
        grad_norm = np.linalg.norm(grad) + 1e-8
        grad_dir = grad / grad_norm

        if self.phase == "plasma":
            step = np.random.randn(2) * 0.8
        elif self.phase == "liquid":
            # symmetry_score interpolates between pure gradient and pure noise
            step = grad_dir * self.symmetry_score + np.random.randn(2) * (1 - self.symmetry_score)
        else:  # solid
            step = np.zeros(2)

        self.pos += step * 0.7
        self.pos = np.clip(self.pos, 1, field.shape[0]-2)

        # Phase transition based on local field strength
        local = field[y, x]
        if local > 0.75:
            self.phase = "solid"
        elif local < 0.15:
            self.phase = "plasma"
        else:
            self.phase = "liquid"

# =============================
# World with diffusive signal
# =============================
class World:
    def __init__(self, size=60, num_villagers=120):
        self.size = size
        self.field = np.zeros((size, size))
        self.villagers = [Villager(np.random.uniform(5, size-5, 2)) for _ in range(num_villagers)]

        # Place one bright attractor in the center (the "god", the "danger", the "truth")
        cy, cx = size//2, size//2
        self.field[cy, cx] = 1.0

    def step(self):
        # Laplace diffusion (poor man's heat equation)
        self.field = (self.field +
                      np.roll(self.field, 1, 0) + np.roll(self.field, -1, 0) +
                      np.roll(self.field, 1, 1) + np.roll(self.field, -1, 1)) / 5.0

        # Slight decay so distant areas stay dark
        self.field *= 0.995

        for v in self.villagers:
            v.move(self.field)

# =============================
# Run the pilgrimage
# =============================
def run_pilgrimage(steps=350):
    world = World(size=70, num_villagers=180)

    fig, ax = plt.subplots(figsize=(8,8))
    im = ax.imshow(world.field, cmap='inferno', origin='lower', vmin=0, vmax=0.9)
    scat = ax.scatter([], [], s=40, c='cyan', edgecolors='white', linewidth=0.5, alpha=0.9)

    def update(frame):
        for _ in range(4):
            world.step()

        im.set_data(world.field)
        pos = np.array([v.pos for v in world.villagers])
        colors = [plt.cm.winter(v.symmetry_score) for v in world.villagers]
        scat.set_offsets(pos)
        scat.set_color(colors)

        solid = sum(1 for v in world.villagers if v.phase == "solid")
        ax.set_title(f"Day {frame:3d} • Converged souls: {solid}/{len(world.villagers)}", 
                     color='white', fontsize=14)
        ax.set_facecolor('black')
        ax.axis('off')
        return im, scat

    anim = FuncAnimation(fig, update, frames=steps, interval=80, repeat=False, blit=False)
    plt.close(fig)
    return HTML(anim.to_jshtml())

# Watch what symmetry does to a species
run_pilgrimage(steps=400)
