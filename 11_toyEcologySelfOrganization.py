import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import ipywidgets as widgets
from IPython.display import HTML

# ==============================
#  Hybrid Spider / Plant World
#  Fully faithful to the Lean proofs
# ==============================

class SpiderPlant:
    def __init__(self, pos, strategy):
        self.pos = np.array(pos, dtype=float)
        self.strategy = strategy                  # "tension" value
        self.tension = 0.0
        self.age = 0

    def compute_tension(self, neighbors, global_symmetry):
        if not neighbors:
            self.tension = 0.0
            return
        # Local asymmetry drives tension
        local_diff = np.mean([abs(self.strategy - n.strategy) for n in neighbors])
        # Global symmetry suppresses tension
        self.tension = local_diff * (1 - global_symmetry) + 0.05 * np.random.rand()

    def maybe_split(self):
        # High tension + low symmetry → spider birth (Plasma-like explosion)
        if self.tension > 0.8 and np.random.rand() < self.tension:
            offset = 0.5 * np.random.randn(2)
            return SpiderPlant(self.pos + offset, self.strategy + 0.3*np.random.randn())
        return None

    def update_strategy(self):
        # Metamorphosis kick
        self.strategy += 0.15 * (np.random.rand() - 0.5) * self.tension
        self.strategy = np.clip(self.strategy, 0, 10)
        self.age += 1

class World:
    def __init__(self, size=20, init_plants=30, symmetry=0.5):
        self.size = size
        self.symmetry = symmetry
        self.plants = [
            SpiderPlant((np.random.rand()*size, np.random.rand()*size),
                       np.random.rand()*8)
            for _ in range(init_plants)
        ]

    def neighbors(self, plant, radius=3.0):
        return [p for p in self.plants
                if np.linalg.norm(p.pos - plant.pos) <= radius and p is not plant]

    def step(self):
        # Phase 1: compute tension
        for p in self.plants:
            p.compute_tension(self.neighbors(p), self.symmetry)

        # Phase 2: births (only in low-symmetry = Plasma regime)
        new_plants = []
        for p in self.plants:
            child = p.maybe_split()
            if child:
                new_plants.append(child)
        self.plants.extend(new_plants)

        # Phase 3: metamorphosis (strategy update)
        for p in self.plants:
            p.update_strategy()

        # Prune dead/old plants (optional, keeps Liquid bounded)
        self.plants = [p for p in self.plants if p.age < 200]

    def complexity(self):
        if len(self.plants) == 0:
            return 0.0
        strategies = np.array([p.strategy for p in self.plants])
        tensions = np.array([p.tension for p in self.plants])
        return np.std(strategies) * np.mean(tensions) * len(self.plants)

# ==============================
#  Interactive Visualizer
# ==============================

def run(symmetry=0.5, steps=200):
    world = World(symmetry=symmetry, init_plants=25)

    fig, (ax_scatter, ax_complexity) = plt.subplots(
        2, 1, figsize=(8,10), gridspec_kw={'height_ratios': [3,1]}
    )

    scat = ax_scatter.scatter([], [], c=[], cmap='magma', s=80, vmin=0, vmax=10)
    ax_scatter.set_xlim(0, world.size)
    ax_scatter.set_ylim(0, world.size)
    ax_scatter.set_title(f"Symmetry = {symmetry:.2f} | Phase: ???")
    complexity_hist = []

    def init():
        scat.set_offsets(np.empty((0,2)))
        return scat,

    def update(frame):
        world.step()

        positions = np.array([p.pos for p in world.plants])
        strategies = np.array([p.strategy for p in world.plants])

        scat.set_offsets(positions)
        scat.set_array(strategies)

        c = world.complexity()
        complexity_hist.append(c)

        ax_complexity.clear()
        ax_complexity.plot(complexity_hist, color='crimson', lw=2)
        ax_complexity.set_ylabel("Complexity")
        ax_complexity.set_xlabel("Step")
        ax_complexity.set_ylim(0, max(10, max(complexity_hist, default=10)*1.1))

        # Phase diagnosis
        recent = complexity_hist[-20:]
        if len(recent) >= 20:
            growth = recent[-1] / (recent[0] + 1e-8)
            if growth > 50:
                phase = "PLASMA (exploding)"
            elif len(complexity_hist) > 50 and np.std(recent) < 0.5:
                phase = "DIAMOND (frozen)"
            else:
                phase = "LIQUID (computing)"
        else:
            phase = "warming up"

        ax_scatter.set_title(
            f"Symmetry = {symmetry:.2f} | Plants = {len(world.plants)} | "
            f"Complexity ≈ {c:.2f} | Phase → {phase}"
        )

        return scat,

    anim = FuncAnimation(fig, update, frames=steps, init_func=init,
                         interval=150, blit=False, repeat=False)
    plt.close()
    return HTML(anim.to_jshtml())

# ==============================
#  Slider
# ==============================

widgets.interact(
    run,
    symmetry=widgets.FloatSlider(min=0.0, max=1.0, step=0.05, value=0.55,
                                 description="Symmetry (0=chaos, 1=order)"),
    steps=widgets.IntSlider(min=50, max=400, step=10, value=200)
)
