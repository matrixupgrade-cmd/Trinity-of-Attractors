import numpy as np
import matplotlib.pyplot as plt

# -----------------------------
# 1. Base Hybrid Spider System
# -----------------------------

class HybridSystem:
    def __init__(self, timescale=1.0):
        self.timescale = timescale  # lower = faster updates

class Spider:
    def __init__(self, tension_fn, timescale=1.0, persistence=4):
        self.tension_fn = tension_fn
        self.timescale = timescale
        self.persistence = persistence
        self.alive = True

    def tension(self, state):
        return self.tension_fn(state)

class Goal:
    def __init__(self, predicate=lambda s: True, clarity=0.0):
        self.predicate = predicate
        self.clarity = clarity

class MetaState:
    def __init__(self, goal, spiders):
        self.goal = goal
        self.spiders = spiders
        self.generation = 0

# -----------------------------
# 2. Step function with timescale ordering
# -----------------------------

def step(meta):
    """Meta-step: spiders act in order of their timescales (fastest first)"""
    # Sort spiders by timescale (lower = faster)
    active_spiders = sorted([sp for sp in meta.spiders if sp.alive],
                            key=lambda sp: sp.timescale)
    new_goal_clarity = meta.goal.clarity
    for sp in active_spiders:
        # Apply spider: increase clarity by tension * persistence
        new_goal_clarity += sp.tension(0.5) * sp.persistence
        # Optional: small randomness to simulate dynamic interactions
        new_goal_clarity += np.random.uniform(-0.1, 0.1)
    new_meta = MetaState(meta.goal, meta.spiders)
    new_meta.goal.clarity = max(new_goal_clarity, 0.0)
    new_meta.generation = meta.generation + 1
    return new_meta

# -----------------------------
# 3. Orbit and phase detection
# -----------------------------

def orbit(meta0, steps):
    orbit_list = [meta0]
    current = meta0
    for _ in range(steps):
        current = step(current)
        orbit_list.append(current)
    return orbit_list

def detect_phase(orbit_list, tolerance=1e-3):
    clarities = [m.goal.clarity for m in orbit_list]
    diffs = np.diff(clarities)
    if np.all(diffs > tolerance):
        return "Plasma"
    elif np.any(np.abs(diffs) < tolerance):
        return "Diamond"
    else:
        return "Liquid"

# -----------------------------
# 4. Example: nested system
# -----------------------------

# Define spiders with different timescales
sp1 = Spider(lambda s: 1.0, timescale=0.5)  # fast
sp2 = Spider(lambda s: 0.5, timescale=1.0)  # slower
sp3 = Spider(lambda s: 0.8, timescale=0.8)  # intermediate

goal = Goal(lambda s: True)
meta0 = MetaState(goal, [sp1, sp2, sp3])

orbit_list = orbit(meta0, 50)
phase = detect_phase(orbit_list)

print("Orbit clarities:", [round(m.goal.clarity,2) for m in orbit_list])
print("Detected phase:", phase)

# -----------------------------
# 5. Plot orbit clarity
# -----------------------------

plt.plot([m.goal.clarity for m in orbit_list], marker='o')
plt.xlabel("Step")
plt.ylabel("MetaState Clarity")
plt.title(f"Nested Hybrid Spider System Phase: {phase}")
plt.show()
