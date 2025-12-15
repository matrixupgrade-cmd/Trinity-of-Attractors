import numpy as np
import matplotlib.pyplot as plt

# -----------------------------
# 1. Meta-Cognitive Hybrid Spider System with nested sub-spiders
# -----------------------------

class MetaSpider:
    def __init__(self, name, base_tension, timescale=1.0, persistence=4, goal_bias=None, sub_spiders=None):
        self.name = name
        self.base_tension = base_tension
        self.timescale = timescale  # lower = faster
        self.persistence = persistence
        self.alive = True
        self.goal_bias = goal_bias if goal_bias is not None else [1.0] * 3
        self.sub_spiders = sub_spiders if sub_spiders is not None else []

    def tension(self):
        # Sub-spiders contribute to this spider's effective tension
        sub_influence = sum(sp.tension() for sp in self.sub_spiders)
        return self.base_tension + 0.5 * sub_influence

class MetaGoal:
    def __init__(self, name, clarity=5.0):
        self.name = name
        self.clarity = clarity

class MetaState:
    def __init__(self, goals, spiders):
        self.goals = goals
        self.spiders = spiders
        self.generation = 0

# -----------------------------
# 2. Step function with nested sub-spider influence
# -----------------------------

def step(meta):
    # Process spiders in order of timescale (fastest first)
    active_spiders = sorted([sp for sp in meta.spiders if sp.alive],
                            key=lambda sp: sp.timescale)
    
    new_goals = [MetaGoal(g.name, g.clarity) for g in meta.goals]
    new_meta = MetaState(new_goals, meta.spiders)
    new_meta.generation = meta.generation + 1
    
    total_drive = sum(sp.tension() * sp.persistence for sp in active_spiders)
    
    if total_drive > 0:
        for sp in active_spiders:
            bias = np.array(sp.goal_bias)
            noise = np.random.dirichlet(np.ones(len(meta.goals)) * 0.5)
            allocation = 0.7 * bias + 0.3 * noise
            allocation /= allocation.sum()
            
            contribution = sp.tension() * sp.persistence * np.random.uniform(0.8, 1.2)
            
            for i, g in enumerate(new_meta.goals):
                g.clarity += contribution * allocation[i]
    
    # Mild decay
    for g in new_meta.goals:
        g.clarity = max(g.clarity * 0.98, 0.0)
    
    # Recursively step sub-spiders
    for sp in meta.spiders:
        if sp.sub_spiders:
            sub_meta = MetaState(new_meta.goals, sp.sub_spiders)
            updated_sub_meta = step(sub_meta)
            # Sub-spiders feedback into parent spider (increase effective clarity)
            for g_parent, g_sub in zip(new_meta.goals, updated_sub_meta.goals):
                g_parent.clarity += 0.2 * (g_sub.clarity - g_parent.clarity)
    
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

def detect_phase(orbit_list, window=10, tol=0.5):
    if len(orbit_list) < window + 1:
        return "Unknown"
    
    recent = orbit_list[-window:]
    total_clarities = [sum(g.clarity for g in m.goals) for m in recent]
    diffs = np.abs(np.diff(total_clarities))
    variance = np.var(total_clarities)
    
    if variance > 100 and np.mean(diffs) > 2:
        return "Plasma"
    elif np.max(diffs) < tol and variance < 20:
        return "Diamond"
    else:
        return "Liquid"

# -----------------------------
# 4. Define goals and nested spiders
# -----------------------------

goals = [
    MetaGoal("Work", clarity=10.0),
    MetaGoal("Health", clarity=10.0),
    MetaGoal("Creativity", clarity=10.0)
]

# Sub-spiders: internal impulses for each main spider
sub_spiders_fast = [
    MetaSpider("Impulsive Creativity", base_tension=0.5, timescale=0.1, persistence=2,
               goal_bias=[0.1,0.1,0.8])
]

sub_spiders_medium = [
    MetaSpider("Planner Adjuster", base_tension=0.4, timescale=0.2, persistence=3,
               goal_bias=[0.7,0.2,0.1])
]

spiders = [
    MetaSpider("Fast Urge (Distraction)", base_tension=1.2, timescale=0.3, persistence=6,
               goal_bias=[0.1,0.2,0.7], sub_spiders=sub_spiders_fast),
    MetaSpider("Medium Planner (Duty)", base_tension=0.9, timescale=0.7, persistence=8,
               goal_bias=[0.8,0.1,0.1], sub_spiders=sub_spiders_medium),
    MetaSpider("Slow Wisdom (Balance)", base_tension=0.6, timescale=1.2, persistence=10,
               goal_bias=[0.2,0.6,0.2]),
    MetaSpider("Random Impulse", base_tension=1.0, timescale=0.5, persistence=5,
               goal_bias=[0.4,0.3,0.3])
]

meta0 = MetaState(goals, spiders)

# -----------------------------
# 5. Run simulation
# -----------------------------

steps = 100
orbit_list = orbit(meta0, steps)
phase = detect_phase(orbit_list)

print(f"Detected phase after {steps} steps: {phase}\n")
print("Final clarity levels:")
for g in orbit_list[-1].goals:
    print(f"  {g.name}: {g.clarity:.2f}")

# -----------------------------
# 6. Plot
# -----------------------------

plt.figure(figsize=(12,7))
for goal_name in ["Work","Health","Creativity"]:
    vals = [next(g.clarity for g in m.goals if g.name==goal_name) for m in orbit_list]
    plt.plot(vals, label=goal_name, linewidth=2)

plt.xlabel("Generation / Step")
plt.ylabel("Goal Clarity")
plt.title(f"Nested Meta-Cognitive Simulation — Phase: {phase}")
plt.legend()
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.show()
