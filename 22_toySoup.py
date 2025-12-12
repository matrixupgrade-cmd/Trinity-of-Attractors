import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from scipy.spatial import cKDTree

# PARAMETERS
N = 250
SIZE = 60
dt = 0.1
asymmetry_gain = 0.08
liquid_arrow_strength = 0.12
solid_contraction_strength = 0.08
plasma_jitter = 0.25
tension_to_dilation = 0.08
asym_to_dilation = 0.12
PLASMA, LIQUID, SOLID = 0, 1, 2
T_low, T_solid, T_high = 0.6, 0.25, 1.2
A_low, A_high, A_melt = 0.08, 0.25, 0.18
cluster_radius = 3.0
global_bias_strength = 0.002  # For galaxy formation
rot_bias_strength = 0.05      # Asymmetry-driven rotation for accretion disks

# INITIAL CONDITIONS
pos = np.random.uniform(0, SIZE, (N, 2))
phase = np.random.choice([PLASMA, LIQUID, SOLID], N, p=[0.7, 0.25, 0.05])
time_rate = np.ones(N)
base_asym = np.array([[0.0,1.0,1.0],[1.0,0.0,1.0],[1.0,1.0,0.0]]) * asymmetry_gain

# FUNCTIONS
def neighbors(i):
    d = np.linalg.norm(pos - pos[i], axis=1)
    mask = (d < 5.0) & (d > 0)
    return mask, d

def compute_tension_asym():
    tension, asym = np.zeros(N), np.zeros(N)
    for i in range(N):
        mask, d = neighbors(i)
        if np.sum(mask) == 0: continue
        tension[i] = np.sum(1.0 / d[mask])
        ph, neighbor_phases = phase[i], phase[mask]
        asym_vals = [base_asym[ph, ph2] for ph2 in neighbor_phases]
        asym[i] = np.mean(asym_vals)
    return tension, asym

def phase_transition(tension, asym):
    global phase
    for i in range(N):
        ph, t, a = phase[i], tension[i], asym[i]
        if ph == PLASMA:
            if t < T_low and a < A_low: phase[i] = LIQUID
        elif ph == LIQUID:
            if t < T_solid: phase[i] = SOLID
            elif t > T_high or a > A_high: phase[i] = PLASMA
        elif ph == SOLID:
            if a > A_melt: phase[i] = LIQUID

def liquid_arrow(i):
    mask, _ = neighbors(i)
    if np.sum(mask) == 0: return np.zeros(2)
    center = np.mean(pos[mask], axis=0)
    v = center - pos[i]
    n = np.linalg.norm(v)
    return liquid_arrow_strength * v / (n + 1e-9)

def solid_contraction(i):
    mask, _ = neighbors(i)
    if np.sum(mask) == 0: return np.zeros(2)
    center = np.mean(pos[mask], axis=0)
    return solid_contraction_strength * (center - pos[i])

def update_time_dilation(tension, asym):
    global time_rate
    time_rate[:] = 1.0 / (1.0 + tension_to_dilation * tension + asym_to_dilation * asym)

def update_positions(tension, asym):
    global pos
    new_pos = pos.copy()
    solid_com = np.mean(pos[phase == SOLID], axis=0) if np.any(phase == SOLID) else np.mean(pos, axis=0)
    for i in range(N):
        v_asym = asym[i] * (np.random.randn(2) * 0.1)
        if phase[i] == PLASMA: v_phase = plasma_jitter * np.random.randn(2)
        elif phase[i] == LIQUID: v_phase = liquid_arrow(i)
        else: v_phase = solid_contraction(i)
        vec = solid_com - pos[i]
        norm = np.linalg.norm(vec) + 1e-9
        v_global = global_bias_strength * vec / norm  # Galaxy bias toward solid COM
        perp = np.array([-vec[1], vec[0]]) / norm
        v_rot = asym[i] * rot_bias_strength * perp    # Asymmetry rotation for disks
        v = v_phase + v_asym + v_global + v_rot
        new_pos[i] += v * dt * time_rate[i]
    pos[:] = np.clip(new_pos, 0, SIZE)

def compute_colors():
    colors = np.zeros((N, 3))
    tree = cKDTree(pos)
    for i in range(N):
        idx = tree.query_ball_point(pos[i], cluster_radius)
        same_phase = np.sum(phase[idx] == phase[i])
        coherence = same_phase / max(len(idx), 1)
        if phase[i] == PLASMA: base = np.array([0.2, 0.2, 1.0])
        elif phase[i] == LIQUID: base = np.array([0.6, 0.0, 0.6])
        else: base = np.array([1.0, 0.2, 0.2])
        colors[i] = np.clip(base * (0.5 + 0.5 * coherence), 0, 1)
    return colors

# ANIMATION
fig, ax = plt.subplots(figsize=(6, 6))
colors = compute_colors()
sc = ax.scatter(pos[:, 0], pos[:, 1], c=colors)

def animate(frame):
    tension, asym = compute_tension_asym()
    phase_transition(tension, asym)
    update_time_dilation(tension, asym)
    update_positions(tension, asym)
    colors = compute_colors()
    sc.set_offsets(pos)
    sc.set_color(colors)
    ax.set_title(f"Quantum Soup Simulator — Frame {frame}")
    return sc,

ani = FuncAnimation(fig, animate, frames=800, interval=40)
plt.close()
ani
