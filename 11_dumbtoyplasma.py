import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from IPython.display import HTML

def metamorphosis_theater():
    size = 50
    N = 160
    
    # Temperature field: one hot beacon, one cold sink
    temp = np.zeros((size, size))
    temp[size//4, size//4] = 1.2
    temp[3*size//4, 3*size//4] = -0.8
    
    # particles: [x, y, energy, state, asymmetry]
    p = np.zeros((N, 5))
    p[:, :2] = np.random.uniform(5, size-5, (N, 2))
    p[:, 2] = 0.4                                     # energy
    p[:, 3] = 0                                       # 0=plasma, 1=liquid, 2=solid
    p[:, 4] = np.random.triangular(0, 0.3, 1.0, N)     # asymmetry (left-skewed = mostly selfish)

    fig, ax = plt.subplots(figsize=(7.5, 7.5))
    ax.set_facecolor('black')
    
    def step():
        nonlocal temp
        
        # Diffuse temperature
        temp = 0.94 * temp + 0.015 * (
            np.roll(temp, 1, 0) + np.roll(temp, -1, 0) +
            np.roll(temp, 1, 1) + np.roll(temp, -1, 1)
        )
        
        for i in range(N):
            x, y = p[i, :2].astype(int)
            x = np.clip(x, 1, size-2)
            y = np.clip(y, 1, size-2)
            T = temp[y, x]
            
            # absorb local heat
            p[i, 2] += (T - p[i, 2]) * 0.06
            p[i, 2] = np.clip(p[i, 2], 0.01, 1.5)
            E = p[i, 2]
            asym = p[i, 4]

            if E < 0.28:                     # COLD → SOLID (green crystals)
                p[i, 3] = 2
                p[i, :2] += np.random.randn(2) * 0.08 * (1 + asym)

            elif E > 0.72:                    # HOT → PLASMA (red fireflies)
                p[i, 3] = 0
                # flee the center + cluster with nearby plasma
                away = p[i, :2] - [size/2, size/2]
                away = away / (np.linalg.norm(away) + 1e-6)
                nearby = p[(np.linalg.norm(p[:, :2] - p[i, :2], axis=1) < 4.5) & (p[:, 3] == 0)]
                attract = (nearby[:, :2].mean(axis=0) - p[i, :2]) if len(nearby) else 0
                p[i, :2] += away * (0.6 + asym) + attract * 0.4 + np.random.randn(2) * 0.3

            else:                              # WARM → LIQUID (blue rivers)
                p[i, 3] = 1
                # 4-neighbor gradient walk, corrupted by asymmetry
                nb = [(0,1),(0,-1),(1,0),(-1,0)]
                grads = [temp[y+dy, x+dx] for dx,dy in nb]
                best = nb[np.argmax(grads)]
                noise = np.random.randn(2) if np.random.rand() < asym else 0
                p[i, :2] += np.array(best) * 0.4 + noise * 0.3

            p[i, :2] = np.clip(p[i, :2], 2, size-3)

    def update(frame):
        for _ in range(8): step()
        
        ax.clear()
        ax.imshow(temp, cmap='coolwarm', alpha=0.4, vmin=-0.9, vmax=1.1, origin='lower')
        
        for state, color, name in zip([0,1,2], ['#ff0044', '#0099ff', '#00ff99'], ['Plasma', 'Liquid', 'Solid']):
            mask = p[:, 3] == state
            if mask.any():
                ax.scatter(p[mask,0], p[mask,1], c=color, s=45, edgecolor='white', linewidth=0.4, label=name, alpha=0.9)
        
        ax.set_title(f"Metamorphosis Theorem Live • Frame {frame}", color='white', fontsize=14)
        ax.legend(loc='upper right', facecolor='#111')
        ax.axis('off')
        ax.set_facecolor('black')

    anim = FuncAnimation(fig, update, frames=500, interval=90, repeat=True)
    plt.close()
    return HTML(anim.to_jshtml())

# Watch the inevitable
metamorphosis_theater()
