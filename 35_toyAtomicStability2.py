import random
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib import colors

class Particle:
    def __init__(self, type_, state, pos):
        self.type = type_          # 'p' or 'n'
        self.state = state         # integer state representing energy/spin
        self.pos = pos             # 2D position

    def interact(self, other):
        # Interaction operator: sum modulo 3 (toy model)
        self.state = (self.state + other.state) % 3 + 1
        other.state = (other.state + self.state) % 3 + 1
        # Move particles slightly toward each other
        self.pos[0] += (other.pos[0] - self.pos[0]) * 0.1
        self.pos[1] += (other.pos[1] - self.pos[1]) * 0.1
        other.pos[0] += (self.pos[0] - other.pos[0]) * 0.1
        other.pos[1] += (self.pos[1] - other.pos[1]) * 0.1

class Atom:
    def __init__(self, protons, neutrons):
        self.particles = []
        for _ in range(protons):
            self.particles.append(Particle('p', random.randint(1,3), [random.random(), random.random()]))
        for _ in range(neutrons):
            self.particles.append(Particle('n', random.randint(1,3), [random.random(), random.random()]))

    def is_stable(self):
        p_states = [p.state for p in self.particles if p.type == 'p']
        n_states = [n.state for n in self.particles if n.type == 'n']
        return sum(p_states) % 3 == 0 and sum(n_states) % 3 == 0

    def step(self):
        for p in self.particles:
            other = random.choice(self.particles)
            if p != other:
                p.interact(other)

# Visualization setup
atom = Atom(protons=3, neutrons=3)
fig, ax = plt.subplots()

# Define a color map for states 1,2,3
cmap = colors.ListedColormap(['yellow', 'orange', 'green'])
bounds = [0.5,1.5,2.5,3.5]
norm = colors.BoundaryNorm(bounds, cmap.N)

scat = ax.scatter([p.pos[0] for p in atom.particles],
                  [p.pos[1] for p in atom.particles],
                  c=[p.state for p in atom.particles],
                  cmap=cmap, norm=norm,
                  s=200, edgecolors='k')

def update(frame):
    atom.step()
    # Update positions
    scat.set_offsets([[p.pos[0], p.pos[1]] for p in atom.particles])
    # Update colors by state
    scat.set_array([p.state for p in atom.particles])
    # If stable, highlight with larger edge
    if atom.is_stable():
        scat.set_edgecolor('cyan')
        scat.set_linewidths(3)
        ax.set_title(f"Stable configuration reached at step {frame}")
    else:
        scat.set_edgecolor('k')
        scat.set_linewidths(1)
        ax.set_title(f"Step {frame}")
    return scat,

ani = animation.FuncAnimation(fig, update, frames=100, interval=300, blit=True)
ax.set_xlim(0,1)
ax.set_ylim(0,1)
plt.show()
