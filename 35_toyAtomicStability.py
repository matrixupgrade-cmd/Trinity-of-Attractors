import random
import matplotlib.pyplot as plt
import matplotlib.animation as animation

class Particle:
    def __init__(self, type_, state, pos):
        self.type = type_          # 'p' or 'n'
        self.state = state         # integer state representing energy/spin
        self.pos = pos             # 2D position
        self.color = 'red' if type_ == 'p' else 'blue'

    def interact(self, other):
        # Interaction operator: simple modular combination of states
        self.state = (self.state + other.state) % 3 + 1
        other.state = (other.state + self.state) % 3 + 1
        # Slightly move particles toward each other (simulating attraction)
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
        # Each particle randomly interacts with another particle
        for p in self.particles:
            other = random.choice(self.particles)
            if p != other:
                p.interact(other)

# Visualization setup
atom = Atom(protons=3, neutrons=3)

fig, ax = plt.subplots()
scat = ax.scatter([p.pos[0] for p in atom.particles],
                  [p.pos[1] for p in atom.particles],
                  c=[p.color for p in atom.particles],
                  s=200)

def update(frame):
    atom.step()
    scat.set_offsets([[p.pos[0], p.pos[1]] for p in atom.particles])
    return scat,

ani = animation.FuncAnimation(fig, update, frames=50, interval=300, blit=True)
ax.set_xlim(0,1)
ax.set_ylim(0,1)
ax.set_title("Protons (red) and Neutrons (blue) finding stable configuration")
plt.show()
