# Toy Model: Drift and Observer Bias Visualization

from itertools import product
import matplotlib.pyplot as plt

# --- 1. Define state space ---
N = 5  # number of states
K_max = 10  # maximum sample length
high_state = 0  # drift direction (unique high element)

states = list(range(N))

# Assign numerical values to states (Φ)
Phi = {0: 10, 1: 5, 2: 5, 3: 5, 4: 5}

# Global average μ
mu = sum(Phi.values()) / N
print(f"Global average μ = {mu}\n")

# --- 2. Compute fraction of biased samples for each K ---
fractions = []

for K in range(1, K_max + 1):
    all_sequences = list(product(states, repeat=K))
    biased_count = sum(1 for seq in all_sequences if high_state in seq)
    fraction_biased = biased_count / len(all_sequences)
    fractions.append(fraction_biased)
    print(f"K={K}, fraction biased = {fraction_biased:.3f}")

# --- 3. Plot ---
plt.figure(figsize=(8,5))
plt.plot(range(1, K_max+1), fractions, marker='o', linestyle='-', color='orange')
plt.xlabel("Sample size K")
plt.ylabel("Fraction of biased samples")
plt.title("Observer Bias Emergence in Finite Cyclic Network")
plt.ylim(0,1.05)
plt.grid(True)
plt.show()
