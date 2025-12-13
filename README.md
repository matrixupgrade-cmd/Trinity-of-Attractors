The repository starts with the axiom of the trinity.

Logic state is immutable.
Logic state is mutable but bounded.
Logic state is mutable but unbounded.

Logic has an observer effect.

000_AxiomOfTrinity_implies_AC_AD.lean
Shows that it is likely the Axiom of Trinity (AT) implies the Axiom of Choice (AC) and also implies the Axiom of Determinacy (AD).
This would mean AT is a more primordial axiom, since AC and AD conflict.

To give the reader some intuition, think of it like this: the Axiom of Choice handles immutable logic, while the Axiom of Determinacy handles mutable logic. AT allows us to pick which one works best for the problem.

From there, the Lean files start with finite coupling systems in a very general, abstract, reductionist sense. Tension is the mechanism that handles how they affect one another. This introduces the concept of a tension spider, which exists in a meta sense and self-forms from tension in coupling systems that begin fighting over which rules the local system will follow. Each tension spider sees its own rules as immutable.

00_Tension_caused_metamorph.lean

Overview:
This Lean file formalizes a fully general, substrate-independent coupling system with an Inner Tension Spider, a mechanism that monitors the system state and rewrites its own governing parameters from within. It establishes the foundations for understanding how internal tension can drive transitions between system behaviors.

00_emergent_order.lean

Overview:
This Lean 4 + mathlib file provides a canonical, fully general, substrate-independent formalization of endogenous metamorphosis in coupled systems. It introduces the Inner Tension Spider, capable of observing the system’s state and autonomously rewriting parameters. This mechanism allows the system to move between self-attractors without external forcing, producing internal attractor metamorphosis and emergent order. 



It also shows how, from this very general reductionist viewpoint of coupling systems, geometry emerges. From there it moves from finite coupling systems to a more general version with hybrid tension spiders.

From this logic setup, self-organization logic emerges in the system. It gives toy models of protein folding, slime mold simulation, and traffic simulation, where real-world observations emerge from tension and hybrid spiders. The work takes this very generic idea of coupling systems and tries to mathematically capture how tensions in coupling systems play out, allowing the math to manifest in the system rather than defining the math for the system.

Because the logic is general, it can apply to anything that can be thought of as a coupling system. What isn’t in some sort of coupling system?

Then it proves the finite-range trichotomy theorem: states in coupling systems will end in one of three states.

• Rule-set tension spiders agree — immutable logic — Solid / Crystal State
• Rule-set tension spiders partially disagree — mutable but bounded logic — Liquid State
• Rule-set tension spiders totally disagree — mutable and unbounded logic — Plasma / Gas State

In the simplest form, with no outside influence and using the Axiom of Choice, the system will end in one of these three fates. A toy model shows how this plays out.

From here, it builds on this by asking: what determines those fates? It dives into how symmetry affects those states. Symmetric cooperation between tension spiders seems not to have a Nash equilibrium. Symmetries tend to end in the solid state. The amount of symmetry in the system can push it toward the liquid state or the plasma state.

From here there are toy models for human herd immunity.

Next, it gets into computation in coupling systems and how computation is distributed between the three states.

• Solid state acts like memory
• Liquid state acts like calculation
• Plasma state acts like expanding search for an optimum

It also includes toy models showing how you can define behavior at the state level and skip most calculations. This potentially gives video game developers a way to produce realistic self-organizing behavior in runtime-friendly ways, skipping large amounts of coding and expensive runtime math. It also shows how plasma can be modeled with zero physics equations added—just by adjusting symmetries and tensions and letting the coupling system do the work. From there, it presents a toy model of an ecology self-organizing itself.

Like a moth to a flame, an attempt was made to see if creating this tension game could lead to Goldbach, and whether a proof might pop out. Maybe better luck next time. The point is to highlight how this logic set can also be used in theoretical ways. Think of it as a primordial logic that manifests in networks, producing self-organization and generating its own internal geometry.

Then it introduces a toy model showing how this logic can model the double-slit experiment. It is not claiming that photons are this or that. What it suggests is that the double slit may force photons into a state where they must calculate. To do that, the photon is forced into a liquid state. One way physicists could test this experimentally is that photons should experience time differently in the double-slit experiment.

This work is not about claims; it is about a new way to look at the world and how it may apply to old problems. Observer effects may simply be cases where you force tension spiders to reach a consensus on rules.

Then it introduces the finite metamorphosis proof: how asymmetry drives network metamorphosis. This includes a toy model of quantum soup—a toy model of a universe.

There is also a toy model of perpetual theological arguments, where the network system of philosophers either comes to a consensus and agrees on rules, has asymmetry and keeps the debate going through calculation to resolve tension, or becomes angry and storms out of the room.

Other Lean files include Newton’s toy (the familiar swinging balls), showing how it produces a processor and how mathematical calculations can be performed using it based on the geometry formed inside the coupling system. There are also files on electronic diagrams showing how to produce a chip that can perform metamorphosis based on built-up tension, and how this logic could help design processor chips.

There is a toy brain model where neurons self-form not from complicated math, but from emergent behavior driven by tensions and symmetries. There are models showing how to nest toy worlds, and Lean files exploring how worldviews that treat PDEs and topology as immutable laws could instead see them as self-formed results of being in a universe where everything affects everything else. Quantum soup may simply be the coupling system that manifests general relativity.

Think of the Axiom of Trinity as a master librarian, classifying where these things come from. It is not meant to replace PDEs or topology-based logic systems. It is more like a meta-axiom explaining why they exist in the first place—why the Axiom of Choice and the Axiom of Determinacy exist, and why they conflict.

The logic of three states in a system produces self-organization in models and explains why functions in immutable states behave as solid logic, while variables correspond to mutable, bounded logic. This may explain why mathematicians say statements like x ∈ ℝ: they bound it to be effective for calculation in the liquid form of logic. But there is also a whole wild logic that exists beyond this, whose behavior remains unknown unless it is explored.
