module

public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleCovering
public import Theory.GroupTheory.Amalgam.UniquenessSystem.Recognition

/-!
# Triangle homotopy and uniqueness-system recognition

This module re-exports edge-path homotopy by triangles and backtracks, the
common-neighbor contraction criterion, homotopy-invariant fiber transport, the
isomorphism theorem for triangle coverings, and recognition from equivalent
faithful uniqueness systems with a simple triangle model.

The distinguished triangle orbit and triangle contraction give the actual
normal-cycle base. The universal-completion theorem then constructs a group
isomorphism extending the compatible stabilizer maps, in either comparison
direction. Only the simple model needs a base.

Sources: Aschbacher–Smith §F.5, Lemmas F.5.7–F.5.8 and the concluding
recognition argument; Aschbacher, *Sporadic Groups* (1994), §§34–37 and
Exercise 13.1(b).
-/
