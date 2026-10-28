module

public import Theory.GroupTheory.SimpleSectionSolvableLayers
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.ZMod.Basic

/-!
# Normal-layer interface for proper subgroups of PSL₄(3)

The targets needed for the proper-section argument are GL₃(3), A₆, and
PSp₄(3). The last carrier is the central quotient of the actual symplectic
matrix group. `HasSmallLayers` specifies normal layers and a faithful map
to one of these groups; it makes no assertion about their simple sections.

The missing intrinsic overgroup theorem must construct these layers for an
overgroup of each proper subgroup of PSL₄(3). Merely naming the three targets
does not prove that theorem. This module publishes its mathematical interface
so that the overgroup proof and the target-section calculations can proceed
independently.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three

public abbrev PSL := ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)

public abbrev PSp := symplecticGroup (Fin 2) (ZMod 3) ⧸
  Subgroup.center (symplecticGroup (Fin 2) (ZMod 3))

/-- The required normal layers, with actual embeddings of their quotients. -/
@[expose] public def HasSmallLayers (H : Type*) [Group H] : Prop :=
  Theory.GroupTheory.SolvableLayersEmbedding H
      (GeneralLinearGroup (Fin 3) (ZMod 3)) ∨
    Theory.GroupTheory.SolvableLayersEmbedding H (alternatingGroup (Fin 6)) ∨
    Theory.GroupTheory.SolvableLayersEmbedding H PSp

end Matrix.PSL4Three
