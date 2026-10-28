module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Group.Pi.Basic

/-!
# The concrete factor witness for solvable binary FF-modules

This is the conclusion data for B.1.8(1)–(2), not an existence theorem or a
hypothesis replacing solvability. The factorization proof must construct it
from the finite solvable group, trivial two-core and faithful FF-module
hypotheses. Conditional results about such data may be proved independently.

The product equivalence agrees with the actual subgroup inclusions on every
coordinate. The linear equivalence agrees with the actual commutator-subspace
inclusions. Thus these are internal decompositions. Each support is identified
equivariantly with the two-dimensional natural module for SL₂(2), the faithful
matrix model of L₂(2). No abstract group-family label is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.8,
printed p. 70 (PDF p. 81).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB

open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual internal group and natural-module factors. An inhabitant must be
constructed; the declarations of this module assert no existence result. -/
structure SolvableFFFactors (ρ : Representation (ZMod 2) G V) where
  count : ℕ
  count_pos : 0 < count
  factor : Fin count → Subgroup G
  groupProduct : ((i : Fin count) → factor i) ≃* offenderSubgroup ρ
  groupProduct_single : ∀ (i : Fin count) (g : factor i),
    (groupProduct (Pi.mulSingle i g) : G) = (g : G)
  moduleSum : ((i : Fin count) → subspaceCommutator ρ ⊤ (factor i)) ≃ₗ[ZMod 2]
    subspaceCommutator ρ ⊤ (offenderSubgroup ρ)
  moduleSum_single : ∀ (i : Fin count) (v : subspaceCommutator ρ ⊤ (factor i)),
    (moduleSum (Pi.single i v) : V) = (v : V)
  factorModel : ∀ i, factor i ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  naturalEquiv : ∀ i, subspaceCommutator ρ ⊤ (factor i) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)
  naturalEquiv_action : ∀ (i : Fin count) (g : factor i)
      (v : subspaceCommutator ρ ⊤ (factor i)),
    ρ (g : G) (v : V) =
      ((naturalEquiv i).symm
        (Representation.specialLinearNatural 2 (factorModel i g) (naturalEquiv i v)) : V)

end CFSG.Quasithin.ChapterB
