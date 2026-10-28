module

public import Theory.Representation.BinaryOffender.Basic
public import Theory.LinearAlgebra.SubspaceRatio

/-!
# The fixed-space comparison for restriction of best offenders

For `B ≤ A`, the sum `C_V(A) + (W ∩ C_V(B))` lies in `C_V(B)` and
its intersection formula involves exactly `W ∩ C_V(A)`. The dimension
formula, together with best-offender maximality on `V`, proves maximality
after restriction to `W`. Equality forces both the original weights to
agree and the containing fixed space to equal this sum.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.1, printed pp. 118–119, equations (!)–(++).
No invariance hypothesis on `W` is needed for this dimension comparison.
-/

public section

namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Fixed spaces reverse subgroup inclusion. -/
theorem fixedSpace_antitone {A B : Subgroup G} (hBA : B ≤ A) :
    fixedSpace ρ A ≤ fixedSpace ρ B := by
  intro v hv b
  exact hv ⟨b, hBA b.property⟩

variable [FiniteDimensional (ZMod 2) V]

/-- The source comparison, retaining the dimension of the extra fixed vectors.
Subtracting the rank of a common action kernel gives equation (!!) of B.7.1. -/
theorem IsBestOffender.restriction_comparison {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hBA : B ≤ A) (W : Submodule (ZMod 2) V) :
    rank B + Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) +
        (Module.finrank (ZMod 2) (fixedSpace ρ B) -
          Module.finrank (ZMod 2)
            (fixedSpace ρ A ⊔ (W ⊓ fixedSpace ρ B) : Submodule (ZMod 2) V)) ≤
      rank A + Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) := by
  have hfix := fixedSpace_antitone ρ hBA
  have hsub : fixedSpace ρ A ⊔ (W ⊓ fixedSpace ρ B) ≤ fixedSpace ρ B :=
    sup_le hfix inf_le_right
  have hinter : fixedSpace ρ A ⊓ (W ⊓ fixedSpace ρ B) = W ⊓ fixedSpace ρ A := by
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans hfix))
  have hdim := (fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (W ⊓ fixedSpace ρ B)
  rw [hinter] at hdim
  have hle := Submodule.finrank_mono hsub
  have hweight := hA.2 B hBA
  unfold weight at hweight
  omega

/-- The weight comparison on an arbitrary subspace. -/
theorem IsBestOffender.restriction_weight_le {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hBA : B ≤ A) (W : Submodule (ZMod 2) V) :
    rank B + Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) ≤
      rank A + Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) := by
  have := hA.restriction_comparison ρ hBA W
  omega

/-- Equality in the restricted comparison gives both source equalities (+), (++). -/
theorem IsBestOffender.restriction_weight_eq_iff {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hBA : B ≤ A) (W : Submodule (ZMod 2) V) :
    rank B + Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) =
      rank A + Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) ↔
    EqualWeightLE ρ B A ∧ fixedSpace ρ A ⊔ (W ⊓ fixedSpace ρ B) = fixedSpace ρ B := by
  have hfix := fixedSpace_antitone ρ hBA
  have hsub : fixedSpace ρ A ⊔ (W ⊓ fixedSpace ρ B) ≤ fixedSpace ρ B :=
    sup_le hfix inf_le_right
  have hinter : fixedSpace ρ A ⊓ (W ⊓ fixedSpace ρ B) = W ⊓ fixedSpace ρ A := by
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans hfix))
  have hdim := (fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (W ⊓ fixedSpace ρ B)
  rw [hinter] at hdim
  have hle := Submodule.finrank_mono hsub
  have hweight := hA.2 B hBA
  unfold weight at hweight
  constructor
  · intro heq
    refine ⟨⟨hBA, ?_⟩, Submodule.eq_of_le_of_finrank_eq hsub ?_⟩
    · unfold weight
      omega
    · omega
  · rintro ⟨⟨_, heq⟩, hsum⟩
    have := congrArg (fun S : Submodule (ZMod 2) V => Module.finrank (ZMod 2) S) hsum
    unfold weight at heq
    omega

end Representation.BinaryOffender
