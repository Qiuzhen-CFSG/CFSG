module
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.SpecificGroups.SL2.SylowBorelSeparation

/-!
# Sylow subgroups invariant under their full normalizer

In binary SL₂, a nonzero subgroup of a Sylow two-subgroup normalized by its
full normalizer is the whole Sylow. Conjugate to the upper root group and
apply the diagonal square action, which is transitive on nonzero parameters.
The result includes the field of order two.

Source: DGS, *Groups and Graphs* (1985), 5.2 and the linear module step of
9.3, pp.105 and 142. The literal graph application is `NeighborSylow`.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Full-normalizer invariance leaves no proper nontrivial subgroup of a binary Sylow. -/
theorem sylow_eq_of_normalized (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F))
    (hAS : A ≤ S) (hne : A ≠ ⊥)
    (hn : normalizer (S : Set SL(2,F)) ≤ normalizer (A : Set SL(2,F))) :
    A = S := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  let c := MulAut.conj a
  have hs : (S : Subgroup SL(2,F)).map c.toMonoidHom = upperUnipotent F := by
    change ((a • S : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have he : A.map c.toMonoidHom = upperUnipotent F := by
    apply eq_upperUnipotent_of_normalized
    · exact hs ▸ map_mono hAS
    · exact fun he => hne ((map_eq_bot_iff_of_injective _ c.injective).mp he)
    · have hm := map_mono (f := c.toMonoidHom) hn
      change (normalizer ((S : Subgroup SL(2,F)) : Set SL(2,F))).map c.toMonoidHom ≤
        (normalizer (A : Set SL(2,F))).map c.toMonoidHom at hm
      rw [map_equiv_normalizer_eq (S : Subgroup SL(2,F)) c,
        map_equiv_normalizer_eq A c, hs] at hm
      exact hm
  exact (Subgroup.map_injective (f := c.toMonoidHom) c.injective) (he.trans hs.symm)
end Matrix.SpecialLinearGroup
