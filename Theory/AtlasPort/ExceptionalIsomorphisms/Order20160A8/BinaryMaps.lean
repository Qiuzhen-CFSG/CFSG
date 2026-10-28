module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightFaithful
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The two faithful actions on the binary split quadratic space

The deleted permutation module gives S₈ → O⁺₆(2), and the exterior square gives
SL₄(2) → O⁺₆(2). Both are injective. The central quotient SL₄(2) → PSL₄(2)
is an equivalence because every nonzero binary scalar is one.

Adapted from ATLAS `Comparisons/Exceptional/Order20160A8.lean` and
`LinearGroups/Orthogonal/D3ExteriorKernel.lean`. Only the binary case and the
order of the linear model needed for the comparison are retained.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8
namespace DeletedEight

/-- Transport of the faithful deleted-module action to the standard split form. -/
def orthogonalHom : Equiv.Perm (Fin 8) →* O_DPlus 3 (ZMod 2) :=
  (isometryGroupTransport splitIsometry.symm).toMonoidHom.comp permutationHom

theorem orthogonalHom_injective : Function.Injective orthogonalHom :=
  (isometryGroupTransport splitIsometry.symm).injective.comp permutationHom_injective

end DeletedEight

namespace Exterior
open ClassicalOrthogonal Bivectors

/-- In characteristic two the scalar kernel of the exterior square is trivial. -/
theorem binary_injective : Function.Injective (toOrthogonal (F := ZMod 2)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  have hg' : toOrthogonal g = 1 := hg
  have hw (w : Six (ZMod 2)) : exteriorMap g.val w = w := by
    apply coordinates.injective
    have h := congrArg (fun k : O_DPlus 3 (ZMod 2) => k.val (coordinates w)) hg'
    change coordinates (exteriorMap g.val (coordinates.symm (coordinates w))) = coordinates w at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  obtain ⟨a,ha,hga⟩ := scalar_of_exteriorMap_eq_id g.val hw
  have ha1 : a = 1 := by
    rcases Atlas.Codes.bit_cases a with h | h
    · simp [h] at ha
    · exact h
  change g = 1
  apply Subtype.ext
  simpa [ha1] using hga

end Exterior

open scoped MatrixGroups

/-- The scalar center is trivial over the binary field. -/
theorem binary_sl_center : Subgroup.center SL(4,ZMod 2) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨a,ha,hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha1 : a = 1 := by
    rcases Atlas.Codes.bit_cases a with h | h
    · simp [h] at ha
    · exact h
  change g = 1
  apply Subtype.ext
  simpa [ha1, Matrix.scalar_apply] using hga.symm

/-- The actual central quotient map is an equivalence in this binary dimension. -/
def sl4TwoEquivPSL : SL(4,ZMod 2) ≃* PSL(4,ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', binary_sl_center], QuotientGroup.mk'_surjective _⟩

private theorem psl4_card_of_two {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card PSL(4,K) = 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := K) 4
  rw [hK] at h
  norm_num [Fin.prod_univ_succ] at h
  omega

theorem psl4Two_card : Nat.card PSL(4,ZMod 2) = 20160 :=
  psl4_card_of_two (by simp [Nat.card_eq_fintype_card])

theorem sl4Two_card : Nat.card SL(4,ZMod 2) = 20160 := by
  rw [Nat.card_congr sl4TwoEquivPSL.toEquiv, psl4Two_card]

end Atlas.Order20160A8
