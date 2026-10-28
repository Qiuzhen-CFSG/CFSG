module

public import Theory.Representation.HermitianTensorThree.Marked
public import Theory.Representation.HermitianTensorThree.Root
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The concrete Hermitian tensor in H.4.2

This module connects the genuine descended SL₃ tensor and its two marked
involutions to the binary module parameters. The field involution has moved
dimension 3n, and the root involution has moved dimension 4n. An overgroup
containing the former therefore has minimum involution displacement at most
3n. The lower bound, full pointwise centralizers, parabolic geometry,
rank/torus restrictions, generated hyperplane and n=1 quotient actions of
H.4.4–6 are separate obligations; they are not hypotheses hidden in a module
record here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.380–382.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor
open Representation.HermitianTensorThree Representation.BinaryOffender
variable (n : ℕ) [NeZero n]

theorem root_fixedCodim :
    fixedCodim (binaryAction n) (Subgroup.zpowers (root n)) = 4 * n := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact finrank_binaryRootMoved n


/-- The same root codimension in any source overgroup containing its actual image. -/
theorem overgroup_root_fixedCodim (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hr : binaryActionHom n (root n) ∈ M) :
    fixedCodim (overgroupAction n M)
      (Subgroup.zpowers ⟨binaryActionHom n (root n), hr⟩) = 4 * n := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact finrank_binaryRootMoved n

/-- In any literal overgroup containing the field involution, that involution
attains the source codimension 3n. This does not assume all overgroups contain it. -/
theorem field_fixedCodim (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (ht : fieldSwapBinary n ∈ M) :
    fixedCodim (overgroupAction n M) (Subgroup.zpowers ⟨fieldSwapBinary n, ht⟩) = 3 * n := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact finrank_binaryFieldMoved n

theorem orderOf_fieldSwapBinary : orderOf (fieldSwapBinary n) = 2 := by
  apply orderOf_eq_prime
  · apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    rfl
  · intro h
    have he : fieldSwap n = 1 := by
      apply LinearEquiv.ext
      intro X
      exact congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e X) h
    exact fieldSwap_ne_one n he

/-- The field involution is an actual attaining actor, not an assumed minimum. -/
theorem moduleM_le_three_mul (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (ht : fieldSwapBinary n ∈ M) : ChapterE.moduleM (overgroupAction n M) ≤ 3 * n := by
  have horder : orderOf (⟨fieldSwapBinary n, ht⟩ : M) = 2 := by
    rw [← orderOf_injective M.subtype Subtype.val_injective]
    exact orderOf_fieldSwapBinary n
  exact (ChapterE.moduleM_le_involution (overgroupAction n M) horder).trans_eq
    (field_fixedCodim n M ht)

/-- The inner root always supplies an involution in the actual cover action. -/
theorem cover_moduleM_le_four_mul : ChapterE.moduleM (binaryAction n) ≤ 4 * n :=
  (ChapterE.moduleM_le_involution (binaryAction n) (orderOf_root n)).trans_eq (root_fixedCodim n)

end CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor
