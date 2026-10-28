module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Basic
public import Theory.GroupTheory.SolvableMutualCommutator
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Solvability of endpoints in an original automorphism extension

Each endpoint is the product of its inner part with the full common overlap.
The inner part is normal in that endpoint, and conjugation has central kernel.
Thus a solvable overlap makes endpoint solvability equivalent to solvability
of the corresponding base parabolic. If the two base parabolics have matching
solvability, so do the extended endpoints: a solvable endpoint already makes
the overlap solvable. No assumption on the outer group or triviality of the
base center is needed.

This is the elementary extension argument used to filter the original Lie
rows in Aschbacher–Smith F.1.12 and 5.2.2, printed pp.263–264,647.
The SourceExtension and its full intersection are unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
variable {X : Type*} [Group X] {P₀ P₁ : Subgroup X}
  (E : SourceExtension P₀ P₁)

private theorem endpoint_solvable_iff (P : Subgroup X) (U : Subgroup (MulAut X))
    (hU : U ≤ E.carrier) (hCU : E.middle ≤ U)
    (hUN : U ⊓ inner X = P.map MulAut.conj) (hC : Group.IsSolvable E.middle) :
    Group.IsSolvable U ↔ Group.IsSolvable P := by
  let : Group.IsSolvable (MulAut.conj : X →* MulAut X).ker := by
    rw [DoubleCoverCentralizer.conj_kernel]
    exact Group.isSolvable_of_comm fun a b =>
      Subtype.ext ((mem_center_iff.mp a.property b).symm)
  have hPU : P.map MulAut.conj ≤ U := hUN ▸ inf_le_left
  constructor
  · intro hs
    let := hs
    apply (Group.isSolvable_map_iff_of_solvable_ker MulAut.conj P).mp
    exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hPU)
  · intro hs
    let := hs
    let := hC
    let : Group.IsSolvable (P.map MulAut.conj) :=
      (Group.isSolvable_map_iff_of_solvable_ker MulAut.conj P).mpr hs
    have hn : E.middle ≤ normalizer (P.map MulAut.conj : Set (MulAut X)) := by
      rw [← hUN]
      exact (le_inf (hCU.trans U.le_normalizer) le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf
    have he : P.map MulAut.conj ⊔ E.middle = U := by
      apply le_antisymm (sup_le hPU hCU)
      intro a ha
      obtain ⟨b,d,hd,he⟩ := E.factor a (hU ha)
      have hbU : MulAut.conj b ∈ U := by
        have hh := U.mul_mem ha (U.inv_mem (hCU hd))
        rwa [he,mul_inv_cancel_right] at hh
      have hbP : MulAut.conj b ∈ P.map MulAut.conj := hUN ▸ ⟨hbU,⟨b,rfl⟩⟩
      rw [he]
      exact (P.map MulAut.conj ⊔ E.middle).mul_mem
        ((show P.map MulAut.conj ≤ _ from le_sup_left) hbP)
        ((show E.middle ≤ _ from le_sup_right) hd)
    exact he ▸ Group.isSolvable_sup_of_normalizes _ _ hn

/-- Solvability of the left endpoint is detected on its literal inner base. -/
theorem left_solvable_iff (hC : Group.IsSolvable E.middle) :
    Group.IsSolvable E.left ↔ Group.IsSolvable P₀ :=
  endpoint_solvable_iff E P₀ E.left E.left_le inf_le_left E.left_inner hC

/-- Solvability of the right endpoint is detected on its literal inner base. -/
theorem right_solvable_iff (hC : Group.IsSolvable E.middle) :
    Group.IsSolvable E.right ↔ Group.IsSolvable P₁ :=
  endpoint_solvable_iff E P₁ E.right E.right_le inf_le_right E.right_inner hC

/-- A restored pair cannot acquire mixed solvability when the base pair has
matching solvability. The solvable endpoint itself makes the full overlap solvable. -/
theorem endpoints_solvable_iff
    (hs : Group.IsSolvable P₀ ↔ Group.IsSolvable P₁) :
    Group.IsSolvable E.left ↔ Group.IsSolvable E.right := by
  constructor
  · intro hl
    let := hl
    have hm : Group.IsSolvable E.middle :=
      Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (show E.middle ≤ E.left from inf_le_left))
    exact (E.right_solvable_iff hm).mpr (hs.mp ((E.left_solvable_iff hm).mp hl))
  · intro hr
    let := hr
    have hm : Group.IsSolvable E.middle :=
      Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (show E.middle ≤ E.right from inf_le_right))
    exact (E.left_solvable_iff hm).mpr (hs.mpr ((E.right_solvable_iff hm).mp hr))

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
