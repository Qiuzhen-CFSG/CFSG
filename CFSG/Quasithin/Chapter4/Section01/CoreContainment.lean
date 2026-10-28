module
public import CFSG.Quasithin.Chapter4.Section01.MaximalCounterexample
public import CFSG.Quasithin.Chapter4.Section01.ResidualCover
import Mathlib.Tactic
/-!
# The actual core in the section centralizer

Eta covers the two-perfect normal subgroup X modulo O2(X). Applying the
A.4.3 signalizer comparison to X intersect I and O2(I) puts this same core
in C_M(X/O2(X)). This proves4.1.4(1) without requiring maximality in mu.
The literal Hypothesis4.1.1 consumer preserves all source subgroups.
Source: Aschbacher--Smith, printed pp.606--607.
-/

public section
namespace CFSG.Quasithin.Chapter4
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The actual core containment of4.1.4(1) requires only eta, not mu-star. -/
theorem core_le_sectionCentralizer_of_eta {M X Mminus I : Subgroup G}
    (hXM : X ≤ M) (hN : (X.subgroupOf M).Normal) (hX : IsPPerfect 2 X)
    (hminus : Mminus ≤ M) (hI : I ∈ eta M X Mminus) :
    I.pCoreIn 2 ≤ sectionCentralizerIn M X := by
  have hIM := hI.1.trans hminus
  have hjoin : X = (X ⊓ I) ⊔ X.pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨i,hi,q,hq,he⟩ := hI.2.2.1 hx
      have hiX : i ∈ X := by
        have hqX := pCoreIn_le 2 X hq
        have he' : i = x * q⁻¹ := by rw [← he]; simp
        rw [he']; exact X.mul_mem hx (X.inv_mem hqX)
      rw [← he]
      exact mul_mem_sup ⟨hiX,hi⟩ hq
    · exact sup_le inf_le_left (pCoreIn_le 2 X)
  rw [sectionCentralizerIn_eq_twoSectionCentralizer]
  apply ChapterA.Section04.signalizer_le_section_of_core_join X (X ⊓ I) M
    (I.pCoreIn 2) hXM hN.isSubnormal hX
  · simpa only [← inf_assoc, inf_idem] using hjoin
  · apply (ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr
    exact ⟨(pCoreIn_le 2 I).trans hIM,isPGroup_pCoreIn 2 I,
      inf_le_right.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))⟩

/-- Source4.1.4(1), for the same original core R=O2(I). -/
theorem lemma_4_1_4_1 {K : GroupClass} {T : Sylow 2 G}
    {M X Mminus I : Subgroup G} (hyp : Hypothesis411 K T M X)
    (hminus : Mminus ∈ sigma M X) (hI : I ∈ muStar M X Mminus) :
    I.pCoreIn 2 ≤ sectionCentralizerIn M X :=
  core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal hyp.plus_perfect
    hminus.1 hI.1.1
end CFSG.Quasithin.Chapter4
