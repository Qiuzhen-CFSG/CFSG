module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Recognition

/-!
# Ambient recognition on the original large-parabolic markings

The original centralizer and fusion arguments already prove generation of G
and its exact native order, including elimination of the possible cubic
endpoint extension. Small-completion recognition now identifies G with the
actual binary triality carrier. Both endpoint squares use the literal
inclusion of the original generated subgroup into G.

The earlier marked realization remains an explicit source input; this module
does not construct it. Source: Aschbacher--Smith F.4.31, 14.2.18--19,
pp.290--295,987 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- Ambient recognition preserves both maps of the supplied original marked
amalgam, including the full common Borel. -/
theorem source_marked_ambient_recognition (r : MarkedTriality T M Mc H) :
    let c := markedCompletion r
    ∃ f : G ≃* Carrier P,
      (∀ x, f (c.left x : G)=ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left x) ∧
      (∀ x, f (c.right x : G)=ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right x) := by
  let c := markedCompletion r
  let J := H ⊔ secondParabolic T M Mc H
  have hgen := source_generated_eq_top hG hempty hM hu hmany hcard e hH r
  have hord := source_card_eq_triality hG hempty hM hu hmany hcard e hH r
  have hbound : Nat.card J≤Nat.card (Carrier P) :=
    (Nat.card_le_card_of_injective J.subtype J.subtype_injective).trans_eq hord
  obtain ⟨f,hfL,hfR⟩ :=
    ChapterF.SourceCompletion.TrialityTwo.Completion.exists_mulEquiv_of_order_bound c hbound
  let j : J ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  refine ⟨j.symm.trans f,?_,?_⟩
  · intro x
    change f (j.symm (j (c.left x)))=_
    rw [j.symm_apply_apply,hfL]
  · intro x
    change f (j.symm (j (c.right x)))=_
    rw [j.symm_apply_apply,hfR]

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
