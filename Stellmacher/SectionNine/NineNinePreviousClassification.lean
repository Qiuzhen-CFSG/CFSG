module
public import Stellmacher.SectionNine.NineNinePreterminalTransvection
public import Stellmacher.SectionNine.NineFiveSuppliedPath
public import Stellmacher.SectionFiveToSeven.ReversedExtendedPath

/-!
# The order-thirty-two wreath-product case in (9.9)

The actual extracted transvection acts on the preceding module with its
commutator inside the original first-step module. Extend the reversed path
from its center vertex through the preterminal vertex and back to the initial
vertex, ending at the preceding neighbor. Critical minimality and the actor's
core escape make these endpoints a genuine critical pair. The centers commute
because the new center lies in the initial core and the preceding center lies
in the initial center.

The shared reversed-path construction retains both endpoint offsets.
Apply (9.5) on that entire supplied path, retaining the original first-step
vertex at its backward offset. The order-eight alternative is impossible:
both neighboring modules contain the initial center of order four, while the
preceding module's intersection has index at least four. Thus the preceding
module has order thirty-two, its exact core quotient is SL₂(2) ≀ C₂, and the
intersection has order eight.

This is assertion (3) of Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. The actual ambient (9.8) bound and the
transported (9.7) index bound remain explicit inputs.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_previous_wreath_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    Nat.card (VAt ctx.Γ previous) = 2^5 ∧
      QuotientIsModel (GAt ctx.Γ previous) (QAt ctx.Γ previous) SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2^3 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨neighbor,actor,hneighbor,hactor,hactorNot,_,hquot,hcontain⟩ :=
    nine_nine_preterminal_transvection bound ctx hb hcore previous hprevious hne hlarge
  obtain ⟨path,hstart,hend,hfirst,hback,hadj⟩ :=
    reversed_extended_path Γ cp hb previous neighbor hprevious hneighbor
  have hnot : ¬ ZAt Γ neighbor ≤ QAt Γ previous := fun hle => hactorNot (hle hactor)
  have hdistance : Γ.distance neighbor previous = cp.length := by
    have hupper := Γ.distance_le_of_path cp.length path hadj
    rw [hstart,hend] at hupper
    have hlower : cp.length ≤ Γ.distance neighbor previous := by
      by_contra hlt
      exact hnot (critical_minimality Γ cp (by omega))
    omega
  have hcritical : IsCriticalPair Γ neighbor previous := by
    refine ⟨?_,hnot⟩
    rw [hdistance,← cp.endpoint_distance]
    exact cp.critical.1
  have hZQa : ZAt Γ neighbor ≤ QAt Γ cp.a := by
    have hpath := path_distance_le Γ cp 0 (cp.length - 2) (by omega) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) preterminal ≤ cp.length - 2 - 0 at hpath
    rw [cp.path_start, Nat.sub_zero] at hpath
    have hstep := nine_eight_adjacent_distance_le Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)) (target := cp.a)
    change Γ.distance neighbor cp.a ≤ Γ.distance preterminal cp.a+1 at hstep
    rw [Γ.distance_symm preterminal cp.a] at hstep
    apply critical_minimality Γ cp
    change 3 < cp.length at hb
    omega
  have hcoreC : QAt Γ cp.a ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hZprevZa : ZAt Γ previous ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 previous hprevious).2
  have hcomm : ⁅ZAt Γ neighbor,ZAt Γ previous⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZQa.trans (hcoreC.trans (Subgroup.centralizer_le hZprevZa)))
  have hactorV : actor ∈ VAt Γ (path ⟨1,by omega⟩) := by
    rw [hfirst]
    apply (show ZAt Γ neighbor ≤ VAt Γ preterminal from ?_) hactor
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  have hresult := nine_five_of_supplied_critical_path ctx hshort neighbor previous hcritical
    hcomm path hstart hend hadj actor ⟨hactorV,hactorNot⟩ hquot (by
      rw [hback]
      exact hcontain)
  rw [hback] at hresult
  rcases hresult with ⟨hsmall,_⟩ | hresult
  · have hZaI : ZAt Γ cp.a ≤ VAt Γ previous ⊓ VAt Γ cp.firstStep := le_inf
      (nine_seven_neighbor_center_le_module Γ
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hprevious)))
      (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    have hcard := Subgroup.card_le_of_le hZaI
    have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
    change Nat.card (ZAt ctx.Γ ctx.criticalPath.a) ≤ Nat.card
      (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) at hcard
    change Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 at hfour
    norm_num at hsmall
    omega
  · exact hresult

end Stellmacher.SectionNine
