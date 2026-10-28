module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# Collapse of the initial core in Stellmacher (8.3)

In the actual Section Eight critical-pair context, suppose the first-step
vertex center is central in its stabilizer. If the commutator of the
initial vertex core with its residual lies in its vertex center module,
then that core equals the vertex center module.

The alternatives in (7.3) identify the central first-step module with
the omega center of its stabilizer: the other alternative would make
a local Sylow subgroup equal its two-core. The neighboring-center
conclusion of (7.3) makes the initial stabilizer center-free.
Its vertex center module lies in the omega center of its two-core.
The odd-prime residual of the ordinary core quotient in (3.3)(a)
supplies the odd image required by the general center-free core-collapse
theorem. Apply that theorem inside the literal initial stabilizer and
map its containment back to the ambient group.

Source: Stellmacher (8.3), Journal of Algebra 190 (1997), p38,
refs/latex/stellmacher-n-group.tex. The caller supplies the commutator
bound from its separate local-family argument; no additional core
containment or graph property is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The initial two-core equals its vertex center module under the (8.3) commutator bound. -/
public theorem eight_three_core_eq_center
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcomm : ⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Z := z Γ cp.a
  let Q := pCore 2 P
  let E := twoResidualAmbient (⊤ : Subgroup P)
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hb : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have h73 := lemma_seven_three h Γ
  have hPcenter : Subgroup.center P = ⊥ := by
    let T : Sylow 2 (↥(Pb ⊓ P)) := default
    have hdata := edge_sectionThree_data h Γ ha T
    have halt := h73.centralizer_alternative cp.firstStep cp.a ha T
    have hZeq : z Γ cp.firstStep = omegaOneCenter Pb := by
      rcases halt with heq | heq
      · have hWPb : sylowTwoAmbient (Pb ⊓ P) T ≤ Pb :=
          (Subgroup.map_subtype_le _).trans inf_le_left
        have hWC : sylowTwoAmbient (Pb ⊓ P) T ≤ Subgroup.centralizer (z Γ cp.firstStep : Set H) :=
          hWPb.trans (Subgroup.le_centralizer_iff.mp
            (hcenter.trans (SevenSix.centerAmbient_le_centralizer Pb)))
        rw [inf_eq_left.mpr hWC] at heq
        have hcore : q Γ cp.firstStep = twoCoreAmbient Pb := Γ.twoCoreAt_def cp.firstStep
        exact (hdata.2.1.1.2.2.2 (heq.trans hcore)).elim
      · exact heq.1
    exact h73.center_neighbor_trivial cp.firstStep cp.a ha hZeq
  have hZomega : Z ≤ omegaOneCenter (q Γ cp.a) := h73.center_core cp.a cp.firstStep hb
  have hZQ : Z ≤ q Γ cp.a := hZomega.trans (Subgroup.map_subtype_le _)
  have hQmap : Q.map P.subtype = q Γ cp.a := by
    change twoCoreIn P = q Γ cp.a
    exact (Γ.twoCoreAt_def cp.a).symm
  have hQP : q Γ cp.a ≤ P := by rw [← hQmap]; exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := hZQ.trans hQP
  let V := Z.subgroupOf P
  have hVmap : V.map P.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZP
  have hEmap : E.map P.subtype = e Γ cp.a := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) P.subtype P
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hm.trans (Γ.twoResidualAt_def cp.a).symm
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  have hSP := (SevenSix.edge_sylow_data h Γ cp).1
  obtain ⟨hSPle, T, hT⟩ := hSP
  have hcover : E ⊔ (T : Subgroup P) = ⊤ := twoResidualAmbient_top_sup_sylow T
  have hPset := (pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1
  have hsolv := (SevenSix.edge_local_data h Γ cp).1.2
  obtain ⟨B, hB, hSB, huniq⟩ := hPset.2
  have hBnative : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B := by
    refine ⟨hB, ?_, ?_⟩
    · intro s hs
      obtain ⟨b, hb, he⟩ := hSB hs
      exact P.subtype_injective he ▸ hb
    · intro B' hB' hS'
      apply huniq B' hB'
      intro s hs
      exact ⟨⟨s, hSPle hs⟩, hS' hs, rfl⟩
  obtain ⟨p, hp, hpodd, hres⟩ :=
    (SectionThree.lemma_three_three S (SevenSix.sectionThreeHypotheses h) P hPset B B.normalCore hBnative
      ⟨B.normalCore_le, inferInstance, fun N hN hNB => by
        let _ := hN
        exact Subgroup.normal_le_normalCore.mpr hNB⟩ hsolv).part_a
  let f := QuotientGroup.mk' Q
  have hodd : Odd (Nat.card (E.map f)) := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) f ⊤
      (Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective Q))]
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hres.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hVcentral : V ≤ Subgroup.centralizer (Q : Set P) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    have hvc := (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a)) (hZomega hv)
    have hrq : (r : H) ∈ q Γ cp.a := hQmap ▸ Subgroup.mem_map_of_mem P.subtype hr
    exact Subgroup.mem_centralizer_iff.mp
      ((SevenSix.centerAmbient_le_centralizer (q Γ cp.a)) hvc) r hrq
  have hcommN : ⁅Q, E⁆ ≤ V := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hQmap, hEmap, hVmap]
    exact hcomm
  have hQV := Subgroup.le_of_centerfree_odd_image_commutator_le T E Q V hcover
    (pCore_isPGroup (p := 2) (G := P)) hodd hPcenter hVcentral hcommN
  apply le_antisymm ?_ hZQ
  rw [← hQmap, ← hVmap]
  exact Subgroup.map_mono hQV

end Stellmacher.SectionEight

