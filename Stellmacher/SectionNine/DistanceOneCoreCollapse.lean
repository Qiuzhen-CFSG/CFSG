module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# Initial core collapse from a residual commutator bound

For a Section Nine local context, the bound [Q_a,E_a] ≤ Z_a implies
Q_a = Z_a. Neither distance one nor the faithful-center conclusion is
needed for this final implication.

The commuting critical pair gives a center-free initial stabilizer by
(7.5). Its vertex center centralizes its two-core by (7.3). The ordinary
core quotient, rather than the faithful-center quotient, has odd residual
image by (3.3)(a). Restrict these data to the actual initial stabilizer,
apply the center-free odd-image core theorem, and map back to the graph
group. All hypotheses belong to the local Section Seven configuration;
no ambient Hypothesis Two is transported to the generated group.

This proves the final implication preceding Stellmacher (9.1)(11),
Journal of Algebra 190 (1997), printed p.48, from the scan
refs/files/stellmacher-n-group.pdf. The separate noncentral chief-factor
exclusion must supply the explicit residual commutator bound.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem distance_one_core_eq_center_of_residual_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hcomm : ⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Z := z Γ cp.a
  let Q := pCore 2 P
  let E := twoResidualAmbient (⊤ : Subgroup P)
  have hneighbor : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hPcenter : Subgroup.center P = ⊥ :=
    (lemma_seven_five h Γ cp ctx.commutator_eq).start_center_trivial
  have hZomega : Z ≤ omegaOneCenter (q Γ cp.a) :=
    (lemma_seven_three h Γ).center_core cp.a cp.firstStep hneighbor
  have hZQ : Z ≤ q Γ cp.a := hZomega.trans (Subgroup.map_subtype_le _)
  have hQmap : Q.map P.subtype = q Γ cp.a := by
    change twoCoreIn P = q Γ cp.a
    exact (Γ.twoCoreAt_def cp.a).symm
  have hQP : q Γ cp.a ≤ P := by
    rw [← hQmap]
    exact Subgroup.map_subtype_le _
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
  obtain ⟨hTP, sylow, hsylow⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hcover : E ⊔ (sylow : Subgroup P) = ⊤ := twoResidualAmbient_top_sup_sylow sylow
  have hPset := (pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1
  have hsolv := (SevenSix.edge_local_data h Γ cp).1.2
  obtain ⟨maximal, hmaximal, hTmaximal, hunique⟩ := hPset.2
  have hnative : IsCoatom maximal ∧ T.subgroupOf P ≤ maximal ∧
      ∀ other : Subgroup P, IsCoatom other → T.subgroupOf P ≤ other → other = maximal := by
    refine ⟨hmaximal, ?_, ?_⟩
    · intro element helement
      obtain ⟨preimage, hpreimage, heq⟩ := hTmaximal helement
      exact P.subtype_injective heq ▸ hpreimage
    · intro other hother hTother
      apply hunique other hother
      intro element helement
      exact ⟨⟨element, hTP helement⟩, hTother helement, rfl⟩
  obtain ⟨prime, hprime, hoddprime, hresidual⟩ :=
    (SectionThree.lemma_three_three T (SevenSix.sectionThreeHypotheses h) P hPset
      maximal maximal.normalCore hnative
      ⟨maximal.normalCore_le, inferInstance, fun normal hnormal hle => by
        let _ := hnormal
        exact Subgroup.normal_le_normalCore.mpr hle⟩ hsolv).part_a
  let projection := QuotientGroup.mk' Q
  have hodd : Odd (Nat.card (E.map projection)) := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) projection ⊤
      (Subgroup.map_top_of_surjective projection (QuotientGroup.mk'_surjective Q))]
    let _ : Fact prime.Prime := ⟨hprime⟩
    obtain ⟨exponent, hcard⟩ := hresidual.exists_card_eq
    rw [hcard]
    exact hoddprime.pow
  have hVcentral : V ≤ Subgroup.centralizer (Q : Set P) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro coreElement hcoreElement
    apply Subtype.ext
    have hcentral := (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a))
      (hZomega helement)
    have hcore : (coreElement : G) ∈ q Γ cp.a :=
      hQmap ▸ Subgroup.mem_map_of_mem P.subtype hcoreElement
    exact Subgroup.mem_centralizer_iff.mp
      ((SevenSix.centerAmbient_le_centralizer (q Γ cp.a)) hcentral) coreElement hcore
  have hcommNative : ⁅Q, E⁆ ≤ V := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hQmap, hEmap, hVmap]
    exact hcomm
  have hQV := Subgroup.le_of_centerfree_odd_image_commutator_le sylow E Q V hcover
    (pCore_isPGroup (p := 2) (G := P)) hodd hPcenter hVcentral hcommNative
  apply le_antisymm ?_ hZQ
  rw [← hQmap, ← hVmap]
  exact Subgroup.map_mono hQV

end Stellmacher.SectionNine
