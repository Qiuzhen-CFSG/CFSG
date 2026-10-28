module

public import Stellmacher.SectionEight.GeneratedEightThreeLocalKernels
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSymmetry
public import Stellmacher.BaumannMap

/-!
# Ambient-backed residual-core noncontainment

The local core-collapse and action-comparison kernels give Baumann containment
in the generated graph. Injective Baumann and omega-center transport, together
with the surjective intrinsic core map, contradict the genuine ambient (6.1).
Hypothesis Two remains on the original group in either edge orientation.
Source: Stellmacher (8.3), printed p.38.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem mapped_two_core_le
    {G H : Type u} [Group G] [Group H]
    (embedding : G →* H) (P : Subgroup G) (R : Subgroup H)
    (hmap : P.map embedding = R) :
    (twoCoreIn P).map embedding ≤ twoCoreIn R := by
  let projection : P →* R := (embedding.comp P.subtype).codRestrict R
    (fun element => hmap ▸ Subgroup.mem_map_of_mem embedding element.property)
  have hsurjective : Function.Surjective projection := by
    intro element
    obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp (hmap.ge element.property)
    exact ⟨⟨preimage, hpreimage⟩, Subtype.ext heq⟩
  change ((pCore 2 P).map P.subtype).map embedding ≤ (pCore 2 R).map R.subtype
  rw [Subgroup.map_map]
  change (pCore 2 P).map (R.subtype.comp projection) ≤ _
  rw [← Subgroup.map_map]
  exact Subgroup.map_mono (le_sSup
    ⟨pCore_normal.map projection hsurjective, pCore_isPGroup.map projection⟩)

public theorem generated_eight_three_baumann_not_le_next
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2) :
    ¬ baumannIn (S.subgroupOf (P1 ⊔ P2)) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let J := P1 ⊔ P2
  let T := S.subgroupOf J
  have hSJ : S ≤ J := ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left
  have hGa : ⁅stabilizer Γ cp.a, omegaOneCenter T⁆ ≠ ⊥ := by
    intro hc
    have hC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    have hΩP : omegaOneCenter T ≤ stabilizer Γ cp.a :=
      (Subgroup.map_subtype_le _).trans (SevenSix.edge_sylow_data h Γ cp).1.1
    have hn : NormalIn (omegaOneCenter T) (stabilizer Γ cp.a) :=
      ⟨hΩP, (Subgroup.normal_subgroupOf_iff_le_normalizer hΩP).mpr
        (hC.trans (Subgroup.centralizer_le_normalizer _))⟩
    have hZ := z_eq_omega_sylow_of_normal Γ cp.a
      (SevenSix.edge_sylow_data h Γ cp).1 hn
    apply ctx.commutator_ne
    change ⁅z Γ cp.a, z Γ cp.a'⁆ = ⊥
    rw [hZ, Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (lemma_seven_four h Γ cp).reverse_containment.1.trans hC
  have homega : (omegaOneCenter T).map J.subtype = omegaOneCenter S := by
    change (omegaOneCenterAmbient T).map J.subtype = omegaOneCenterAmbient S
    rw [← omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hSJ]
  have hGaAmbient : ⁅(stabilizer Γ cp.a).map J.subtype, omegaOneCenter S⁆ ≠ ⊥ := by
    intro hzero
    apply hGa
    apply (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    rw [Subgroup.map_commutator, homega, hzero]
  have hBmap : (baumannIn T).map J.subtype = baumannIn S := by
    rw [show (baumannIn T).map J.subtype = baumannIn (T.map J.subtype) from
      baumann_map_injective J.subtype J.subtype_injective T,
      Subgroup.map_subgroupOf_eq_of_le hSJ]
  intro hbad
  have hbound : baumannIn S ≤
      twoCoreIn ((stabilizer Γ cp.firstStep).map J.subtype) := by
    rw [← hBmap]
    apply (Subgroup.map_mono hbad).trans
    change (q Γ cp.firstStep).map J.subtype ≤ _
    rw [q, Γ.twoCoreAt_def]
    exact mapped_two_core_le J.subtype _ _ rfl
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.2, Subgroup.map_subgroupOf_eq_of_le le_sup_right] at hbound
    exact lemma_six_one S0 S P1 P2 ctx.hypothesisTwo hbound
  · rw [hedge.1, Subgroup.map_subgroupOf_eq_of_le le_sup_right] at hGaAmbient
    rw [hedge.2, Subgroup.map_subgroupOf_eq_of_le le_sup_left] at hbound
    exact lemma_six_one S0 S P2 P1
      (ctx.hypothesisTwo.swap_of_commutator_ne_bot S0 S P1 P2 hGaAmbient) hbound

/-- Stellmacher (8.3) for the actual graph on the generated subgroup. -/
public theorem generated_lemma_eight_three
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hcontained
  obtain ⟨hcomm, hZaT⟩ := eight_three_core_bound_data_local ctx.toLocalContext hcontained
  have hcore := eight_three_core_eq_center_local ctx.toLocalContext hcenter hcomm
  exact generated_eight_three_baumann_not_le_next ctx
    (eight_three_action_comparison_local ctx.toLocalContext hcore (hcore.le.trans hZaT))

end Stellmacher.SectionEight
