module
public import Stellmacher.SectionEight.EightThreeLocalFamily
public import Stellmacher.SectionEight.EightThreeCharacteristicObstruction
public import Stellmacher.SectionThree.ResidualCoreTransfer

/-!
# The smaller local Sylow group in the containment case of (8.2)

If the first-edge core intersection is normal in the initial stabilizer,
the next core is an actual Sylow subgroup of the join of the initial
two-residual and that next core. Every supplied Sylow with this ambient
image has the characteristic-subgroup obstruction required in (2.5).

Result (7.6) makes the next core lie outside the initial core. The residual
core transfer from (3.4) then puts the initial residual core in the next
core. The normal-supplement theorem constructs the Sylow in the smaller
group, and the characteristic-obstruction theorem uses the two generating
vertex stabilizers and the trivial ambient two-core. These arguments do
not require the centrality hypothesis of (8.3).

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), pp.37–38,
refs/latex/stellmacher-n-group.tex, the first containment case.

The local companion uses the ambient-retaining Section Eight context.
The legacy public signature is preserved by its exact graph-preserving
`toLocalContext` adapter; supplied Sylow maps and action instances are retained.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_local_setup_of_core_intersection_normal_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    NormalIn L (GAt ctx.Γ ctx.criticalPath.a) ∧
      L ⊔ S = GAt ctx.Γ ctx.criticalPath.a ∧
      ∃ T : Sylow 2 L,
        (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep ∧
        ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
          ¬ (K.map (T : Subgroup L).subtype).Normal := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let P := stabilizer Γ cp.a
  let B := q Γ cp.firstStep
  have hBS : B ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hBN : (B.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mpr
    exact (SevenSix.edge_sylow_data h Γ cp).2.1.trans
      (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  have hBnot : ¬ B ≤ twoCoreAmbient P := by
    intro hB
    apply (lemma_seven_six h Γ cp).next_residual_core.1
    have hres : twoCoreIn (e Γ cp.firstStep) ≤ B := by
      change twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.firstStep
      rw [q, Γ.twoCoreAt_def]
      rw [show e Γ cp.firstStep = twoResidualIn (stabilizer Γ cp.firstStep)
        from Γ.twoResidualAt_def cp.firstStep,
        SevenSix.residual_core_eq_inter_core]
      exact inf_le_right
    exact hres.trans (hB.trans_eq (Γ.twoCoreAt_def cp.a).symm)
  have hN : ((B ⊓ twoCoreAmbient P).subgroupOf P).Normal := by
    rw [← show q Γ cp.a = twoCoreAmbient P from Γ.twoCoreAt_def cp.a,
      inf_comm]
    exact hnormal.2
  have htransfer := SectionThree.residual_core_transfer S
    (SevenSix.sectionThreeHypotheses h) P
    ((pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1)
    B ⟨hBS, hBN⟩ (SevenSix.edge_local_data h Γ cp).1.2
    (SevenSix.edge_characteristic_data h Γ cp).1 hN hBnot
  have hcontained : twoCoreIn (EAt Γ cp.a) ≤ QAt Γ cp.firstStep := by
    rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
    exact htransfer.trans inf_le_left
  obtain ⟨hL, hLN, hgen, _⟩ := eight_three_normal_supplement_local ctx hcontained
  obtain ⟨T, hT⟩ := hL.2.1
  exact ⟨hLN, hgen, T, hT, eight_three_characteristic_obstruction_local ctx _ T hT hgen⟩


public theorem eight_two_local_setup_of_core_intersection_normal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    NormalIn L (GAt ctx.Γ ctx.criticalPath.a) ∧
      L ⊔ S = GAt ctx.Γ ctx.criticalPath.a ∧
      ∃ T : Sylow 2 L,
        (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep ∧
        ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
          ¬ (K.map (T : Subgroup L).subtype).Normal := by
  exact eight_two_local_setup_of_core_intersection_normal_local ctx.toLocalContext hnormal

end Stellmacher.SectionEight
