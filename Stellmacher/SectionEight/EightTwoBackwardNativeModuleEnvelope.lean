module
public import Stellmacher.SectionEight.EightTwoBackwardHallOrbitReduction
public import Stellmacher.SectionEight.EightThreeCoreBound

/-!
# The native module and the neighboring core's central involutions

Under initial-stabilizer normality of the first-edge core intersection,
the smaller group's native module is the join of the initial vertex module
and the omega center of the neighboring core. The residual-core transfer
allows the prescribed-module commutator bound from (8.3). The omega center
centralizes the initial vertex module and hence lies in the initial core.
Its residual commutators therefore lie in the initial vertex module, so
their join is normalized by the smaller group. The normal-closure definition
gives the upper bound; the normal-supplement comparison gives the lower bound.

Consequently the native-module upper comparison is equivalent to containment
of the neighboring core's omega center in the neighbor module. This isolates
the central-involution inclusion needed in Stellmacher (8.2), printed pp.37–38,
`refs/latex/stellmacher-n-group.tex`. Neither the native upper comparison nor
the classification or critical-distance conclusion is assumed here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem residual_core_le_neighbor
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
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
  rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
  exact htransfer.trans inf_le_left

public theorem eight_two_backward_native_module_eq_vertex_sup_omega
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a))
    (T : Sylow 2 ↥(EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep))
    (hT : (T : Subgroup ↥(EAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep)).map
        (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype =
          QAt ctx.Γ ctx.criticalPath.firstStep) :
    (SectionTwo.vSubgroup T).map
      (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype =
        ZAt ctx.Γ ctx.criticalPath.a ⊔
          omegaOneCenterAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let P := GAt Γ cp.a
  let E := EAt Γ cp.a
  let B := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.a
  let A := omegaOneCenterAmbient B
  let L := E ⊔ B
  let Y := Z ⊔ A
  have hdata := eight_three_core_bound_data ctx (residual_core_le_neighbor ctx hnormal)
  have hZB : Z ≤ B := hdata.2
  have hBS : B ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hBP : B ≤ P := hBS.trans (SevenSix.edge_sylow_data h Γ cp).1.1
  have hEP : E ≤ P := by
    rw [show E = twoResidualIn P from Γ.twoResidualAt_def cp.a]
    exact SevenSix.twoResidualIn_le P
  have hAC : A ≤ Subgroup.centralizer (B : Set H) := by
    intro element helement
    exact (Subgroup.mem_centralizer_iff).mpr
      (fun other hother => ((mem_omegaOneCenterAmbient_iff B element).mp helement).2.2
        other hother)
  have hAB : A ≤ B := by
    intro element helement
    exact ((mem_omegaOneCenterAmbient_iff B element).mp helement).1
  have hAQ : A ≤ QAt Γ cp.a := by
    change A ≤ q Γ cp.a
    rw [← (lemma_seven_four h Γ cp).edge_centralizer]
    exact le_inf (hAB.trans hBS) (hAC.trans (Subgroup.centralizer_le hZB))
  have hPZ : P ≤ Subgroup.normalizer (Z : Set H) := stabilizer_le_normalizer_z Γ cp.a
  have hEZ : E ≤ Subgroup.normalizer (Z : Set H) := hEP.trans hPZ
  have hEA : ⁅E, A⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hAQ le_rfl).trans hdata.1
  have hEY : E ≤ Subgroup.normalizer (Y : Set H) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    have hmap : Y.map (MulAut.conj actor).toMonoidHom ≤ Y := by
      rw [show Y = Z ⊔ A from rfl, Subgroup.map_sup]
      apply sup_le
      · rintro value ⟨generator, hgenerator, rfl⟩
        exact Subgroup.mem_sup_left
          ((Subgroup.le_normalizer_iff.mp hEZ) actor hactor generator hgenerator)
      · rintro value ⟨generator, hgenerator, rfl⟩
        have hcomm := hEA (Subgroup.commutator_mem_commutator hactor hgenerator)
        have hmul := Y.mul_mem (Subgroup.mem_sup_left hcomm)
          (Subgroup.mem_sup_right hgenerator)
        change actor * generator * actor⁻¹ ∈ Y
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hmul
    exact hmap (Subgroup.mem_map_of_mem _ helement)
  have hBY : B ≤ Subgroup.normalizer (Y : Set H) := by
    apply (le_inf (hBP.trans hPZ) ?_).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Z A)
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hAC helement)) actor hactor
    simpa only [← mul_assoc, hcomm, mul_inv_cancel_right] using helement
  have hLY : L ≤ Subgroup.normalizer (Y : Set H) := sup_le hEY hBY
  let _ : (Y.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLY
  have hOmega : (omegaOneCenterAmbient (T : Subgroup L)).map L.subtype = A := by
    rw [← omegaOneCenterAmbient_map_injective L.subtype L.subtype_injective, hT]
  change (SectionTwo.vSubgroup T).map L.subtype = Y
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    change SectionTwo.vSubgroup T ≤ Y.subgroupOf L
    apply Subgroup.normalClosure_le_normal
    change omegaOneCenterAmbient (T : Subgroup L) ≤ Y.comap L.subtype
    apply Subgroup.map_le_iff_le_comap.mp
    exact hOmega.le.trans le_sup_right
  · apply sup_le (eight_two_backward_vertex_le_native_module ctx hnormal T hT)
    change A ≤ (SectionTwo.vSubgroup T).map L.subtype
    rw [← hOmega]
    exact Subgroup.map_mono Subgroup.le_normalClosure

public theorem eight_two_backward_native_le_neighbor_iff_omega_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a))
    (T : Sylow 2 ↥(EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep))
    (hT : (T : Subgroup ↥(EAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep)).map
        (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype =
          QAt ctx.Γ ctx.criticalPath.firstStep) :
    (SectionTwo.vSubgroup T).map
      (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype ≤
        VAt ctx.Γ ctx.criticalPath.firstStep ↔
      omegaOneCenterAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) ≤
        VAt ctx.Γ ctx.criticalPath.firstStep := by
  rw [eight_two_backward_native_module_eq_vertex_sup_omega ctx hnormal T hT, sup_le_iff]
  exact and_iff_right
    (lemma_seven_four (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated)
      ctx.Γ ctx.criticalPath).first_containment.1

end Stellmacher.SectionEight
