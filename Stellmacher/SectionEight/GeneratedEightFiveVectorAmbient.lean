module

public import Stellmacher.SectionEight.GeneratedEightFiveVectorGraph
public import Stellmacher.SectionEight.GeneratedEightFiveCentralizerSetup
public import Stellmacher.SectionFiveToSeven.SixFourWitnessCriticalNontrivial
public import Stellmacher.SectionFiveToSeven.Result6_4

/-!
# Ambient (6.4) for a transported generated-graph witness

The graph-side module and stabilizers map into the genuine ambient Hypothesis
Two data. An ambient faithful witness with the same mapped offender fixed
subgroup gives canonical critical nontriviality and full-preimage fixedness.
The mapped generating centralizer therefore permits the exact ambient (6.4)
to put the vector in the Sylow omega-center. Injectivity brings it back to
the next graph center.

The witness transport premise is explicit here; the final generated criterion
must construct it, not assume it. No Hypothesis Two is imposed on the join,
and neither normality nor (8.3) is used. Source: Stellmacher (6.4), (8.4),
and (8.5), printed pp.39–40 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem generated_eight_four_vector_criterion_of_ambient_witness
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set (P1 ⊔ P2 : Subgroup H)))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (ambientWitness : QuotientModuleWitness
      ((GAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype)
      ((GAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype ⊓
        Subgroup.centralizer
          ((ZAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype : Set H))
      ((ZAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype))
    (hfixed : ambientWitness.oneJFixedPoints S =
      (w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2))).map (P1 ⊔ P2).subtype)
    (v : (P1 ⊔ P2 : Subgroup H))
    (hv : v ∈ w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2)))
    (hgen : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set (P1 ⊔ P2 : Subgroup H))) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep) :
    v ∈ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let embedding := (P1 ⊔ P2).subtype
  have hinjective : Function.Injective embedding := (P1 ⊔ P2).subtype_injective
  let T := S.subgroupOf (P1 ⊔ P2)
  have hmapS : T.map embedding = S := Subgroup.map_subgroupOf_eq_of_le
    (ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)
  obtain ⟨_, hGa, hNext, _⟩ := generated_central_first_step_setup ctx hcenter
  let V := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  have hV : V = sectionSixV S P1 := generated_eight_four_center_eq_sectionSixV ctx hGa
  have homega : (ZAt ctx.Γ ctx.criticalPath.firstStep).map embedding = omegaOneCenter S := by
    rw [generated_central_first_step_center ctx hcenter]
    exact (omegaOneCenterAmbient_map_injective embedding hinjective T).symm.trans
      (congrArg omegaOneCenter hmapS)
  have hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥ := by
    rw [← hNext, ← homega, ← Subgroup.map_commutator]
    have hlocal : ⁅GAt ctx.Γ ctx.criticalPath.firstStep,
        ZAt ctx.Γ ctx.criticalPath.firstStep⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      exact Subgroup.le_centralizer_iff.mpr
        (hcenter.trans (centerAmbient_le_centralizer _))
    rw [hlocal, Subgroup.map_bot]
  let R := GAt ctx.Γ ctx.criticalPath.firstStep ⊓
    Subgroup.centralizer ({v} : Set (P1 ⊔ P2 : Subgroup H))
  have hRT : R ⊔ T = GAt ctx.Γ ctx.criticalPath.firstStep :=
    eight_four_edge_generation_local ctx.toLocalContext R hgen
  have hRTH : R.map embedding ⊔ S = P2 := by
    rw [← hmapS, ← Subgroup.map_sup, hRT]
    exact hNext
  have hRcentral : R.map embedding ≤
      Subgroup.centralizer (Subgroup.zpowers (embedding v) : Set H) := by
    rintro actor ⟨preimage, hpreimage, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro member ⟨power, rfl⟩
    apply (show Commute (embedding v) (embedding preimage) from ?_).zpow_left power
    have hcommute := (Subgroup.mem_centralizer_singleton_iff.mp hpreimage.2).symm
    change embedding v * embedding preimage = embedding preimage * embedding v
    simpa only [map_mul] using congrArg embedding hcommute
  have hgenerate : sectionSixCentralizerJoin P2 S (embedding v) = P2 := by
    apply le_antisymm
    · exact sup_le inf_le_left ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    · exact hRTH.ge.trans (sup_le_sup_right
        (le_inf (le_sup_left.trans_eq hRTH) hRcentral) S)
  have hcanon : ∀ witness : QuotientModuleWitness P1
      (P1 ⊓ Subgroup.centralizer (V : Set H)) V,
      witness.oneJFixedPoints S ≠ V →
      embedding v ∈ witness.oneJFixedPoints S → embedding v ∈ omegaOneCenter S := by
    intro witness hproper hvfixed
    have hJ := sectionSix_barredCritical_ne_bot_of_witness_fixed_ne
      ctx.hypothesisTwo V hV witness hproper
    rw [sectionSix_witness_fixed_eq ctx.hypothesisTwo V hV witness] at hvfixed
    by_contra hvnot
    exact lemma_six_four S0 S P1 P2 ctx.hypothesisTwo V hV hcomm hJ
      (embedding v) hvfixed.1 hvfixed.2 hvnot hgenerate.symm
  have htransport := Eq.mpr (congrArg (fun P : Subgroup H =>
    ∀ witness : QuotientModuleWitness P (P ⊓ Subgroup.centralizer (V : Set H)) V,
      witness.oneJFixedPoints S ≠ V →
      embedding v ∈ witness.oneJFixedPoints S → embedding v ∈ omegaOneCenter S) hGa) hcanon
  have hproper : ambientWitness.oneJFixedPoints S ≠ V := by
    intro heq
    apply eight_four_fixed_proper_local ctx.toLocalContext w
    apply Subgroup.map_injective hinjective
    exact hfixed.symm.trans heq
  have hvfixed : embedding v ∈ ambientWitness.oneJFixedPoints S :=
    hfixed.ge (Subgroup.mem_map_of_mem embedding hv)
  have hvomega := htransport ambientWitness hproper hvfixed
  obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp (homega.ge hvomega)
  exact hinjective heq ▸ hpreimage

end Stellmacher.SectionEight
