module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# B.5.1 on the actual component actor

After (k), the replacement has H = L₀T. The perfect offender span equals
L₀: it contains every T-conjugate of L, while its image in the two-group
H/L₀ is trivial. Hence its faithful, offender-generated action is exactly
the L₀* action. The genuine two-group quotient preserves the SQTK bounds.
An actual SL₂ equivalence supplies quasisimplicity and the full generalized
Fitting hypothesis, without assuming a module-classification conclusion.

Source: Aschbacher–Smith, B.5.1, printed p.99, applied in the proof of
15.3.49 on printed p.1144. The universal enumerated theorem remains explicit.
-/

@[expose] public section

open Subgroup CFSG CFSG.Quasithin Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : BorelInner.SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

theorem span_eq_closure (hY : Y0 ≤ localSpan L T) :
    localSpan A H = localSpan L T := by
  let J := localSpan A H
  let L0 := localSpan L T
  have hLT : H = L0 ⊔ (T : Subgroup G) := by
    rw [d.replacement]
    change L0 ⊔ (Y0 ⊔ (T : Subgroup G)) = _
    rw [← sup_assoc, sup_eq_left.mpr hY]
  have hL0H : L0 ≤ H := hLT ▸ le_sup_left
  have hTH : (T : Subgroup G) ≤ H := hLT ▸ le_sup_right
  have hJH : J ≤ H := conjugateSpanBy_le_self d.actor_le
  have hL0J : L0 ≤ J :=
    conjugateSpanBy_le d.component_le
      (hTH.trans (le_normalizer_conjugateSpanBy A H))
  have hJ : Group.IsPerfect J := by
    let _ := cComponentLayer_isPerfect (G := J)
    have hp := Group.IsPerfect.map (H := cComponentLayer J) J.subtype
    rw [d.component_generation] at hp
    exact hp
  let _ := hJ
  have hn : (L0.subgroupOf H).Normal := by
    have h := componentClosure_normal_in_replacement L Y0 T
      (le_normalizer_iff_commutator_le_left.mpr d.commutator_eq.ge) d.sylow_normalizes
    rwa [← d.replacement] at h
  let _ := hn
  have hj : L0.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hL0H, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype, ← hLT]
  have hq := isPGroup_quotient_of_sup_eq_top (L0.subgroupOf H)
    ((T : Subgroup G).subgroupOf H) T.isPGroup'.comap_subtype hj
  let _ := hq.isNilpotent
  have hr := solvableResidual_le_of_solvable_quotient (L0.subgroupOf H)
  apply le_antisymm _ hL0J
  exact (le_map_solvableResidual_of_isPerfect J H hJH).trans (by
    simpa only [map_subgroupOf_eq_of_le hL0H] using map_mono (f := H.subtype) hr)

theorem component_actor_sqtk (hY : Y0 ≤ localSpan L T) :
    IsSQTK κ (starImage H (localSpan L T)) := by
  let C := (localSpan A H).subgroupOf H
  let N := (FactorGeneration.spanStarProjection H A).ker
  have hC : IsSQTK κ C := d.sqtk.subgroup C
  have hQ : IsSQTK κ (C ⧸ N) := by
    refine ⟨?_, hC.isKGroup.quotient N⟩
    intro p hp ho
    let _ : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho N
      (FactorGeneration.spanStarProjection_kernel_twoGroup H A)).trans
      (hC.stronglyQuasithin p hp ho)
  have he := (IsSQTK.equiv (FactorGeneration.spanStarQuotientEquiv H A)).mp hQ
  rwa [span_eq_closure d hY] at he

theorem component_actor_hypotheses (hY : Y0 ≤ localSpan L T) :
    let ρ := d.action.representation.comp (starImage H (localSpan L T)).subtype
    Function.Injective ρ ∧ pCore 2 (starImage H (localSpan L T)) = ⊥ ∧
      offenderSubgroup ρ = ⊤ ∧ IsFFModule ρ := by
  obtain ⟨_, hf, hc, hg, _, hff⟩ := d.classification_hypotheses
  rw [span_eq_closure d hY] at hf hc hg hff
  exact ⟨hf, hc, hg, hff⟩

theorem selected_offender (hY : Y0 ≤ localSpan L T) :
    starImage H A ≤ starImage H (localSpan L T) ∧
      IsBestOffender
        (d.action.representation.comp (starImage H (localSpan L T)).subtype)
        ((starImage H A).subgroupOf (starImage H (localSpan L T))) ∧
      IsQuadratic
        (d.action.representation.comp (starImage H (localSpan L T)).subtype)
        ((starImage H A).subgroupOf (starImage H (localSpan L T))) := by
  have hA : starImage H A ≤ starImage H (localSpan L T) :=
    map_mono (comap_mono ((le_conjugateSpanBy A H).trans_eq (span_eq_closure d hY)))
  refine ⟨hA, d.best.subgroupOf d.action.representation hA, ?_⟩
  intro a ha b hb v
  exact d.quadratic a ha b hb v

omit d [Finite G] in
theorem sl2_quasisimple {F : Type*} [Field F] [Finite F] [CharP F 2]
    (X : Subgroup G) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hF : 2 < Nat.card F) : Theory.GroupTheory.IsQuasisimple X := by
  let _ := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let _ := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  let _ : Theory.GroupTheory.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { simple := (MulEquiv.isSimpleGroup_congr
        (Representation.SL2NaturalH1.projectiveEquiv (K := F))).mpr inferInstance }
  exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm

omit d [Finite G] in
theorem generalizedFitting_eq_top_of_quasisimple (X : Subgroup G)
    [Theory.GroupTheory.IsQuasisimple X] : Theory.GroupTheory.generalizedFitting X = ⊤ := by
  apply top_unique
  apply Theory.GroupTheory.component_le_generalizedFitting
  refine ⟨Subgroup.IsSubnormal.top, ?_⟩
  exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := X)).symm

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- Every hypothesis of B.5.1 holds on the actual component actor after (k).
The SL₂ equivalence is a rank-reduction input, not a module identification. -/
theorem component_sourceHypothesis {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hY : Y0 ≤ localSpan L T)
    (e : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hF : 2 < Nat.card F) :
    QuasisimpleSourceHypothesis
      (d.action.representation.comp (starImage H (localSpan L T)).subtype) κ ⊤ := by
  obtain ⟨hf, hc, hg, _⟩ := component_actor_hypotheses d hY
  let _ := sl2_quasisimple _ e hF
  refine ⟨Module.Finite.of_finite, hf, ?_, ?_, ?_, hc, hg⟩
  · exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  · exact (component_actor_sqtk d hY).subgroup ⊤
  · rw [generalizedFitting_eq_top_of_quasisimple]
    simp

/-- Apply the full universal, enumerated B.5.1 theorem only after proving
its hypotheses. All module alternatives remain in the output. -/
theorem component_sourceConclusion {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hB51 : QuasisimpleClassificationInput.{u,u} κ)
    (hY : Y0 ≤ localSpan L T)
    (e : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hF : 2 < Nat.card F) :
    Nonempty (QuasisimpleSourceConclusion
      (d.action.representation.comp (starImage H (localSpan L T)).subtype) ⊤) :=
  hB51 _ _ _ _ (component_sourceHypothesis d hY e hF)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
