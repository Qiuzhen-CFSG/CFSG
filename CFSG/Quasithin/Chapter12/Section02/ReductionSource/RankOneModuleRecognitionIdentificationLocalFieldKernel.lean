module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFieldComponents
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldClassification

/-!
# The actual field-plane action kernel and component lifts in Chapter 12

The chosen module supplies the uniqueness hypothesis for the kernel proof.
For the literal noncommuting conjugate configuration, the faithful action
has exactly the original centralizer's two-core as kernel. Its components
lift with their intrinsic quotients and actual action maps preserved, so
the checked B.5 restriction applies directly to the action components.

The final cubic exclusions and graph escape remain to be proved.
Source: Aschbacher--Smith, 6.2.4(4) and 6.2.7, pp.680,683, applied to
12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Source 6.2.4(4) on the original Chapter12 field plane. -/
theorem source_local_one_sided_action_kernel
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let U := B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)
    (LocalFieldQuotientAction.action B U).ker = pCore 2 (centralizer (U : Set G)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact LocalFieldQuotientAction.action_kernel_eq_core h611 hnatural hE hfactor
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    hfield hUc hout

/-- The component restriction now applies to each actual faithful-action
component in the B.5 small-moved catalogue; the lift premise is discharged. -/
theorem source_local_one_sided_action_component_models
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let U := B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)
    ∀ J : Subgroup (LocalFieldQuotientAction.action B U).range,
      IsComponent _ J → SmallMoved.ActorList J →
      Nonempty (J ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (J ≃* PSL(3,ZMod 2)) ∨
        Nonempty (J ≃* SL(3,BinaryField.four.Carrier)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  dsimp only
  intro J hJ hm
  obtain ⟨K,hK,_,e,_⟩ := LocalFieldQuotientAction.action_component_lift h611 hnatural hE hfactor
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    hfield hUc hout J hJ
  have hmK : SmallMoved.ActorList (K ⧸ pCore 2 K) := hm.of_mulEquiv e
  rcases local_field_component_small_actor h611 hnat hfield hUc K hK hmK with hf | hf | hf
  · exact Or.inl (hf.map (fun f => e.symm.trans f))
  · exact Or.inr (Or.inl (hf.map (fun f => e.symm.trans f)))
  · exact Or.inr (Or.inr (hf.map (fun f => e.symm.trans f)))


/-- Apply B.5 and the lifted-component restriction together in the disjoint
commutator-plane branch of 6.2.7, on the actual conjugate four-group image. -/
theorem source_local_one_sided_disjoint_component_models
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (centralizer (U : Set G))).map
      (LocalFieldQuotientAction.action B U).rangeRestrict
    U ⊓ ⁅A,B⁆ = ⊥ → ∀ J : Subgroup (LocalFieldQuotientAction.action B U).range,
      IsComponent _ J → ⁅J,I⁆ = J →
      Nonempty (J ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (J ≃* PSL(3,ZMod 2)) ∨
        Nonempty (J ≃* SL(3,BinaryField.four.Carrier)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  dsimp only
  intro hdis J hJ hJI
  obtain ⟨ρ,c,_,_,_,_,_,_,_,_,hmodels,_⟩ :=
    LocalFieldQuotientAction.exists_classified_offender_action h611 hnatural hE hfactor g hBA hnon
  exact source_local_one_sided_action_component_models D h h611 hnatural g hBA hnon J hJ
    ((hmodels hdis).2.2.2 J hJ hJI).2

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
