module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalSelection
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalFiveAction
import all CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalFiveAction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalClassification
public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.CentralQuotientFive

/-!+# One original chosen summand suffices for the central-line contradiction

The escaping H-star residual moves the reduced local omega-span. Homogeneous
selection inside that same span supplies an original chosen module. The
chosen-action clause of 12.2.2 identifies its faithful central quotient as
the natural A₅ module. Projectivity lifts this marking to the chosen module
itself, giving an actual five-point core inside the unchanged local span.

The faithful action of J/C_J(V_J), Borel placement, and evenness then give
the original 12.6.23 actor contradiction. No decomposition of the whole
moved span into one or two modules is needed. The same-G,T structural and
module theorems and the literal earlier A₇ exclusion are the only earlier
source inputs; no rank-one generic or small exit is assumed.

The internal import of LocalFiveAction reuses its conjugation-model summand
transport while keeping that helper outside the public interface.

Source: Aschbacher–Smith, 12.6.23, printed pp.829–830, and 12.3.2, p.807,
using homogeneous selection A.1.40–42 and projectivity I.1.5–6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine.LocalContradiction Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V J : Subgroup G}

private theorem chosen_five_model_in_local_span
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hZ : centralizer (Z T : Set G) ≤ M L)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (hK : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual J))
    (e₀ : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5))
    (each : ∀ (W : Subgroup G) (E : ChosenModule T (localResidual J) W),
      letI := E.actionCentralizer_normal
      Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5))) :
    ∃ W : Subgroup G, W ≤ localSpan T J ∧
      Chapter6.Source.IsConjugationModel (localResidual J) W Chapter6.Source.a5Module := by
  let K := localResidual J
  let X := K ⊔ (T : Subgroup G)
  let R := (localSpan T J).subgroupOf X
  have hX : X = J :=
    Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual_supplement hJ.1.1.2
  have hUX : localSpan T J ≤ X := hX.symm ▸ localSpan_le hJ.1.1.2
  have hr : IsPReduced 2 R := by
    change IsPReduced 2 ((localSpan T J).subgroupOf X)
    rw [hX]
    exact Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_reduced H.source hJ
  have hm : ⁅R,K.subgroupOf X⁆ ≠ ⊥ := by
    intro he
    have he' := congrArg (map X.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUX,
      map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left),Subgroup.map_bot] at he'
    have hc := commutator_eq_bot_iff_le_centralizer.mp he'
    exact Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual_not_centralizes_seed
      H.chosen.sylow_normalizes_component hZ hJ
      ((le_centralizer_iff.mp hc).trans (centralizer_le (le_conjugateSpanBy _ _)))
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.maximal_faithful.1.1
  obtain ⟨W,⟨E⟩,hW⟩ := exists_chosen_le_reduced_witness (B := K)
    (hJ.1.1.2.trans
      (Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual_normalized J)) R hr hm
  have hWU : W ≤ localSpan T J := by
    change W ≤ ((localSpan T J).subgroupOf X).map X.subtype at hW
    simpa only [map_subgroupOf_eq_of_le hUX] using hW
  let := E.actionCentralizer_normal
  obtain ⟨a⟩ := each W E
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (K ⧸ pCore 2 K) := e₀.isSimpleGroup
  let e := (E.coreToFaithfulEquiv hs).trans a.groupEquiv
  refine ⟨W,hWU,E.a5_model_of_central_quotient e a.linearEquiv ?_⟩
  intro k v
  exact a.intertwines (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf K) k) v

private theorem fixed_hstar_chosen_five_contradiction
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (hK : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual J))
    (e₀ : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5))
    (each : ∀ (W : Subgroup G) (E : ChosenModule T (localResidual J) W),
      letI := E.actionCentralizer_normal
      Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5))) : False := by
  let := H.local_span_elementary hJ
  have hZ := H.fixed_sylow_seed_centralizer_le D hTV hz
  obtain ⟨W,hWU,e,b,hb⟩ := chosen_five_model_in_local_span H hZ hJ hK e₀ each
  let E := coreEquivNatural (Fin 5) (by decide)
  obtain ⟨j,hj,he⟩ := LocalFiveAction.summand_from_conjugation_model hWU
    Chapter6.Source.a5Module e b hb E.toLinearMap E.injective
    (fun a v => coreEquivNatural_equivariant (Fin 5) (by decide) a.val v)
  obtain ⟨α,hα,hmark⟩ := LocalFiveAction.exists_local_five_action H hZ hJ e
  have hmark' (k : localResidual J) : α (localActorMap (T := T)
      (map_subtype_le (pResidual 2 J)) k) ∈ alternatingGroup (Fin 5) :=
    (hmark k) ▸ (e (QuotientGroup.mk' _ k)).property
  obtain ⟨g,hAT,hAB,hne⟩ := H.fixed_local_actor_exists D hTV hTI hz hJ
    (H.fixed_hstar_borel_le_join D hJ e)
  have hAJ := hAT.trans hJ.1.1.2
  have hAK := hAB.trans (LocalFiveAction.local_borel_core_le_residual_join_core H hJ e)
  have heven := LocalFiveAction.local_even_of_le_residual_join_core H hJ α hmark' hAJ hAK
  apply H.fixed_marked_local_actor_contradiction D hTV hTI hz hAJ hne α hα heven j hj
  intro a v
  obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ⟨α (localActorMap (T := T) hAJ a),heven a⟩
  have hq : localActorMap (T := T) (map_subtype_le (pResidual 2 J)) k =
      localActorMap (T := T) hAJ a :=
    hα ((hmark k).trans (congrArg Subtype.val hk))
  have hc := congrArg (QuotientGroup.kerLift (localConjugation T J)) hq
  change localConjugation T J (inclusion (map_subtype_le (pResidual 2 J)) k) =
    localConjugation T J (inclusion hAJ a) at hc
  have hk' : (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)).val =
      α (localActorMap (T := T) hAJ a) := congrArg Subtype.val hk
  rw [←hk',he]
  apply Additive.toMul.injective
  exact congrArg (fun f : MulAut (localSpan T J) => f (j v).toMul) hc

/-- The original fixed space vanishes using one chosen local summand. The
earlier inputs are restricted to this same G,T, with no rank-one exits. -/
theorem SourceHypothesis.fixed_space_eq_bot_of_chosen_five_source
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7))) :
    ZV L V = ⊥ := by
  by_contra hz
  have hs := (structural L H.source).2.2 V H.chosen
  obtain ⟨J,hJ⟩ := H.fixed_exists_hstar D hz
  have hZ := H.fixed_sylow_seed_centralizer_le D hs.1 hz
  have hn := H.fixed_hstar_not_solvable D hs.1 hs.2.2.1 hz hJ
  obtain ⟨hK,⟨e⟩,each⟩ :=
    Section04.SLThreeCommutatorSource.ConjugateExistence.local_residual_maximal_five_of_seven_excluded
      H.source structural modules hZ hJ hn seven
  exact fixed_hstar_chosen_five_contradiction H D hs.1 hs.2.2.1 hz hJ hK e each

end CFSG.Quasithin.Chapter12.Section06
