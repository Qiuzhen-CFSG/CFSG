module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.SourceEntry
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Contracts
public import Theory.Alternating.FivePairOuterTwo
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# The original selected A₅ component in the Baumann argument

The actual module model gives a centerless A₅ quotient and a two-group
outer automorphism group. Two-perfection constructs the diagonal projection
and its literal residual supplement before block recognition. Source 13.3.2
supplies the selected component's genuine Hypothesis12.2.3. Finally equality
of the two actual Baumann subgroups forces normalizer escape using K≰M.
That equality remains the separate source obligation.

Source: Aschbacher--Smith, 13.3.14(e) and final paragraph, pp.892--893.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- The actual A₅ module marking already supplies the inner-action lift and
residual supplement. Block recognition and the chief budget are not used. -/
theorem ordinary_selected_projection_of_model
    (K : Subgroup H)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hmodel : Chapter6.Source.IsConjugationModel (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
      Chapter6.Source.a5Module) :
    ∃ hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G),
      (∃ f : sourceOne L T P →* (K.map H.subtype ⧸ pCore 2 (K.map H.subtype)),
        (MulAut.conj : (K.map H.subtype ⧸ pCore 2 (K.map H.subtype)) →*
          MulAut (K.map H.subtype ⧸ pCore 2 (K.map H.subtype))).comp f =
            (pCoreJoinAction 2 hnG).comp (inclusion le_sup_right)) ∧
      K.map H.subtype ⊔ Diagonal.centralizerResidual (K.map H.subtype)
        (sourceOne L T P) hnG = K.map H.subtype ⊔ sourceOne L T P := by
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  obtain ⟨e,_,_⟩ := hmodel
  have hc : center (K.map H.subtype ⧸ pCore 2 (K.map H.subtype)) = ⊥ := by
    apply bot_unique
    intro z hz
    apply e.injective
    have hez : e z ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨x,rfl⟩ := e.surjective a
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz x)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hez
    simpa only [map_one] using hez
  have ho : IsPGroup 2 (MulAut.Outer (K.map H.subtype ⧸ pCore 2 (K.map H.subtype))) :=
    Theory.AlternatingFive.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf).1
  exact ⟨hnG,Diagonal.exists_projection_and_residual_supplement _ _ hnG hp
    ordinary_point_residual_twoPerfect hc ho⟩

/-- The selected component satisfies the genuine earlier 12.2.3 hypotheses.
Maximality comes from 13.3.2, not from the A₅-minimality assumption on L. -/
theorem ordinary_selected_hypothesis1223
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T (K.map H.subtype) := by
  let := hq
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  have hqB : IsQuasisimple (K.map H.subtype ⧸ pCore 2 (K.map H.subtype)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  exact (Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 d.counterexample).hypothesis1223
    ⟨source1332_faithful_maximal d.counterexample.qtke T h1332 hf,
      ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf).2⟩ hqB

/-- Equality with the Baumann subgroup of O₂(KT) gives the original escape:
K normalizes that characteristic subgroup and K is not contained in M. -/
theorem ordinary_baumann_escape_of_core_identity
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hB : ChapterB.baumann ((sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2) =
      ChapterB.baumann ((K.map H.subtype ⊔ (T : Subgroup G)).pCoreIn 2)) :
    ¬ normalizer (ChapterB.baumann
      ((sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M := by
  have hout := (ordinary_component_normalizer_conclusions_of_escape d
    (Chapter14.Section08.LieTypeBranch.hypothesis1221_of_maximal_six hmax eL)
    (Chapter14.Section08.LieTypeBranch.original_six_point_normalizer_mem_Hz d hmax eL escape).2.2
    h1332 K hK hf).2.2.2.2.2
  let J := K.map H.subtype ⊔ (T : Subgroup G)
  have hn : K.map H.subtype ≤ normalizer (ChapterB.baumann (J.pCoreIn 2) : Set G) :=
    (show K.map H.subtype ≤ J from le_sup_left).trans
      ((J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))).trans
        (Stellmacher.normalizer_le_normalizer_baumann _))
  rw [hB]
  exact fun hh => hout (hn.trans hh)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
