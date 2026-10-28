module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUp
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpFitting
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# Actual escaping components in the nonbinary pushing-up configuration

The contained generalized-Fitting branch is impossible for the full natural
quotient. C.2.11 therefore selects an escaping C-component in the same H.
For an ordinary component, C.3 places both the residual and full module in
it and proves normality. For a constrained component, C.4.4 supplies the
literal C.2.7 input, and its proved classifier gives the actual star model.
The original V, covering inclusion and all scalar centers are retained.

This is a reduction to the remaining C.3/C.4 quotient analysis, not its
exclusion. The odd-normalizer task retains that analysis and final control.
Source: Aschbacher--Smith C.2.11--13, C.3.2--4 and C.4.4, printed
pp.148--152, applied in 4.4.6, printed p.620.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual pushing-up pair with its escaping ordinary or constrained component. -/
def PushingUpComponentCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G,
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let M := H ⊓ normalizer (L : Set G)
    let R := J.pCoreIn 2
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W ∧
    (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G) ∧
    (B.subgroupOf M).Normal ∧
    (∃ e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L),
      ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) b)) ∧
    ¬ ExceptionalQuotient (B ⧸ pCore 2 B) ∧ 64 ≤ Nat.card W ∧
    (∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∧
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧ B ≤ normalizer (K.map H.subtype : Set G) ∧
      ((IsComponent H K ∧ K.Normal ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K) ∨
        (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H R M (K.map H.subtype) ∧
          ChapterC.C27Source.StarModels.Model (starImage (K.map H.subtype) R (K.map H.subtype))))

include D S
/-- The previously constructed configuration discharges the component-selection premise. -/
theorem pushingUp_component_case {A : Subgroup G} (hc : PushingUpCase L V A) :
    PushingUpComponentCase L V A := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,he,hno,_,_,_,_,_,hsize,hVW⟩ := hc
  obtain ⟨e,he⟩ := he
  have hf := pushingUp_fitting_escape D S hC hstrict e
  obtain ⟨K,hK,hq,hout,hn,hcases⟩ := hC.ordinary_or_constrained_escape hf
  refine ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,⟨e,he⟩,hno,hsize,hVW,
    K,hK,hq,hout,(le_conjugateSpanBy _ _).trans hn,?_⟩
  rcases hcases with ho | hfK
  · exact Or.inl ⟨ho,hC.ordinary_component_normal K ho,
      hC.ordinary_component_contains_original K ho,
      (hC.ordinary_module_placement K ho).1.trans inf_le_right⟩
  · exact Or.inr ⟨hfK,hC.constrained_source_input K hK hq hout hfK,
      ChapterC.C27Source.star_model_from_source (hC.constrained_source_input K hK hq hout hfK)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
