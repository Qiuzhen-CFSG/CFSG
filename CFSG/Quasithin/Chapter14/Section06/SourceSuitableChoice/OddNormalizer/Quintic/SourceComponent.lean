module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.Contained
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.OuterComparison.Kernel

/-!
# Source extraction without the ordinary-centralizer identification

This separately named contract is constructed from the raw second-normalizer
extraction. It retains the actual component, commutators, relative normality
at five-rank one, the conjugate-span intersection and the C.2.4 alternative.
The older conditional EscapingComponent interface remains separate.

The consumer theorems apply this component to C.2.7 and the checked contained
natural-row contradiction, and retain the literal quotient action in both
rank cases. No ordinary-centralizer residual identity is required or asserted.

This is conditional on the intermediate NormalizerGeometry, whose construction
remains in qt-e-14615-quintic-exclusion, along with natural-row selection and
the remaining outer comparison before p = 3 is assembled. The authorized
earlier 14.6.12--14 inputs remain with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The proved extraction data, with relative normality instead of a residual identity. -/
structure SourceEscapingComponent (Mc Kz K1 K2 Q1 : Subgroup G) where
  J : Subgroup G
  component_le : J ≤ normalizer (K2 : Set G)
  component : (J.subgroupOf (normalizer (K2 : Set G))).IsCComponent
  quasisimple : IsQuasisimple (J ⧸ pCore 2 J)
  characteristic_normalizer : generalizedFitting (normalizer (K2 : Set G)) =
    pCore 2 (normalizer (K2 : Set G))
  characteristic_component : generalizedFitting J = pCore 2 J
  outside : ¬J ≤ Mc ⊓ normalizer (K2 : Set G)
  normalized_by_closure : Kz ≤ normalizer (J : Set G)
  generated_commutator : J = ⁅J,K1⁆
  second_commutator : ⁅J,K2⁆ ≤ J.pCoreIn 2
  quintic_rank : primeRank 5 J ≤ 1
  rank_one_normal : primeRank 5 J = 1 →
    (J.subgroupOf (normalizer (K2 : Set G))).Normal
  intersection_normalizes_first :
    conjugateSpanBy J Q1 ⊓ (Mc ⊓ normalizer (K2 : Set G)) ≤ normalizer (K1 : Set G)
  pushingUp_alternative : Chapter1.IsSylowIn 2 (Q1 ⊓ J) J ∨ Q1 ≤ normalizer (J : Set G)

variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)

/-- Construct the new source contract from the checked raw extraction. -/
theorem exists_source_escaping_component :
    Nonempty (SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2)) := by
  obtain ⟨J,hJN,hJ,hq,hf,hout,hn,hfirst,hsecond,hr,hrn,_,_,hi,ha⟩ :=
    exists_component_for_model_comparison s d
  exact ⟨{
    J := J
    component_le := hJN
    component := hJ
    quasisimple := hq
    characteristic_normalizer := source_secondNormalizer_characteristicTwo s.ambient T
      s.empty s.maximal s.unique s.many s.module_card s.action s.abelian H s.outside
      a H1 H2 s.critical d
    characteristic_component := hf
    outside := hout
    normalized_by_closure := hn
    generated_commutator := hfirst
    second_commutator := hsecond
    quintic_rank := hr
    rank_one_normal := hrn
    intersection_normalizes_first := hi
    pushingUp_alternative := ha }⟩

variable (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The contained branch supplies the literal C.2.7 input for this extracted component. -/
theorem source_component_contained_input (h : d.K1 ≤ j.J) :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) j.J :=
  contained_component_input s d j.J j.component_le j.component j.quasisimple
    j.characteristic_component j.outside h

/-- The checked natural-row contradiction applies to the new source component. -/
theorem source_component_contained_natural_row_exclusion (h : d.K1 ≤ j.J) :
    ¬Nonempty (ContainedComparison.NaturalStarRow j.J (Mc.pCoreIn 2)) := by
  rintro ⟨row⟩
  exact contained_component_false_of_natural_row s d j.J j.component_le j.component
    j.quasisimple j.characteristic_component j.outside h row

/-- The new source component supplies an actual outer five-element at rank zero. -/
theorem source_component_outer_quintic_of_rank_zero (hr : primeRank 5 j.J = 0) :
    ∃ k : normalizer (j.J : Set G), (k : G) ∈ d.K1 ∧ (k : G) ∉ j.J ∧
      orderOf k = 5 ∧ orderOf (pCoreNormalizerAction 2 j.J k) = 5 ∧
      pCoreNormalizerAction 2 j.J k ∉ MulAut.innerSubgroup (j.J ⧸ pCore 2 j.J) ∧
      orderOf (pCoreNormalizerOuterAction 2 j.J k) = 5 :=
  exists_outer_quintic_of_rank_zero s d j.J j.component_le j.component j.quasisimple
    j.outside hr

/-- At rank one retain both literal action kernels and the original second factor. -/
theorem source_component_rank_one_action_kernel (hr : primeRank 5 j.J = 1) :
    ∃ hn : normalizer (d.K2 : Set G) ≤ normalizer (j.J : Set G),
      ((pCoreNormalizerOuterAction 2 j.J).comp (inclusion hn)).ker =
        j.J.subgroupOf (normalizer (d.K2 : Set G)) ⊔
          ((pCoreNormalizerAction 2 j.J).comp (inclusion hn)).ker ∧
      primeRank 5 (((pCoreNormalizerAction 2 j.J).comp (inclusion hn)).ker) = 1 ∧
      d.K2 ≤ (((pCoreNormalizerAction 2 j.J).comp (inclusion hn)).ker).map
        (normalizer (d.K2 : Set G)).subtype :=
  component_rank_one_outer_action_kernel s d j.J j.component_le j.component
    j.quasisimple j.outside j.characteristic_component hr

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
