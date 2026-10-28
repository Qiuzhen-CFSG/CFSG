module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceLocalQuotient
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SpanOddRank
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The literal triality local row in C.3.5

The original conjugate span maps to a perfect subgroup of the component's
central quotient. Its image normalizes the nontrivial image of R intersect K.
The triality normalizer bound therefore gives odd-prime rank at most one;
the exact central quotient preserves the odd ranks of the original span.

This retains the original C.2.8 data and the actual triality carrier at every
positive binary exponent. Source: Aschbacher--Smith C.3.5, printed p.150.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The binary triality central-quotient row bounds the original span's
odd-prime rank, including the field of order two. -/
theorem ordinary_span_primeRank_le_one_of_triality
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (n : ℕ) (hn : 0 < n)
    (e : K ⧸ center K ≃* Triality.Standard.Carrier
      (Triality.Standard.binaryParameters n hn))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (conjugateSpanBy L M) ≤ 1 := by
  apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e ho
  intro A P hA hP hne hN
  let := hA
  exact Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
    n hn P hP hne A hN ho

/-- The actual triality catalogue marking retains the same odd-prime bound. -/
theorem ordinary_span_primeRank_le_one_of_isTrialityGroupAt
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (conjugateSpanBy L M) ≤ 1 := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (K ⧸ center K) n hn).mp hm
  exact h.ordinary_span_primeRank_le_one_of_triality K hK n hn e ho

/-- The binary triality ordinary row forces normalization of the original
A₅-marked source component. -/
theorem normalizes_a5_of_ordinary_triality
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (n : ℕ) (hn : 0 < n)
    (e : K ⧸ center K ≃* Triality.Standard.Carrier
      (Triality.Standard.binaryParameters n hn)) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact h.normalizes_of_a5_span_fiveRank_le_one a
    (h.ordinary_span_primeRank_le_one_of_triality K hK n hn e (by decide))

/-- The Theorem C triality model predicate supplies local normality directly. -/
theorem normalizes_a5_of_ordinary_isTrialityGroupAt
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K)) :
    M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact h.normalizes_of_a5_span_fiveRank_le_one a
    (h.ordinary_span_primeRank_le_one_of_isTrialityGroupAt K hK hn hm (by decide))

end CFSG.Quasithin.ChapterC.HypothesisC28
