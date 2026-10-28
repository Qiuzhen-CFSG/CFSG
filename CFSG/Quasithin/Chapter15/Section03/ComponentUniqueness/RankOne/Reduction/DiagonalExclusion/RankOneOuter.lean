module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.InnerAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.Quotient
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.SpecificGroups.Classical.RankOneOuter
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter

/-!+# Inner action in the three-rank-one quotient alternative

All four quotient families in alternative (ii) have abelian actual outer
automorphism group. The binary and prime-field PSL₂ outer groups are cyclic.
The opposite-sign congruence removes the diagonal outer image of PSL₃, and
the unitary congruence gives even field degree and the proved cyclic PSU₃
outer group. The latter uses simplicity inherited from the component.

The relative component is quasisimple, and the trivial odd core of I gives
Z(L) = O₂(L). Faithful central descent embeds Out(L) in the outer group of
the specified quotient model, retaining every central two-cover. The S₃
argument from `InnerAction` then gives literal inner action on L.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), alternative
(ii) and its inner-action implication between 15.3.43(d) and (e), printed
p.1139; compare the model list in 15.3.37 on p.1135. No rank-two assumption
on Y₊ or conclusion of 15.3.35 or 15.3.38 is used.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion

/-- All the source quotient models have abelian outer group after lifting
through the genuine central quotient of the quasisimple component. -/
theorem outer_isMulCommutative_of_rankOneQuotientModel
    {L : Type*} [Group L] [IsQuasisimple L]
    (hcenter : center L = pCore 2 L) (hmodel : Candidates.RankOneQuotientModel L) :
    IsMulCommutative (MulAut.Outer L) := by
  let e₀ : (L ⧸ center L) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  rcases hmodel with ⟨n, hn, hmodel⟩ | ⟨n, hn, hm, hmodel⟩ |
    ⟨n, hn, hm, hmodel⟩ | ⟨p, hp, hmodel⟩
  · obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := hmodel
    let := Fintype.ofFinite F
    have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
      rw [← Nat.card_eq_fintype_card, hF]
      simp [Nat.pow_mod, Nat.ne_of_gt hn])
    let : CharP F 2 := ringChar.of_eq hc
    let := Theory.PSL2.OuterSolvable.charTwo_outer_isCyclic (F := F)
    exact MulAut.outer_isMulCommutative_of_centralQuotient (e₀.trans e)
  · obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := hmodel
    let := Matrix.PSL3.OuterSolvable.outer_isMulCommutative_of_two_power_card_mod_three
      F hn hF hm
    exact MulAut.outer_isMulCommutative_of_centralQuotient (e₀.trans e)
  · obtain ⟨F, hFfield, hFfinite, J, hF, hconj, ⟨e⟩⟩ := hmodel
    have heven : Even n := by
      rw [Nat.even_iff]
      have ht := Nat.BinaryTorusParity.two_pow_mod_three n
      split_ifs at ht <;> omega
    have hn₂ : 1 < n := by
      obtain ⟨k, hk⟩ := heven
      omega
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      (e₀.trans e).isSimpleGroup_congr.mp IsQuasisimple.simple
    let := BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear.outer_isCyclic_of_even
      J hn₂ heven hF hconj
    exact MulAut.outer_isMulCommutative_of_centralQuotient (e₀.trans e)
  · obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := hmodel
    let := Theory.PSL2.OuterSolvable.prime_outer_isCyclic hp.1 hF
    exact MulAut.outer_isMulCommutative_of_centralQuotient (e₀.trans e)

variable {G : Type*} [Group G] [Finite G] {Yplus S M I L : Subgroup G}

/-- The relative component and odd-core hypothesis discharge the central-cover
premises for every model in alternative (ii). -/
theorem LocalSetup.outer_isMulCommutative_of_rankOneQuotientModel
    (h : LocalSetup Yplus S M I L) (hmodel : Candidates.RankOneQuotientModel L) :
    IsMulCommutative (MulAut.Outer L) := by
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  exact DiagonalExclusion.outer_isMulCommutative_of_rankOneQuotientModel
    (Candidates.SignedReduction.local_center_eq_twoCore h.component_le h.component h.odd_core)
    hmodel

/-- Alternative (ii) in the S₃ branch forces literal inner action on L,
including when L is a nontrivial central two-cover of its listed quotient. -/
theorem LocalSetup.inner_of_rankOneQuotientModel (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) (_hrank : primeRank 3 L = 1)
    (hmodel : Candidates.RankOneQuotientModel L) :
    Yplus ≤ L ⊔ centralizer (L : Set G) :=
  h.inner_of_abelian_outer horbit (h.outer_isMulCommutative_of_rankOneQuotientModel hmodel)

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
