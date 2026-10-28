module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SmallMGenericity
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Generic
public import Stellmacher.SectionOne.LemmaOneFiveRelativeM
public import Stellmacher.SectionOne.LocalCommutatorThreeGroup
public import Stellmacher.SectionOne.OrderTwoOddComplementClassification
public import Theory.GroupAction.PTimesQ
public import Theory.GroupAction.CoprimeHall
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.PCore.PPrimeCoreFactorization
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The local quotient action

For an order-two maximal offender A, the local commutator subgroup centralizes A. The descended action on C_V(A) is faithful once its original kernel is A; the P-times-Q argument provides the odd centralizer reduction.

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne.SmallMProof

universe u

open RankOneThreeGroupAssembly

public theorem local_odd_centralizer_eq_bot_of_p_times_q
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S) (hAS : A ≤ S)
    (hA_elem : IsElementaryAbelian 2 A) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    W_A ⊓ fixingSubgroup G (FixedPoints.subgroup A V : Set V) = ⊥ := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let Q := W_A ⊓ fixingSubgroup G (FixedPoints.subgroup A V : Set V)
  have hScentA : S ≤ Subgroup.centralizer (A : Set G) := by
    let : IsElementaryAbelian 2 S := hS_elem
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := S)).comm ⟨s, hs⟩ ⟨a, hAS ha⟩)).symm
  have hWAcentA : W_A ≤ Subgroup.centralizer (A : Set G) := by
    exact (Subgroup.commutator_le_sup _ _).trans
      (sup_le inf_le_right hScentA)
  have hQcentA : Q ≤ Subgroup.centralizer (A : Set G) :=
    inf_le_left.trans hWAcentA
  have hAQcomm : ⁅A, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQcentA
  have hQleW : Q ≤ oddCore G := by
    let : (oddCore G).Normal := pPrimeCore_normal
    exact inf_le_left.trans
      ((Subgroup.commutator_mono inf_le_left le_rfl).trans
        (Subgroup.commutator_le_left (oddCore G) S))
  have hQcop : Nat.Coprime 2 (Nat.card Q) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hQleW)
      pPrimeCore_coprime_card
  have hQtriv : Q ≤ fixingSubgroup G (Set.univ : Set V) :=
    p_times_q_lemma A Q (hA_elem.isPGroup 2 A) hQcop hAQcomm inf_le_right
  have hQbot : Q ≤ ⊥ := by
    rw [← h.action_faithful]
    exact hQtriv
  exact le_antisymm hQbot bot_le

public theorem sylow_two_card_eq_two_or_ge_four
    {G : Type u} [Group G] [Finite G]
    (hG_even : Even (Nat.card G)) (S : Sylow 2 G) :
    Nat.card (S : Subgroup G) = 2 ∨ 4 ≤ Nat.card (S : Subgroup G) := by
  have hS_ne : (S : Subgroup G) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S hG_even.two_dvd
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  by_cases hn1 : n = 1
  · left
    simpa [hn1] using hn
  · right
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hS_ne
      apply (Subgroup.eq_bot_iff_card (S : Subgroup G)).2
      simpa [hn0] using hn
    rw [hn]
    have : 2 ≤ n := by omega
    simpa using
      (pow_le_pow_right' (a := (2 : ℕ)) (n := 2) (m := n) (by omega) this)

/- The subgroup `A` is central in the local group `W_A S`, so the quotient
used by the source is defined without any additional normality hypothesis. -/

public theorem local_A_normal
    {G : Type u} [Group G]
    (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S) (hAS : A ≤ S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    (A.subgroupOf H).Normal := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  have hScentA : S ≤ Subgroup.centralizer (A : Set G) := by
    let : IsElementaryAbelian 2 S := hS_elem
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := S)).comm
        ⟨s, hs⟩ ⟨a, hAS ha⟩)).symm
  have hWAcentA : W_A ≤ Subgroup.centralizer (A : Set G) := by
    exact (Subgroup.commutator_le_sup _ _).trans
      (sup_le inf_le_right hScentA)
  have hHcentA : H ≤ Subgroup.centralizer (A : Set G) :=
    sup_le hWAcentA hScentA
  have hAleH : A ≤ H := hAS.trans le_sup_right
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAleH).2
    (hHcentA.trans (Subgroup.centralizer_le_normalizer (A : Set G)))

public theorem quotient_fixedPoints_action_faithful_of_kernel_eq
    {H V : Type u} [Group H] [Group V] [MulDistribMulAction H V]
    (A : Subgroup H) [A.Normal]
    [IsInvariant H V (FixedPoints.subgroup A V)]
    (hker : fixingSubgroup H
      (Set.univ : Set (FixedPoints.subgroup A V)) = A) :
    fixingSubgroup (H ⧸ A)
        (Set.univ : Set (FixedPoints.subgroup A V)) = ⊥ := by
  apply le_antisymm
  · intro x hx
    induction x using QuotientGroup.induction_on with
    | _ h =>
      have hhfix : h ∈ fixingSubgroup H
          (Set.univ : Set (FixedPoints.subgroup A V)) := by
        rw [mem_fixingSubgroup_iff]
        intro v _hv
        exact ((mem_fixingSubgroup_iff (H ⧸ A)).mp hx) v (Set.mem_univ v)
      rw [hker] at hhfix
      have hq : (h : H ⧸ A) = 1 := (QuotientGroup.eq_one_iff h).mpr hhfix
      simp [hq]
  · exact bot_le

end Stellmacher.SectionOne.SmallMProof
