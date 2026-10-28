module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# Odd-rank isolation of a component

A centerless quasisimple two-core quotient carrying the full ambient odd
prime rank leaves no room for that prime in a different C-component.
Pass to the actual ambient two-core quotient, where the distinguished
factor is an ordinary component. Distinct factors commute; the trivial
center makes their odd ranks add. Rank zero and the two-core order then
recover the prime-to-p order of the original second component.

Source: the component-rank argument in Aschbacher–Smith A.3.18 and
13.6.27, printed pp.51–52 and934. The J₂ consumer applies it at p=5.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- Every other C-component has order prime to an odd prime whose full
ambient rank is carried by the distinguished centerless quotient. -/
theorem IsCComponent.other_coprime_of_full_odd_rank
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hr : primeRank p G ≤ primeRank p (K ⧸ pCore 2 K))
    {D : Subgroup G} (hD : D.IsCComponent) (hne : D ≠ K) :
    Nat.Coprime p (Nat.card D) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let E := D.map q
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hB : B.IsCComponent := hK.map_quotient _
  have hE : E.IsCComponent := hD.map_quotient _
  have hcomp : IsComponent (G ⧸ pCore 2 G) B := ⟨hB.subnormal, inferInstance⟩
  have hcomm : E ≤ centralizer (B : Set (G ⧸ pCore 2 G)) := by
    rw [←commutator_eq_bot_iff_le_centralizer, commutator_comm]
    rcases hcomp.subnormal_dichotomy E hE.subnormal with hle | hc
    · exact (hne (hD.eq_of_map_quotient_eq hK _ (hB.eq_of_le hE hle).symm)).elim
    · exact hc
  have hcard : Nat.card (center B) = 1 := by
    rw [←Nat.card_congr (centerCongr e).toEquiv,hz]
    simp
  have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    E B hcomm (show Nat.Coprime p (Nat.card (center B)) by rw [hcard]; exact Nat.coprime_one_right p)
  have hrB : primeRank p B = primeRank p (K ⧸ pCore 2 K) := (primeRank_congr p e).symm
  have hrQ : primeRank p (G ⧸ pCore 2 G) ≤ primeRank p G :=
    primeRank_quotient_le_of_isTwoGroup p hp _ pCore_isPGroup
  have hzero : primeRank p E = 0 := by omega
  have hcop : Nat.Coprime p (Nat.card (D ⧸ pCore 2 D)) := by
    rw [Nat.card_congr (cComponentTwoCoreQuotientEquiv hD).toEquiv]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (PrimeRank.eq_zero_iff_not_dvd_card.mp hzero)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D)]
  apply hcop.mul_right
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_right.mpr hp).pow_right n
end Subgroup
