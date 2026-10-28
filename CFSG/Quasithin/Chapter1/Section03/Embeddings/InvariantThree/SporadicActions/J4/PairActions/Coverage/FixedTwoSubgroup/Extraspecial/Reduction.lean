module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.LocalReduction

public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Large two-cores in the extraspecial J₄ pair product

For a permuting pair with odd complement of order 27, let H = RS and
K = O₂(H). The quotient H/K has trivial two-core. Its three-core has
order at most 27, so the small-three-core theorem implies that 64 does
not divide |H/K|. Since |H| = 27 · 2²¹, we obtain |K| ≥ 2¹⁶.

Embed K in the ambient model. Both R and S normalize K, and Sylow
maximality puts K inside S, with [S:K] ≤ 32. In fact K is radical:
O₂(N(K)) lies in S and is normal in H, hence lies in K. The image of H
in the actual quotient N(K)/K is solvable of order 27 · [S:K] and has
trivial two-core. Thus the remaining model calculation concerns radical
normal subgroups of the fixed Sylow subgroup of index at most 32. No
list of these subgroups or quotient exclusion is asserted here.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed
p.511 (PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups
of Sylow subgroups in sporadic groups* (1986). The large-core reduction
uses the general solvable-group theorem in `SolvableSmallThreeCore`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Janko4.OuterReduction.OddIndex
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
variable [Finite Janko4.Model]

/-- The actual order-27 pair product has a two-core of order at least 2¹⁶. -/
theorem fixedTwo_order27_product_twoCore_card_ge {S : Sylow 2 Janko4.Model}
    (hS : (S : Subgroup Janko4.Model) = twoSubgroup)
    {R : Subgroup Janko4.Model} (h : PairInput S R) (hR : Nat.card R = 27) :
    2 ^ 16 ≤ Nat.card (pCore 2 (R ⊔ twoSubgroup : Subgroup Janko4.Model)) := by
  let H := R ⊔ twoSubgroup
  let K := pCore 2 H
  let Q := H ⧸ K
  have hcH : Nat.card H = 27 * 2 ^ 21 := by
    change Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model) = _
    rw [← hS, EvenRankTwo.product_card h, hR]
    have hcS : Nat.card S = 2 ^ 21 := by rw [hS, twoSubgroup_card]
    rw [hcS]
  let _ : Group.IsSolvable H := by
    change Group.IsSolvable (R ⊔ twoSubgroup : Subgroup Janko4.Model)
    rw [← hS]
    exact EvenRankTwo.product_solvable h
  have hQdvd : Nat.card Q ∣ Nat.card H := card_quotient_dvd_card K
  have hsmall : Nat.card (pCore 3 Q) ≤ 27 := by
    have hd := (pCore 3 Q).card_subgroup_dvd_card.trans hQdvd
    rw [hcH] at hd
    have hcop : Nat.Coprime (Nat.card (pCore 3 Q)) (2 ^ 21) := by
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := Q)).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow n 21
    exact Nat.le_of_dvd (by decide) (hcop.dvd_of_dvd_mul_right hd)
  have hprime (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card Q) : p = 2 ∨ p = 3 := by
    have hdH := hd.trans hQdvd
    change p ∣ Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model) at hdH
    rw [← hS] at hdH
    exact EvenRankTwo.product_prime_divisors h hp hdH
  have hno : ¬ 64 ∣ Nat.card Q := by
    intro hd
    exact twoCore_ne_bot_of_solvable_small_three_core inferInstance hprime hsmall hd
      (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  change Nat.card K = 2 ^ n at hn
  have hmul : 2 ^ n * Nat.card Q = 27 * 2 ^ 21 := by
    rw [← hn]
    exact K.card_mul_index.trans hcH
  have hnlarge : 16 ≤ n := by
    by_contra! hnsmall
    have hndvd : 2 ^ n ∣ 2 ^ 15 := Nat.pow_dvd_pow 2 (by omega)
    have hd : 2 ^ 21 ∣ 2 ^ 15 * Nat.card Q := by
      apply dvd_trans (show 2 ^ 21 ∣ 2 ^ n * Nat.card Q by rw [hmul]; exact dvd_mul_left _ _)
      exact mul_dvd_mul hndvd dvd_rfl
    have hd' : 2 ^ 15 * 64 ∣ 2 ^ 15 * Nat.card Q := by norm_num at hd ⊢; exact hd
    exact hno (Nat.dvd_of_mul_dvd_mul_left (by positivity) hd')
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnlarge


/-- The quotient is by K inside its ambient normalizer, not an ambient
quotient of J₄ or an assumed abstract local model. -/
abbrev FixedTwoLargeNormalizerQuotient (K : Subgroup Janko4.Model) :=
  normalizer (K : Set Janko4.Model) ⧸ K.subgroupOf (normalizer (K : Set Janko4.Model))

/-- The pair produces a small-index normal subgroup of the fixed Sylow
subgroup, which is radical, and a solvable subgroup with trivial two-core
in its actual normalizer quotient. -/
theorem fixedTwo_order27_largeNormalizerQuotient {S : Sylow 2 Janko4.Model}
    (hS : (S : Subgroup Janko4.Model) = twoSubgroup)
    {R : Subgroup Janko4.Model} (h : PairInput S R) (hR : Nat.card R = 27) :
    ∃ K : Subgroup Janko4.Model,
      K ≤ twoSubgroup ∧ twoSubgroup ≤ normalizer (K : Set Janko4.Model) ∧
      R ≤ normalizer (K : Set Janko4.Model) ∧
      2 ^ 16 ≤ Nat.card K ∧ K.relIndex twoSubgroup ≤ 32 ∧ K.IsPRadical 2 ∧
      ∃ L : Subgroup (FixedTwoLargeNormalizerQuotient K), Group.IsSolvable L ∧ pCore 2 L = ⊥ ∧
        Nat.card L = 27 * K.relIndex twoSubgroup := by
  let H := R ⊔ twoSubgroup
  let C := pCore 2 H
  let K := C.map H.subtype
  have hHN : H ≤ normalizer (K : Set Janko4.Model) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      C.le_normalizer_map H.subtype
  have hSN : (S : Subgroup Janko4.Model) ≤ normalizer (K : Set Janko4.Model) :=
    hS ▸ le_sup_right.trans hHN
  have hKS : K ≤ (S : Subgroup Janko4.Model) :=
    sup_eq_left.mp (S.is_maximal'
      (S.isPGroup'.to_sup_of_normal_right' (pCore_isPGroup.map H.subtype) hSN)
      le_sup_left)
  have hKT : K ≤ twoSubgroup := hKS.trans_eq hS
  have hKcard : Nat.card K = Nat.card C :=
    (Nat.card_congr (C.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
  have hKlarge : 2 ^ 16 ≤ Nat.card K := by
    rw [hKcard]
    exact fixedTwo_order27_product_twoCore_card_ge hS h hR
  have hKmul : Nat.card K * K.relIndex twoSubgroup = 2 ^ 21 := by
    have hc := (K.subgroupOf twoSubgroup).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hKT).toEquiv, twoSubgroup_card] at hc
    exact hc
  have hKi : K.relIndex twoSubgroup ≤ 32 := by
    have hb := Nat.mul_le_mul_right (K.relIndex twoSubgroup) hKlarge
    rw [hKmul] at hb
    norm_num at hb
    omega
  let N := normalizer (K : Set Janko4.Model)
  have hrad : K.IsPRadical 2 := by
    refine ⟨?_, ?_⟩
    · intro hb
      rw [hb, Subgroup.card_bot] at hKlarge
      norm_num at hKlarge
    let B := (pCore 2 N).map N.subtype
    have hNB : N ≤ normalizer (B : Set Janko4.Model) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 N).le_normalizer_map N.subtype
    have hBS : B ≤ (S : Subgroup Janko4.Model) :=
      sup_eq_left.mp (S.is_maximal'
        (S.isPGroup'.to_sup_of_normal_right' (pCore_isPGroup.map N.subtype)
          (hSN.trans hNB)) le_sup_left)
    have hBH : B ≤ H := hBS.trans (hS ▸ le_sup_right)
    have hBK : B ≤ K :=
      le_pCoreIn_of_normalizes (pCore_isPGroup.map N.subtype) hBH (hHN.trans hNB)
    exact le_antisymm hBK (le_map_pCore_normalizer (pCore_isPGroup.map H.subtype))
  let f : H →* FixedTwoLargeNormalizerQuotient K :=
    (QuotientGroup.mk' (K.subgroupOf N)).comp (inclusion hHN)
  have hfker : f.ker = C := by
    ext x
    change QuotientGroup.mk' (K.subgroupOf N) (inclusion hHN x) = 1 ↔ x ∈ C
    exact (QuotientGroup.eq_one_iff (inclusion hHN x)).trans
      (mem_map_iff_mem H.subtype_injective)
  have hcH : Nat.card H = 27 * 2 ^ 21 := by
    change Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model) = _
    rw [← hS, EvenRankTwo.product_card h, hR]
    have hcS : Nat.card S = 2 ^ 21 := by rw [hS, twoSubgroup_card]
    rw [hcS]
  have hfmul : Nat.card K * Nat.card f.range = 27 * 2 ^ 21 := by
    rw [hKcard, ← hfker, ← index_ker, Subgroup.card_mul_index, hcH]
  have hfcard : Nat.card f.range = 27 * K.relIndex twoSubgroup := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K))
    calc
      Nat.card K * Nat.card f.range = 27 * 2 ^ 21 := hfmul
      _ = Nat.card K * (27 * K.relIndex twoSubgroup) := by rw [← hKmul]; ring
  let _ : Group.IsSolvable H := by
    change Group.IsSolvable (R ⊔ twoSubgroup : Subgroup Janko4.Model)
    rw [← hS]
    exact EvenRankTwo.product_solvable h
  have hfsol : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hfcore : pCore 2 f.range = ⊥ := by
    let e : (H ⧸ C) ≃* f.range :=
      (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        (QuotientGroup.quotientKerEquivRange f)
    have he := pCore_map_iso 2 e
    rw [show pCore 2 (H ⧸ C) = ⊥ from pCore_quotient_pCore_eq_bot 2,
      Subgroup.map_bot] at he
    exact he.symm
  exact ⟨K, hKT, le_sup_right.trans hHN, le_sup_left.trans hHN,
    hKlarge, hKi, hrad, f.range, hfsol, hfcore, hfcard⟩


/-- The remaining concrete calculation, independent of the elementary
normalizer A: exclude the specified orders in the actual quotients for
radical normal subgroups K of the fixed Sylow subgroup with index at
most 32, for solvable quotient subgroups with trivial two-core.
This definition is a proof obligation, not a subgroup-table theorem. -/
def FixedTwoLargeNormalizerQuotientExclusion : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ K : Subgroup Janko4.Model, K ≤ twoSubgroup →
      twoSubgroup ≤ normalizer (K : Set Janko4.Model) →
      K.relIndex twoSubgroup ≤ 32 → K.IsPRadical 2 →
      ∀ L : Subgroup (FixedTwoLargeNormalizerQuotient K), Group.IsSolvable L →
        pCore 2 L = ⊥ → Nat.card L ≠ 27 * K.relIndex twoSubgroup

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
