module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.GroupTheory.SolvableSmallThreeCore
public import Theory.GroupTheory.MaximalTwoLocalElementary
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Elementary-normalizer reduction for the fixed J₄ Sylow pair

Permutability makes the pair product a solvable group of order 2²¹ times
9 or 27. Its three-core has order at most 27, so the small-three-core
theorem forces a nontrivial two-core. Extend the product to a maximal
two-local. The characteristic-center construction identifies that local
with the full ambient normalizer of a nontrivial elementary abelian
two-subgroup A. Sylow maximality puts A inside the fixed two-subgroup,
and that subgroup normalizes A.

Both odd-complement alternatives are retained. The two final placement
contracts concern the actual elementary normalizers just obtained; neither
their exhaustive incidence calculation nor max4 coverage is asserted here.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups of
Sylow subgroups in sporadic groups* (1986). The solvable-core and
characteristic-center steps use the general finite-group results imported
above, rather than assuming a sporadic subgroup table.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

variable [Finite Janko4.Model]

/-- The exact order of the pair product, with neither complement case omitted. -/
theorem fixedTwo_pair_product_orders {S : Sylow 2 Janko4.Model}
    (hS : (S : Subgroup Janko4.Model) = twoSubgroup)
    {R : Subgroup Janko4.Model} (h : PairInput S R) :
    Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model) = 9 * 2 ^ 21 ∨
      Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model) = 27 * 2 ^ 21 := by
  have hSc : Nat.card S = 2 ^ 21 := by
    rw [hS, twoSubgroup_card]
  rw [← hS, EvenRankTwo.product_card h, hSc]
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact Or.inl (by rw [hc]; norm_num)
  · exact Or.inr (by rw [hc]; norm_num)

/-- The three-core of the permuting product has order at most 27. -/
theorem fixedTwo_pair_product_threeCore_card_le {S : Sylow 2 Janko4.Model}
    (hS : (S : Subgroup Janko4.Model) = twoSubgroup)
    {R : Subgroup Janko4.Model} (h : PairInput S R) :
    Nat.card (pCore 3 (R ⊔ twoSubgroup : Subgroup Janko4.Model)) ≤ 27 := by
  rw [← hS]
  let H := R ⊔ (S : Subgroup Janko4.Model)
  have hd := (pCore 3 H).card_subgroup_dvd_card
  change Nat.card (pCore 3 H) ∣ Nat.card (R ⊔ (S : Subgroup Janko4.Model) :
    Subgroup Janko4.Model) at hd
  rw [EvenRankTwo.product_card h] at hd
  have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide)
    (pCore 3 H) (S : Subgroup Janko4.Model) pCore_isPGroup S.isPGroup'
  have hdiv := hcop.dvd_of_dvd_mul_right hd
  have hR : Nat.card R ≤ 27 := by
    rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> decide
  exact (Nat.le_of_dvd Nat.card_pos hdiv).trans hR

/-- The actual product has nontrivial intrinsic two-core in both cases. -/
theorem fixedTwo_pair_product_twoCore_ne_bot {S : Sylow 2 Janko4.Model}
    (hS : (S : Subgroup Janko4.Model) = twoSubgroup)
    {R : Subgroup Janko4.Model} (h : PairInput S R) :
    pCore 2 (R ⊔ twoSubgroup : Subgroup Janko4.Model) ≠ ⊥ := by
  have hsolv : Group.IsSolvable (R ⊔ twoSubgroup : Subgroup Janko4.Model) := by
    rw [← hS]
    exact EvenRankTwo.product_solvable h
  have hprime (p : ℕ) (hp : p.Prime)
      (hd : p ∣ Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model)) : p = 2 ∨ p = 3 := by
    rw [← hS] at hd
    exact EvenRankTwo.product_prime_divisors h hp hd
  have h64 : 64 ∣ Nat.card (R ⊔ twoSubgroup : Subgroup Janko4.Model) := by
    rcases fixedTwo_pair_product_orders hS h with hc | hc <;> rw [hc] <;> norm_num
  exact twoCore_ne_bot_of_solvable_small_three_core hsolv hprime
    (fixedTwo_pair_product_threeCore_card_le hS h) h64

/-- The normality data are relative to `twoSubgroup`, whereas the normalizer
and its maximal two-local property are taken in the whole J₄ model. -/
structure FixedTwoElementaryNormalizer (A : Subgroup Janko4.Model) : Prop where
  le_twoSubgroup : A ≤ twoSubgroup
  ne_bot : A ≠ ⊥
  elementary : IsElementaryAbelian 2 A
  normalized : twoSubgroup ≤ normalizer (A : Set Janko4.Model)
  maximal : IsMaximalTwoLocal (normalizer (A : Set Janko4.Model))

/-- A full elementary normalizer containing the actual pair. The original
permutability hypothesis is used to obtain this normalization conclusion. -/
theorem fixedTwo_pair_elementary_normalizer {S : Sylow 2 Janko4.Model}
    (hS : (S : Subgroup Janko4.Model) = twoSubgroup)
    {R : Subgroup Janko4.Model} (h : PairInput S R) :
    ∃ A : Subgroup Janko4.Model, FixedTwoElementaryNormalizer A ∧
      R ≤ normalizer (A : Set Janko4.Model) := by
  obtain ⟨M, hM, hHM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (R ⊔ twoSubgroup) (fixedTwo_pair_product_twoCore_ne_bot hS h)
  obtain ⟨A, hA, hEA, hMA⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hM
  have hTN : twoSubgroup ≤ normalizer (A : Set Janko4.Model) :=
    hMA ▸ le_sup_right.trans hHM
  have hSN : (S : Subgroup Janko4.Model) ≤ normalizer (A : Set Janko4.Model) :=
    hS ▸ hTN
  let _ := hEA
  have hAS : A ≤ (S : Subgroup Janko4.Model) :=
    sup_eq_left.mp (S.is_maximal'
      (S.isPGroup'.to_sup_of_normal_right' (IsElementaryAbelian.isPGroup 2 A) hSN)
      le_sup_left)
  exact ⟨A, ⟨hAS.trans_eq hS, hA, hEA, hTN, hMA ▸ hM⟩,
    hMA ▸ le_sup_left.trans hHM⟩

/-- Remaining placement for elementary complements in the full normalizers
obtained above. The conclusion includes an actual ambient conjugator. -/
def FixedTwoElementaryNormalizerPlacement : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ R : Subgroup Janko4.Model, PairInput S R →
      IsElementaryAbelian 3 R → Nat.card R = 3 ^ 2 →
      ∀ A : Subgroup Janko4.Model, FixedTwoElementaryNormalizer A →
        R ≤ normalizer (A : Set Janko4.Model) →
        ∃ g : Janko4.Model,
          twoSubgroup ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom ∧
          R ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom

/-- Remaining placement for extraspecial exponent-three complements.
An exclusion of these configurations also proves this contract. -/
def FixedTwoExtraspecialNormalizerPlacement : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ R : Subgroup Janko4.Model, PairInput S R →
      IsExtraspecial 3 R → Nat.card R = 3 ^ 3 → Monoid.exponent R = 3 →
      ∀ A : Subgroup Janko4.Model, FixedTwoElementaryNormalizer A →
        R ≤ normalizer (A : Set Janko4.Model) →
        ∃ g : Janko4.Model,
          twoSubgroup ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom ∧
          R ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
