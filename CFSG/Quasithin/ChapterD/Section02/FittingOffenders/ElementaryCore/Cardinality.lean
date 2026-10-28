module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.Basic
public import Theory.GroupAction.KleinFourPGroupCardinality
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Order and commutator conclusions for the three-core

The Brauer--Wielandt formula bounds the order of a three-group by the
product of its three involution centralizer orders, hence by 27 under
the preceding hyperplane conclusions. A faithful four-group cannot act
on a group of order one or three. Coprime decomposition and the trivial
common centralizer give the full commutator subgroup.

Source: Aschbacher--Smith, D.2.14(2), printed p.186. These conclusions do
not assert elementarity: the module-support argument is still needed
to eliminate the Frattini subgroup. Once that is supplied, a basis gives
the actual product-of-cyclic-groups equivalence.
-/

public section
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G]

private def conjugation (P A : Subgroup G) (hn : A ≤ normalizer (P : Set G)) :
    A →* MulAut P := P.normalizerMonoidHom.comp (inclusion hn)

private theorem conjugation_ker (P A : Subgroup G) (hn : A ≤ normalizer (P : Set G)) :
    (conjugation P A hn).ker = (centralizer (P : Set G)).subgroupOf A := by
  ext a
  change inclusion hn a ∈ P.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

private theorem conjugation_injective (P A : Subgroup G)
    (hn : A ≤ normalizer (P : Set G))
    (hf : A ⊓ centralizer (P : Set G) = ⊥) :
    Function.Injective (conjugation P A hn) := by
  apply (injective_iff_map_eq_one (conjugation P A hn)).mpr
  intro a ha
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hf]
  refine ⟨a.property, mem_centralizer_iff.mpr ?_⟩
  intro p hp
  have he := congrArg (fun f : MulAut P => ((f ⟨p, hp⟩ : P) : G)) ha
  change (a : G) * p * (a : G)⁻¹ = p at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem fixed_conjugation_iff (P A : Subgroup G)
    (hn : A ≤ normalizer (P : Set G)) (a : A) (p : P) :
    p ∈ (conjugation P A hn a).fixedSubgroup ↔
      (p : G) ∈ centralizer (zpowers (a : G) : Set G) := by
  rw [MulAut.mem_fixedSubgroup, Subtype.ext_iff, zpowers_eq_closure,
    centralizer_closure, mem_centralizer_singleton_iff]
  change (a : G) * (p : G) * (a : G)⁻¹ = (p : G) ↔ _
  exact mul_inv_eq_iff_eq_mul.trans eq_comm

private theorem fixed_conjugation_card (P A : Subgroup G)
    (hn : A ≤ normalizer (P : Set G)) (a : A) :
    Nat.card (conjugation P A hn a).fixedSubgroup =
      Nat.card (P ⊓ centralizer (zpowers (a : G) : Set G) : Subgroup G) := by
  apply Nat.card_congr
  exact {
    toFun := fun p => ⟨p.val.val, p.val.property,
      (fixed_conjugation_iff P A hn a p.val).mp p.property⟩
    invFun := fun p => ⟨⟨p.val, p.property.1⟩,
      (fixed_conjugation_iff P A hn a _).mpr p.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem centralizer_card_le_three (P A : Subgroup G)
    [IsElementaryAbelian 2 A]
    (hc : ∀ B ≤ A, rank B = 1 → P ⊓ centralizer (B : Set G) ≠ ⊥ →
      Nat.card (P ⊓ centralizer (B : Set G) : Subgroup G) = 3)
    (a : A) (ha : a ≠ 1) :
    Nat.card (P ⊓ centralizer (zpowers (a : G) : Set G) : Subgroup G) ≤ 3 := by
  by_cases ht : P ⊓ centralizer (zpowers (a : G) : Set G) = ⊥
  · simp [ht]
  have ho : orderOf (a : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
    (fun h => ha (Subtype.ext h))
  have hr : rank (zpowers (a : G)) = 1 := by
    simp only [rank, Nat.card_zpowers, ho]
    decide
  exact (hc _ (zpowers_le.mpr a.property) hr ht).le

variable [Finite G]

/-- The three hyperplane centralizers bound the order even before elementarity is proved. -/
theorem card_le_twentySeven (P A : Subgroup G) (hP : IsPGroup 3 P)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hn : A ≤ normalizer (P : Set G))
    (hc : ∀ B ≤ A, rank B = 1 → P ⊓ centralizer (B : Set G) ≠ ⊥ →
      Nat.card (P ⊓ centralizer (B : Set G) : Subgroup G) = 3) : Nat.card P ≤ 27 := by
  let f := conjugation P A hn
  have hsquare (a : A) : a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hinv (a : A) : Function.Involutive (f a) := by
    intro p
    change (f a * f a) p = p
    rw [← map_mul, ← pow_two, hsquare a, map_one]
    rfl
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := A)
    (by simp only [ENat.card_eq_coe_natCard, hA]; decide) 1 a
  have hab : a * b ≠ 1 := by
    intro he
    apply hba
    exact (eq_inv_of_mul_eq_one_right he).trans
      (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare a))
  have hcomm : Commute (f a) (f b) := by
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul, mul_comm a b]
  obtain ⟨n, hnP⟩ := hP.exists_card_eq
  have hodd : Odd (Nat.card P) := hnP ▸ (by decide : Odd 3).pow
  have he := Theory.GroupAction.brauerWielandt_fixedSubgroup_card_of_isPGroup
    hP hodd (f a) (f b) (hinv a) (hinv b) hcomm
  have hbnd (c : A) (hcn : c ≠ 1) : Nat.card (f c).fixedSubgroup ≤ 3 := by
    rw [fixed_conjugation_card]
    exact centralizer_card_le_three P A hc c hcn
  rw [← map_mul] at he
  calc
    Nat.card P ≤ Nat.card P * Nat.card ((f a).fixedSubgroup ⊓
        (f b).fixedSubgroup : Subgroup P) ^ 2 :=
      Nat.le_mul_of_pos_right _ (pow_pos Nat.card_pos 2)
    _ = _ := he
    _ ≤ 3 * 3 * 3 := Nat.mul_le_mul (Nat.mul_le_mul (hbnd a ha) (hbnd b hb))
      (hbnd (a * b) hab)
    _ = 27 := rfl

/-- Faithfulness of the four-group excludes the two smallest three-group orders. -/
theorem card_ne_one_and_three (P A : Subgroup G) (hA : Nat.card A = 4)
    (hn : A ≤ normalizer (P : Set G))
    (hf : A ⊓ centralizer (P : Set G) = ⊥) :
    Nat.card P ≠ 1 ∧ Nat.card P ≠ 3 := by
  have hi := conjugation_injective P A hn hf
  constructor
  · intro hP
    have hb : P = ⊥ := card_eq_one.mp hP
    have hcent : centralizer (P : Set G) = ⊤ := by
      rw [hb]
      ext x
      simp [mem_centralizer_iff]
    have hAb : A = ⊥ := by simpa only [hcent, inf_top_eq] using hf
    have hcA : Nat.card A = 1 := card_eq_one.mpr hAb
    omega
  · intro hP
    let : IsCyclic P := isCyclic_of_prime_card hP
    have hd := card_dvd_of_injective (conjugation P A hn) hi
    rw [IsCyclic.card_mulAut, hP, hA] at hd
    norm_num [Nat.totient_prime Nat.prime_three] at hd

/-- The order is exactly `3²` or `3³`; this assertion does not presuppose elementarity. -/
theorem exists_card_exponent (P A : Subgroup G) (hP : IsPGroup 3 P)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hn : A ≤ normalizer (P : Set G))
    (hf : A ⊓ centralizer (P : Set G) = ⊥)
    (hc : ∀ B ≤ A, rank B = 1 → P ⊓ centralizer (B : Set G) ≠ ⊥ →
      Nat.card (P ⊓ centralizer (B : Set G) : Subgroup G) = 3) :
    ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card P = 3 ^ s := by
  obtain ⟨s, hs⟩ := hP.exists_card_eq
  have hbound := card_le_twentySeven P A hP hA hn hc
  have hsmall := card_ne_one_and_three P A hA hn hf
  have hsle : s ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
    (by simpa only [hs] using hbound)
  refine ⟨s, ?_, hs⟩
  have hs0 : s ≠ 0 := by intro h; apply hsmall.1; simp [hs, h]
  have hs1 : s ≠ 1 := by intro h; apply hsmall.2; simp [hs, h]
  omega

/-- The common-centralizer hypothesis supplies the literal ambient commutator conclusion. -/
theorem commutator_eq (P A : Subgroup G) (hP : IsPGroup 3 P)
    (hA : Nat.card A = 4) (hn : A ≤ normalizer (P : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥) : ⁅P, A⁆ = P := by
  let : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨n, hnP⟩ := hP.exists_card_eq
  have hc : Nat.Coprime (Nat.card A) (Nat.card P) := by
    rw [hA, hnP]
    exact (by decide : Nat.Coprime 4 3).pow_right n
  simpa only [hfix, sup_bot_eq] using
    (eq_commutator_sup_centralizer_of_solvable_coprime P A hn inferInstance hc).symm

/-- The kernel of the four-group action on an invariant order-three subgroup
is a hyperplane. Centrality of the line in `P` is not needed for this step. -/
theorem line_centralizer_card (P A Z : Subgroup G) (hA : Nat.card A = 4)
    (hZP : Z ≤ P) (hZ : Nat.card Z = 3)
    (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥) :
    Nat.card (A ⊓ centralizer (Z : Set G) : Subgroup G) = 2 := by
  let f := conjugation Z A hnZ
  let : IsCyclic Z := isCyclic_of_prime_card hZ
  have hAut : Nat.card (MulAut Z) = 2 := by
    rw [IsCyclic.card_mulAut, hZ, Nat.totient_prime Nat.prime_three]
  have hrdiv : Nat.card f.range ∣ 2 := hAut ▸ f.range.card_subgroup_dvd_card
  have hr : Nat.card f.range = 2 := by
    apply (Nat.dvd_prime Nat.prime_two).mp hrdiv |>.resolve_left
    intro hrone
    have hrbot : f.range = ⊥ := card_eq_one.mp hrone
    have hAC : A ≤ centralizer (Z : Set G) := by
      intro a ha
      have hk : (⟨a, ha⟩ : A) ∈ f.ker := by
        apply MonoidHom.mem_ker.mpr
        exact mem_bot.mp (hrbot ▸ (show f ⟨a, ha⟩ ∈ f.range from ⟨⟨a, ha⟩, rfl⟩))
      rw [conjugation_ker] at hk
      exact hk
    have hb : Z = ⊥ := le_bot_iff.mp
      ((le_inf hZP (le_centralizer_iff.mp hAC)).trans_eq hfix)
    have hZ1 : Nat.card Z = 1 := card_eq_one.mpr hb
    omega
  have hkc : Nat.card f.ker =
      Nat.card (A ⊓ centralizer (Z : Set G) : Subgroup G) := by
    change Nat.card (conjugation Z A hnZ).ker = _
    rw [conjugation_ker]
    exact Nat.card_congr {
      toFun := fun a => ⟨a.val.val, a.val.property, a.property⟩
      invFun := fun a => ⟨⟨a.val, a.property.1⟩, a.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : Nat.card A = Nat.card f.range * Nat.card f.ker := by
    rw [← index_ker, index_mul_card]
  rw [hA, hr, hkc] at he
  omega

/-- The preceding hyperplane centralizer is exactly the prescribed invariant
order-three subgroup, in the original ambient group. -/
theorem line_eq_hyperplane_centralizer (P A Z : Subgroup G) (hA : Nat.card A = 4)
    (hZP : Z ≤ P) (hZ : Nat.card Z = 3)
    (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hc : ∀ B ≤ A, rank B = 1 → P ⊓ centralizer (B : Set G) ≠ ⊥ →
      Nat.card (P ⊓ centralizer (B : Set G) : Subgroup G) = 3) :
    rank (A ⊓ centralizer (Z : Set G)) = 1 ∧
      P ⊓ centralizer ((A ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) = Z := by
  let B := A ⊓ centralizer (Z : Set G)
  have hB : Nat.card B = 2 := line_centralizer_card P A Z hA hZP hZ hnZ hfix
  have hr : rank B = 1 := by simp only [rank, hB]; decide
  have hZD : Z ≤ P ⊓ centralizer (B : Set G) :=
    le_inf hZP (le_centralizer_iff.mp (show B ≤ centralizer (Z : Set G) from inf_le_right))
  have hDne : P ⊓ centralizer (B : Set G) ≠ ⊥ := by
    intro he
    have hZb := le_bot_iff.mp (hZD.trans_eq he)
    have hZ1 : Nat.card Z = 1 := card_eq_one.mpr hZb
    omega
  refine ⟨hr, (eq_of_le_of_card_ge hZD ?_).symm⟩
  rw [hc B inf_le_left hr hDne, hZ]

end CFSG.Quasithin.ChapterD.ElementaryCore
