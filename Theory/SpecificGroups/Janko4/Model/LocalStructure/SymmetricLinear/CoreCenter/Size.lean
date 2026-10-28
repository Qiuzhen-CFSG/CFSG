module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# Order and normal forms of the J₄ max4 two-core

The fifteen independent binary words give the lower bound. The quotient
S₅ × SL₃(2), together with the ambient two-part bound, gives the matching
upper bound. Thus the normal-closure words enumerate the intrinsic two-core.

Source: the J₄ row of Aschbacher–Smith A.3.12; the literal ATLAS max4 words
and their coordinate certificates are recorded in `SymmetricLinear.SylowTwoPart`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup CharacteristicTwo

 theorem twoCore_card : Nat.card (pCore 2 max4Subgroup) = 2 ^ 15 := by
  have hl : 2 ^ 15 ≤ Nat.card (pCore 2 max4Subgroup) :=
    (SylowTwoPart.seed_card_lower_of_coordinates seedConjugate_coordinates).trans
      (Nat.card_le_card_of_injective
        (inclusion (show seedNormalClosure ≤ pCore 2 max4Subgroup from
          le_sSup ⟨inferInstance, seedNormalClosure_isPGroup⟩)) (inclusion_injective _))
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := max4Subgroup)).exists_card_eq
  have hn15 : 15 ≤ n := by
    rw [hn] at hl
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hl
  have hindex : (pCore 2 max4Subgroup).index = 20160 := by
    change Nat.card (max4Subgroup ⧸ pCore 2 max4Subgroup) = 20160
    rw [Nat.card_congr max4QuotientEquiv.toEquiv, quotientModel_card]
  have he := (pCore 2 max4Subgroup).card_mul_index
  rw [hn, hindex] at he
  have hnle : n ≤ 15 := by
    by_contra! hh
    have hd : 2 ^ 22 ∣ Nat.card Model := by
      apply dvd_trans _ max4Subgroup.card_subgroup_dvd_card
      rw [← he]
      have h64 : 2 ^ 6 ∣ 20160 := by decide
      have h16 : 2 ^ 16 ∣ 2 ^ n := pow_dvd_pow 2 hh
      simpa only [← pow_add] using Nat.mul_dvd_mul h16 h64
    exact OuterReduction.OddIndex.model_two_part_bound hd
  rw [hn, show n = 15 by omega]

 theorem seedNormalClosure_eq_twoCore : seedNormalClosure = pCore 2 max4Subgroup := by
  apply eq_of_le_of_card_ge (show seedNormalClosure ≤ pCore 2 max4Subgroup from
    le_sSup ⟨inferInstance, seedNormalClosure_isPGroup⟩)
  rw [twoCore_card]
  exact SylowTwoPart.seed_card_lower_of_coordinates seedConjugate_coordinates

 theorem seed_card : Nat.card seedNormalClosure = 2 ^ 15 := by
  rw [seedNormalClosure_eq_twoCore, twoCore_card]

 theorem binaryProduct_bijective : Function.Bijective SylowTwoPart.binaryProduct := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨SylowTwoPart.binaryProduct_injective_of_coordinates seedConjugate_coordinates,
    by simp only [Nat.card_fun, Nat.card_fin, seed_card]⟩
end Janko4.LocalStructure.SymmetricLinear
