module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.Source
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Separating the other FF models from A₈

Actual group equivalences preserve order. The SL₂ order formula bounds its
binary exponent by four, leaving four explicit checks. SL₃ over a field of
order at least four, Sp₄ over such a field, and G₂ over such a field already
have order greater than 20160. Their small derived cases have order at most
the full small group. The alternating and triple-cover cases are smaller,
and PSL₅(2) has order 9999360.

These are exclusions only: no group is recognized from its order. They sift
all the group possibilities in B.4.2 and B.5.1(1), printed pp.86 and 99–102.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve
open Chapter2.ComponentRefinement.LieType.Binary

private theorem card_sl_three (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 3) F))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at h
  exact h.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F)

private theorem power_product_mono {q q' : ℕ} (h : q ≤ q') (a b c : ℕ) :
    q ^ a * (q ^ b - 1) * (q ^ c - 1) ≤
      q' ^ a * (q' ^ b - 1) * (q' ^ c - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h a)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h b) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h c) 1)

/-- No positive binary parameter gives SL₂ order 20160. -/
theorem sl_two_card_ne (f : ℕ) (hf : 0 < f) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (BinaryField f)) ≠ 20160 := by
  rw [Atlas.card_sl_two, GaloisField.card 2 f (by omega)]
  intro h
  have hb : f < 5 := by
    by_contra hn
    have hq : 32 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ f)
    have hh := Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega
  interval_cases f <;> norm_num at h

/-- The SL₃ double-natural family never has an A₈ actor. -/
theorem sl_three_card_ne (f : ℕ) (hf : 0 < f) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (BinaryField f)) ≠ 20160 := by
  rw [card_sl_three, GaloisField.card 2 f (by omega)]
  intro h
  have hb : f < 2 := by
    by_contra hn
    have hq : 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ f)
    have hh := power_product_mono hq 3 3 2
    omega
  have : f = 1 := by omega
  norm_num [this] at h

/-- In B.4.2(9),(11) and B.5.1(1)(iii),(iv), dimension five is excluded. -/
theorem psl_five_card_ne : Nat.card (PSL 5) ≠ 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  rw [Nat.card_zmod] at h
  -- Normalize only the five numerical factors, leaving the group cardinal opaque.
  -- Simplifying a concrete Fintype cardinal can expand its matrix enumeration.
  have hproduct : (∏ i : Fin 5, (2 ^ 5 - 2 ^ i.val)) = 9999360 := by decide
  have hscalar : Nat.gcd 5 (2 - 1) = 1 := by decide
  rw [hscalar, show 2 - 1 = 1 from rfl, mul_one, mul_one, hproduct] at h
  change Nat.card (PSL 5) = 9999360 at h
  omega

/-- The full symplectic groups above the binary field are already too large. -/
theorem symplectic_large_card_ne (f : ℕ) (hf : 1 < f) :
    Nat.card (Matrix.symplecticGroup (Fin 2) (BinaryField f)) ≠ 20160 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, GaloisField.card 2 f (by omega)]
  have hq : 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ f)
  have hh := power_product_mono hq 4 2 4
  omega

/-- The full G₂ groups above the binary field are already too large. -/
theorem g2_large_card_ne (f : ℕ) (hf : 1 < f) :
    Nat.card (Atlas.G2.Model (BinaryField f)) ≠ 20160 := by
  rw [Atlas.G2.card_Model, GaloisField.card 2 f (by omega)]
  have hq : 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ f)
  have hh := power_product_mono hq 6 6 2
  omega

/-- All the remaining irreducible-table actors have order different from A₈. -/
theorem not_other_of_card {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 20160) : ¬ OtherIrreducibleGroup H := by
  intro h
  cases h with
  | linearTwo f hf e => exact sl_two_card_ne f hf ((Nat.card_congr e.toEquiv).symm.trans hcard)
  | linearThree f hf e => exact sl_three_card_ne f hf ((Nat.card_congr e.toEquiv).symm.trans hcard)
  | symplecticSmall e =>
    have hle := (commutator (Matrix.symplecticGroup (Fin 2) (BinaryField 1))).card_le_card_group
    rw [← Nat.card_congr e.toEquiv, hcard,
      Theory.SpecificGroups.SymplecticFour.card_sp, GaloisField.card 2 1 (by decide)] at hle
    norm_num at hle
  | symplecticLarge f hf e =>
    exact symplectic_large_card_ne f hf ((Nat.card_congr e.toEquiv).symm.trans hcard)
  | g2Small e =>
    have hle := (commutator (Atlas.G2.Model (BinaryField 1))).card_le_card_group
    rw [← Nat.card_congr e.toEquiv, hcard,
      Atlas.G2.card_Model, GaloisField.card 2 1 (by decide)] at hle
    norm_num at hle
  | g2Large f hf e => exact g2_large_card_ne f hf ((Nat.card_congr e.toEquiv).symm.trans hcard)
  | alternatingFive e =>
    have h := Nat.card_congr e.toEquiv
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at h
    norm_num at h
  | alternatingSix e =>
    have h := Nat.card_congr e.toEquiv
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at h
    norm_num at h
  | alternatingSeven e =>
    have h := Nat.card_congr e.toEquiv
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at h
    norm_num at h
  | tripleSix f hs _ hk =>
    have h := f.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top, hk, hcard] at h
    rw [nat_card_alternatingGroup, Nat.card_fin] at h
    norm_num at h
  | linearFive e => exact psl_five_card_ne ((Nat.card_congr e.toEquiv).symm.trans hcard)

/-- Only order invariance is used from the supplied, actual alternating-group model. -/
theorem card_of_alternating {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 8)) : Nat.card H = 20160 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve

end
