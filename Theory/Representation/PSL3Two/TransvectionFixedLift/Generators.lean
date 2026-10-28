module

public import Theory.GroupTheory.DihedralGeneratedFactor
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.FinCases

/-!
# A binary plane times a dihedral group from four lifts

Four involutions, two commuting with all the others, give an actual product
isomorphism when their binary coordinates retract the first pair and annihilate
the second. The nontrivial square of the second pair gives a dihedral subgroup.
The retraction proves that multiplication of the two factors is injective;
the cardinality then proves surjectivity.

This is the group-theoretic construction used for the transvection preimage in
Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.61(2),
printed p.1150. No product recognition is assumed.
-/

@[expose] public section
open Subgroup
namespace BinaryLinearThree.TransvectionFixedLift
/-- The multiplicative binary plane. -/
abbrev E := Multiplicative (Fin 2 → ZMod 2)

private def binaryPower {H : Type*} [Group H] (a : H) (ha : a ^ 2 = 1) :
    Multiplicative (ZMod 2) →* H where
  toFun i := a ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change a ^ (i.toAdd + j.toAdd).val = a ^ i.toAdd.val * a ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ ha).symm

private def pairLift {H : Type*} [Group H] (a b : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) : E →* H where
  toFun i := binaryPower a ha (.ofAdd (i.toAdd 0)) * binaryPower b hb (.ofAdd (i.toAdd 1))
  map_one' := by simp
  map_mul' i j := by
    change binaryPower a ha ((.ofAdd (i.toAdd 0)) * (.ofAdd (j.toAdd 0))) *
        binaryPower b hb ((.ofAdd (i.toAdd 1)) * (.ofAdd (j.toAdd 1))) = _
    rw [map_mul, map_mul]
    exact (hab.pow_pow (j.toAdd 0).val (i.toAdd 1).val).mul_mul_mul_comm _ _

private theorem retract_pairLift {H : Type*} [Group H] (r : H →* E) (a b : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (hra : r a = .ofAdd ![1,0]) (hrb : r b = .ofAdd ![0,1]) (i : E) :
    r (pairLift a b ha hb hab i) = i := by
  change r (a ^ (i.toAdd 0).val * b ^ (i.toAdd 1).val) = i
  rw [map_mul, map_pow, map_pow, hra, hrb]
  apply Multiplicative.toAdd.injective
  ext j
  have bit (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hv := x.val_lt
    have hh : x.val = 0 ∨ x.val = 1 := by omega
    rcases hh with hh | hh
    · exact Or.inl (ZMod.val_injective 2 (by simpa using hh))
    · exact Or.inr (ZMod.val_injective 2 (hh.trans (show (1 : ZMod 2).val = 1 from rfl).symm))
  rcases bit (i.toAdd 0) with hi | hi <;>
    rcases bit (i.toAdd 1) with hj | hj <;> fin_cases j <;> simp [hi, hj]

/-- Four involutory generators with a binary retraction and one dihedral pair
construct the direct product of a binary plane and the order-eight dihedral group. -/
theorem nonempty_equiv_of_lifts {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 32) (r : H →* E) (a b c d : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hd : d ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d)
    (hra : r a = .ofAdd ![1,0]) (hrb : r b = .ofAdd ![0,1])
    (hrc : r c = 1) (hrd : r d = 1)
    (hcd : (c * d) ^ 2 ≠ 1) (hfour : (c * d) ^ 4 = 1) :
    Nonempty (H ≃* (E × DihedralGroup 4)) := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hc)
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hd)
  have hinv : d * (c * d) * d⁻¹ = (c * d)⁻¹ := by
    simp only [mul_inv_rev, hci, hdi, mul_assoc]
    rw [← pow_two, hd, mul_one]
  have hout : d ∉ zpowers (c * d) := by
    intro hh
    obtain ⟨k, hk⟩ := hh
    have hcomm : Commute d (c * d) := by
      simpa only [hk] using (Commute.refl (c * d)).zpow_left k
    have he : c * d = (c * d)⁻¹ := by
      simpa only [hcomm.eq, mul_inv_cancel_right] using hinv
    apply hcd
    simpa only [pow_two] using
      (congrArg (fun x : H => x * (c * d)) he).trans (inv_mul_cancel _)
  obtain ⟨hDcard, ⟨eD⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion (by decide : 0 < 4)
    (c * d) d (orderOf_eq_prime_pow (p := 2) (n := 1) hcd hfour) hd hout hinv
  let D := zpowers (c * d) ⊔ zpowers d
  have hDker : D ≤ r.ker := by
    apply sup_le <;> apply zpowers_le.mpr
    · change r (c * d) = 1
      rw [map_mul, hrc, hrd, one_mul]
    · exact hrd
  have hcentral (x : H) (hxc : Commute x c) (hxd : Commute x d) :
      ∀ y : D, Commute x (y : H) := by
    have hle : D ≤ centralizer ({x} : Set H) := by
      apply sup_le <;> apply zpowers_le.mpr <;> apply mem_centralizer_singleton_iff.mpr
      · exact (hxc.mul_right hxd).eq.symm
      · exact hxd.eq.symm
    intro y
    exact (mem_centralizer_singleton_iff.mp (hle y.property)).symm
  let α := pairLift a b ha hb hab
  have hα (i : E) : r (α i) = i := retract_pairLift r a b ha hb hab hra hrb i
  have hcomm (i : E) (y : D) : Commute (α i) (y : H) :=
    ((hcentral a hac had y).pow_left _).mul_left ((hcentral b hbc hbd y).pow_left _)
  let F : E × D →* H := α.noncommCoprod D.subtype hcomm
  have hF : Function.Injective F := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    refine ⟨?_, D.subtype_injective, ?_⟩
    · exact Function.LeftInverse.injective hα
    · apply disjoint_def.mpr
      rintro x ⟨i, rfl⟩ hx
      have hxD : α i ∈ D := by simpa only [D.range_subtype] using hx
      have hi : i = 1 := (hα i).symm.trans (hDker hxD)
      rw [hi, map_one]
  have hsize : Nat.card H ≤ Nat.card (E × D) := by
    rw [Nat.card_prod, hcard]
    have hE : Nat.card E = 4 := by
      change Nat.card (Fin 2 → ZMod 2) = 4
      norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rw [hE]
    change 32 ≤ 4 * Nat.card (zpowers (c * d) ⊔ zpowers d : Subgroup H)
    rw [hDcard]
  exact ⟨(MulEquiv.ofBijective F (hF.bijective_of_nat_card_le hsize)).symm.trans
    ((MulEquiv.refl E).prodCongr eD)⟩
end BinaryLinearThree.TransvectionFixedLift
