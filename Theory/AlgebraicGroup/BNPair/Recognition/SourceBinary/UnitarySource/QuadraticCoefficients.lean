module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ScalarSubfield
public import Mathlib.FieldTheory.Fixed
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Compatible quadratic scalars and their actual fixed field

Both fields are subfields of the same commuting ring. The nth Frobenius
on its 2n-degree subfield is an involution, and its fixed field is explicitly
isomorphic, by inclusion of the very same elements, to the n-degree
subfield. The cardinal calculation proves that the involution is nontrivial.
Thus the matrix-field order is q squared and the fixed-field order is q,
including q=2 and q=4, without an assumed coefficient involution.

This supplies the quadratic scalar data in CoefficientApplication. It does
not identify the independent rank-one module realizations or their labels.
Source: Fong--Seitz II (8B)--(8C), printed pp.201--203.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.ScalarSubfield
variable (E : Type*) [Field E] [CharP E 2] [Finite E]

@[expose] def conjugation (n : ℕ) : field E (2*n) ≃+* field E (2*n) :=
  iterateFrobeniusEquiv (field E (2*n)) 2 n

theorem conjugation_involutive (n : ℕ) : Function.Involutive (conjugation E n) := by
  intro a
  apply Subtype.ext
  change ((a : E) ^ (2 ^ n)) ^ (2 ^ n) = (a : E)
  rw [← pow_mul, ← pow_add, ← two_mul]
  exact a.property

omit [Finite E] in
theorem field_le_double (n : ℕ) : field E n ≤ field E (2*n) := by
  intro a ha
  change a ^ (2 ^ (2*n)) = a
  change a ^ (2 ^ n) = a at ha
  rw [two_mul, pow_add, pow_mul, ha, ha]

@[expose] def fixedFieldEquiv (n : ℕ) :
    field E n ≃+* FixedBy.subfield (field E (2*n)) (conjugation E n) where
  toFun a := ⟨⟨a,field_le_double E n a.property⟩,by
    apply Subtype.ext
    exact a.property⟩
  invFun a := ⟨a.val.val,congrArg Subtype.val a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem quadratic_cards (n : ℕ) (hn : 0 < n)
    (hd : 2 ^ (2*n) - 1 ∣ Nat.card E - 1) :
    Nat.card (field E (2*n)) = (2 ^ n)^2 ∧
    Nat.card (FixedBy.subfield (field E (2*n)) (conjugation E n)) = 2^n := by
  constructor
  · rw [card_eq E (2*n) (by omega) hd, ← pow_mul, Nat.mul_comm n 2]
  · rw [← Nat.card_congr (fixedFieldEquiv E n).toEquiv]
    exact card_eq E n hn ((Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left n 2)).trans hd)

theorem conjugation_ne_one (n : ℕ) (hn : 0 < n)
    (hd : 2 ^ (2*n) - 1 ∣ Nat.card E - 1) : conjugation E n ≠ RingEquiv.refl _ := by
  intro he
  have hs : Function.Surjective
      (FixedBy.subfield (field E (2*n)) (conjugation E n)).subtype := by
    intro a
    exact ⟨⟨a,by change conjugation E n a = a; rw [he]; rfl⟩,rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective
    (FixedBy.subfield (field E (2*n)) (conjugation E n)).subtype
    ⟨Subtype.val_injective,hs⟩)
  obtain ⟨hbig,hsmall⟩ := quadratic_cards E n hn hd
  rw [hsmall,hbig] at hc
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) hn.ne'
  nlinarith

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.ScalarSubfield
