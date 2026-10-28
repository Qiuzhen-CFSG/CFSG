module

public import Theory.SpecificGroups.PSL2.QuadraticFieldInvolutionFixed
public import GorensteinWalter.PGL2Cardinality

/-!
# Quadratic fixed groups in every odd characteristic

The fixed-group model and odd index hold also in characteristic three.
The restriction p>3 in the nonsolvability theorem is unnecessary for these
two conclusions. A direct order calculation proves odd index in all odd
characteristics, and projective Hilbert90 transports the literal full group.

This removes the small-characteristic edge in the quadratic fusion argument
of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem coefficient_fixed_odd_index
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Odd (psl2FieldAut F σ).fixedSubgroup.index := by
  let E := FixedPoints.subfield (zpowers σ) F
  let P := (psl2FieldAut F σ).fixedSubgroup
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hE : Nat.card E = p := OddSquareFieldFixed.fixed_subfield_card hF σ hσ
  obtain ⟨d⟩ := OddSquareFieldFixed.coefficient_fixed_equiv ho hF σ hσ
  have hP : Nat.card P = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr d.toEquiv, pgl2_card_formula, hE]
  have hG := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho.pow)
  rw [hF] at hG
  have hidx := P.card_mul_index
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hsub : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel hp2
  have hsub4 : (p ^ 2) ^ 2 - 1 + 1 = (p ^ 2) ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hfactor : p ^ 2 * ((p ^ 2) ^ 2 - 1) = (p * (p ^ 2 - 1)) * (p * (p ^ 2 + 1)) := by
    zify [hp2] at hsub hsub4 ⊢
    nlinarith only [hsub, hsub4]
  have hi : 2 * P.index = p * (p ^ 2 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P))
    calc
      Nat.card P * (2 * P.index) = (Nat.card P * P.index) * 2 := by ring
      _ = p ^ 2 * ((p ^ 2) ^ 2 - 1) := by rw [hidx]; exact hG
      _ = Nat.card P * (p * (p ^ 2 + 1)) := by rw [hP]; exact hfactor
  have hm := congrArg (fun n : ℕ => n % 4) hi
  have hodd := Nat.odd_iff.mp ho
  have hb := Nat.mod_lt p (by decide : 0 < 4)
  have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hr : (p * (p ^ 2 + 1)) % 4 = 2 := by
    rw [Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
    rcases hpmod with hh | hh <;> norm_num [hh]
  rw [hr] at hm
  change Odd P.index
  exact Nat.odd_iff.mpr (by omega)

/-- In every odd characteristic, the whole fixed subgroup of an arbitrary
quadratic semilinear involution has odd index and the fixed-field PGL₂ model. -/
theorem quadratic_semilinear_involution_fixed_all_odd
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1) :
    let hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
    let hc : 3 < Nat.card F := by
      have hp := (Fact.out : p.Prime).two_le
      rw [hF]; nlinarith
    let a := pGammaL2ToMulAutPSL2 F hodd hc x
    Odd a.fixedSubgroup.index ∧ Nonempty
      (a.fixedSubgroup ≃* PGL2 (FixedPoints.subfield (zpowers x.right) F)) := by
  intro hodd hc a
  have hs : orderOf x.right = 2 := orderOf_eq_prime_iff.mpr ⟨by
    have hh := congrArg SemidirectProduct.right (pow_orderOf_eq_one x)
    simpa only [hx, pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right] using hh,
    hf⟩
  let f := pGammaL2ToMulAutPSL2 F hodd hc
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr hodd x hx hf
  let b : MulAut PSL(2,F) := f (SemidirectProduct.inl c)
  have he : b⁻¹ * a * b = psl2FieldAut F x.right := by
    have hh := congrArg f hc
    simpa only [map_mul, map_inv, f, pGammaL2ToMulAutPSL2_inr] using hh
  have he' : MulAut.congr b.symm a = psl2FieldAut F x.right := he
  have hm : Nonempty (a.fixedSubgroup ≃* (psl2FieldAut F x.right).fixedSubgroup) := by
    rw [← he']
    exact ⟨MulAut.fixedSubgroupCongr b.symm a⟩
  obtain ⟨e⟩ := hm
  obtain ⟨d⟩ := OddSquareFieldFixed.coefficient_fixed_equiv ho hF x.right hs
  have hi : a.fixedSubgroup.index = (psl2FieldAut F x.right).fixedSubgroup.index := by
    have hcard : Nat.card a.fixedSubgroup = Nat.card (psl2FieldAut F x.right).fixedSubgroup :=
      Nat.card_congr e.toEquiv
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := a.fixedSubgroup))
    rw [a.fixedSubgroup.card_mul_index, hcard,
      (psl2FieldAut F x.right).fixedSubgroup.card_mul_index]
  exact ⟨hi ▸ coefficient_fixed_odd_index ho hF x.right hs, ⟨e.trans d⟩⟩

end Theory.PSL2
