module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.FieldTheory.Finite.Basic
public import Theory.AlgebraicGroup.Tori.Basic

universe u

/-! Finite-order points of tori over algebraic extensions of finite fields. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private lemma units_isOfFinOrder_coprime_orderOf
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (a : kˣ) : IsOfFinOrder a ∧ Nat.Coprime (orderOf a) p := by
  let E : IntermediateField (ZMod p) k :=
    IntermediateField.adjoin (ZMod p) {(a : k)}
  let aE : E :=
    ⟨(a : k), IntermediateField.subset_adjoin (ZMod p) {(a : k)}
      (Set.mem_singleton _)⟩
  have haE : aE ≠ 0 := by
    intro h
    apply Units.ne_zero a
    exact congrArg Subtype.val h
  have : FiniteDimensional (ZMod p) E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := ZMod p) (a : k))
  have : Finite E := Module.finite_of_finite (ZMod p)
  let := Fintype.ofFinite E
  have hpowE : aE ^ (Fintype.card E - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one aE haE
  have hpow : a ^ (Fintype.card E - 1) = 1 := by
    apply Units.ext
    change (a : k) ^ (Fintype.card E - 1) = 1
    exact congrArg Subtype.val hpowE
  have hcardpos : 0 < Fintype.card E - 1 := by
    have htwo : 1 < Nat.card E := Finite.one_lt_card
    rw [Nat.card_eq_fintype_card] at htwo
    omega
  have hfin : IsOfFinOrder a :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Fintype.card E - 1, hcardpos, hpow⟩
  have horddvd : orderOf a ∣ Fintype.card E - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  have hcard : Fintype.card E = p ^ Module.finrank (ZMod p) E := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := E), Nat.card_zmod]
  have hd : 0 < Module.finrank (ZMod p) E := Module.finrank_pos
  have hp_dvd : p ∣ p ^ Module.finrank (ZMod p) E :=
    dvd_pow_self p hd.ne'
  have hpow_one : 1 ≤ p ^ Module.finrank (ZMod p) E :=
    Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)
  have hcopPow : Nat.Coprime (p ^ Module.finrank (ZMod p) E - 1)
      (p ^ Module.finrank (ZMod p) E) :=
    (Nat.coprime_self_sub_left hpow_one).2 (Nat.coprime_one_left _)
  have hcopCard : Nat.Coprime (Fintype.card E - 1) p := by
    rw [hcard]
    exact hcopPow.of_dvd_right hp_dvd
  exact ⟨hfin, hcopCard.of_dvd_left horddvd⟩

/-- Every point of `D_n` has finite order coprime to the characteristic when
the ground field is algebraic over its finite prime field. -/
public lemma dVariety_isOfFinOrder_coprime_orderOf
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (n : ℕ) (x : Variety.Point (dVariety k n)) :
    IsOfFinOrder x ∧ Nat.Coprime (orderOf x) p := by
  let e : Variety.Point (dVariety k n) ≃* (Fin n → kˣ) :=
    { dPointEquiv n with
      map_mul' := dPointEquiv_mul n }
  have hcoord : ∀ i,
      IsOfFinOrder (e x i) ∧ Nat.Coprime (orderOf (e x i)) p :=
    fun i ↦ units_isOfFinOrder_coprime_orderOf (e x i)
  have hfinPi : IsOfFinOrder (e x) :=
    IsOfFinOrder.pi fun i ↦ (hcoord i).1
  have hordDvdProd : orderOf (e x) ∣ ∏ i, orderOf (e x i) := by
    rw [Pi.orderOf]
    exact Finset.lcm_dvd_prod _ _
  have hcopProd : Nat.Coprime (∏ i, orderOf (e x i)) p :=
    Nat.coprime_fintype_prod_left_iff.mpr fun i ↦ (hcoord i).2
  have hcopPi : Nat.Coprime (orderOf (e x)) p :=
    hcopProd.of_dvd_left hordDvdProd
  have horder : orderOf (e x) = orderOf x := e.orderOf_eq x
  exact ⟨by
      rw [← orderOf_pos_iff, ← horder]
      exact hfinPi.orderOf_pos,
    by simpa [horder] using hcopPi⟩

/-- Over an algebraic extension of a finite prime field, every element of a
torus has finite order coprime to the characteristic. -/
public theorem torus_elements_finiteOrder_coprime_primeChar
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T) :
    ∀ t : Variety.Point T,
      IsOfFinOrder t ∧ Nat.Coprime (orderOf t) p := by
  rcases hT with ⟨n, ⟨e⟩⟩
  intro t
  let s : Variety.Point (dVariety k n) := e.toMulEquiv.symm t
  have hs : IsOfFinOrder s ∧ Nat.Coprime (orderOf s) p :=
    dVariety_isOfFinOrder_coprime_orderOf n s
  have horder : orderOf s = orderOf t := e.toMulEquiv.symm.orderOf_eq t
  exact ⟨by
      rw [← orderOf_pos_iff, ← horder]
      exact hs.1.orderOf_pos,
    by simpa [horder] using hs.2⟩

end Theory.AlgebraicGroup
