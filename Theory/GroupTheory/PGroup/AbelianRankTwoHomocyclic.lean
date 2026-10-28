module
public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Theory.GroupTheory.SpecificGroups.AbelianUnequalTwoFactorsAut

/-!
# Rank-two abelian two-groups with an order-three automorphism

A finite abelian two-group whose first omega subgroup has order four and
which admits an automorphism of order three is a product of two cyclic
groups of the same nontrivial two-power order.

The finite abelian structure theorem supplies nontrivial cyclic factors.
Every factor has two-power order and a square kernel of order two, so the
omega order forces exactly two factors. Unequal exponents would make the
whole automorphism group a two-group, contradicting the given order three.
No fixed-point-free action or product decomposition is assumed.

This is the intrinsic abelian-group step in Janko–Thompson,
Math. Z. 113 (1970), §6, p.394, independent of the ambient simple group
and of Brauer's homocyclic Sylow theorem.
-/

open scoped IsMulCommutative

namespace AbelianRankTwoHomocyclic

private def squareKerEquiv {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    (powMonoidHom 2 : A →* A).ker ≃* (powMonoidHom 2 : B →* B).ker where
  toFun x := ⟨e x, by change (e x)^2 = 1; rw [← map_pow, show (x : A)^2 = 1 from x.property, map_one]⟩
  invFun x := ⟨e.symm x, by change (e.symm x)^2 = 1; rw [← map_pow, show (x : B)^2 = 1 from x.property, map_one]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e (x : A) (y : A))

private def squareKerPiEquiv {ι : Type*} (B : ι → Type*) [∀ i, CommGroup (B i)] :
    (powMonoidHom 2 : (∀ i, B i) →* (∀ i, B i)).ker ≃
      (∀ i, (powMonoidHom 2 : B i →* B i).ker) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def piReindex {ι κ : Type*} (B : ι → Type*) [∀ i, Group (B i)] (e : κ ≃ ι) :
    (∀ i, B i) ≃* (∀ j, B (e j)) where
  __ := (Equiv.piCongrLeft B e).symm
  map_mul' _ _ := rfl

private def piTwo (B : Fin 2 → Type*) [∀ i, Group (B i)] :
    (∀ i, B i) ≃* B 0 × B 1 where
  __ := piFinTwoEquiv B
  map_mul' _ _ := rfl

/-- Omega order four forces exactly two nontrivial cyclic factors. -/
public theorem _root_.IsPGroup.equiv_two_cyclic_factors_of_card_omega_one_eq_four
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hfour : Nat.card (omega₁ A (p := 2)) = 4) :
    ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
      (A ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^m)))) := by
  classical
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨ι, hι, d, hd, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  let B (i : ι) := Multiplicative (ZMod (d i))
  have hB (i : ι) : IsPGroup 2 (B i) :=
    (hA.of_equiv e).of_surjective (Pi.evalMonoidHom B i)
      (Function.surjective_eval i)
  have hpow (i : ι) : ∃ n : ℕ, d i = 2^n := by
    have : NeZero (d i) := ⟨by have := hd i; omega⟩
    simpa [B] using (IsPGroup.iff_card.mp (hB i))
  choose n hn using hpow
  have hnpos (i : ι) : 1 ≤ n i := by
    have := hd i
    rw [hn i] at this
    by_contra h
    have : n i = 0 := by omega
    simp_all
  have hcardker (i : ι) : Nat.card (powMonoidHom 2 : B i →* B i).ker = 2 := by
    let : NeZero (d i) := ⟨by have := hd i; omega⟩
    rw [IsCyclic.card_powMonoidHom_ker]
    have hdiv : 2 ∣ d i := by rw [hn i]; exact dvd_pow_self 2 (by have := hnpos i; omega)
    simp [B, Nat.gcd_eq_right hdiv]
  have hcard : 2 ^ Fintype.card ι = 4 := by
    rw [← IsPGroup.square_ker_eq_omega_one] at hfour
    rw [Nat.card_congr (squareKerEquiv e).toEquiv,
      Nat.card_congr (squareKerPiEquiv B), Nat.card_pi] at hfour
    simpa only [hcardker, Finset.prod_const, Finset.card_univ] using hfour
  have htwo : Fintype.card ι = 2 := Nat.pow_right_injective (by decide : 2 ≤ 2) hcard
  let f := (Fintype.equivFinOfCardEq htwo).symm
  refine ⟨n (f 0), n (f 1), hnpos _, hnpos _, ⟨?_⟩⟩
  have hc (i : ι) : B i ≃* Multiplicative (ZMod (2^(n i))) := by
    dsimp [B]
    rw [hn i]
  exact (e.trans (piReindex B f)).trans
    ((piTwo (fun j => B (f j))).trans ((hc (f 0)).prodCongr (hc (f 1))))

end AbelianRankTwoHomocyclic

/-- A rank-two abelian two-group admitting an order-three automorphism is homocyclic. -/
public theorem IsPGroup.exists_equiv_prod_self_zmod_of_orderOf_aut_eq_three
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hfour : Nat.card (omega₁ A (p := 2)) = 4)
    (a : MulAut A) (ha : orderOf a = 3) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty
      (A ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  obtain ⟨n, m, hn, _, ⟨e⟩⟩ :=
    hA.equiv_two_cyclic_factors_of_card_omega_one_eq_four hfour
  have heq : n = m := by
    by_contra hne
    have hAut : IsPGroup 2 (MulAut A) :=
      (abelian_unequal_two_factors_aut_isPGroup n m hne).of_equiv (MulAut.congr e).symm
    have ha1 : a ≠ 1 := by intro h; simp [h] at ha
    have hd := hAut.dvd_orderOf ha1
    rw [ha] at hd
    norm_num at hd
  subst m
  exact ⟨n, hn, ⟨e⟩⟩
