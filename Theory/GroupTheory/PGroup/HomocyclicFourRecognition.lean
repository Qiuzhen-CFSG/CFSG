module

public import Theory.GroupTheory.PGroup.Homocyclic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Tactic

/-!
# Recognizing a product of cyclic groups of order four

A finite abelian group of exponent dividing four is homocyclic of exponent
four precisely when every element of square one has a square root. In the
finite abelian decomposition, exponent bounds leave factors of order two or
four, and the square-root condition excludes the order-two factors. The order
then fixes the number of factors. This supplies the actual coordinate
isomorphism for binary unitary root slices (GLS4, Chapter 4, Lemma 3.4(d5)).
-/

noncomputable section
namespace Theory.GroupTheory
open scoped IsMulCommutative

/-- A square-root criterion constructing the genuine homocyclic isomorphism. -/
public theorem homocyclicFour_of_square_roots {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hsq : ∀ x : A, x ^ 4 = 1)
    (hroot : ∀ x : A, x ^ 2 = 1 → ∃ y : A, y ^ 2 = x)
    {n : ℕ} (hc : Nat.card A = 4 ^ n) :
    Nonempty (A ≃* StandardHomocyclicCover (Fin n) 4) := by
  classical
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨ι, hι, d, hd, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  let B (i : ι) := Multiplicative (ZMod (d i))
  have hexp : Monoid.exponent A ∣ 4 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq
  have hdvd (i : ι) : d i ∣ 4 := by
    have hp := MonoidHom.exponent_dvd (f := (Pi.evalMonoidHom B i).comp e.toMonoidHom)
      ((Function.surjective_eval i).comp e.surjective)
    have he : Monoid.exponent (B i) = d i := ZMod.exponent _
    rw [he] at hp
    exact hp.trans hexp
  have hd4 (i : ι) : d i = 4 := by
    have hi := hd i
    have hv : d i ∣ 2 ^ 2 := hdvd i
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hv
    interval_cases k
    · norm_num at he
      omega
    · have htwo : d i = 2 := by simpa using he
      let x : ∀ j, B j := Pi.mulSingle i (Multiplicative.ofAdd 1)
      have hx : x ^ 2 = 1 := by
        ext j
        by_cases hji : j = i
        · subst j
          simp only [Pi.pow_apply, Pi.one_apply, x, Pi.mulSingle_eq_same]
          change (2 : ℕ) • (1 : ZMod (d i)) = 0
          rw [htwo]
          decide
        · simp [x, hji]
      obtain ⟨y, hy⟩ := hroot (e.symm x) (by rw [← map_pow, hx, map_one])
      have heq := congrArg (fun w => (e w) i) hy
      have hh : (e y i) ^ 2 = Multiplicative.ofAdd (1 : ZMod (d i)) := by
        simpa [map_pow, x] using heq
      have hh' : (2 : ℕ) • (e y i).toAdd = (1 : ZMod (d i)) := hh
      have hz : (2 : ℕ) • (e y i).toAdd = 0 := by
        rw [nsmul_eq_mul]
        have hzero : (2 : ZMod (d i)) = 0 := by rw [htwo]; decide
        simp only [Nat.cast_ofNat, hzero, zero_mul]
      have h01 : (0 : ZMod (d i)) = 1 := hz.symm.trans hh'
      rw [htwo] at h01
      exact (zero_ne_one h01).elim
    · simpa using he
  have ei (i : ι) : B i ≃* Multiplicative (ZMod 4) := by
    dsimp [B]
    rw [hd4 i]
  let f : A ≃* StandardHomocyclicCover ι 4 :=
    (e.trans (MulEquiv.piCongrRight ei)).trans (MulEquiv.funMultiplicative ι (ZMod 4)).symm
  have hcard : Fintype.card ι = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 4)
    have hh := (Nat.card_congr f.toEquiv).symm.trans hc
    simpa [StandardHomocyclicCover, Nat.card_eq_fintype_card] using hh
  let r : (ι → ZMod 4) ≃+ (Fin n → ZMod 4) :=
    { __ := Equiv.arrowCongr (Fintype.equivFinOfCardEq hcard) (Equiv.refl _)
      map_add' := fun _ _ => rfl }
  exact ⟨f.trans r.toMultiplicative⟩

end Theory.GroupTheory
