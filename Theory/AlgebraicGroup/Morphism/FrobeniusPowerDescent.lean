module

public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Mathlib.FieldTheory.Perfect

/-!
# Reversing a morphism after Frobenius

Suppose a surjective algebraic-group morphism `φ : H → G` has the following
coordinate descent property: a characteristic-power of each coordinate of `H`
is a polynomial in the coordinates of its image under `φ`. A common exponent
exists because the presentation has finitely many coordinates. If coordinate
Frobenius acts bijectively on `G`, its sufficiently high power factors through
`φ` by a regular reverse isogeny.

The point map is the inverse of `φ` followed on its input by Frobenius. To
prove regularity, take Frobenius roots of the coefficients of the descended
polynomials. This construction allows inseparable `φ`; it never asserts that
its point inverse is regular. The coordinate descent property itself is a
separate geometric obligation.

This is the inseparability step for the version comparison in GLS3, Chapter 1,
Sections 1.10--1.12 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k]

/-- Finitely many coordinate descent exponents can be replaced by one exponent. -/
theorem Variety.Morphism.exists_uniform_coordinate_frobenius_power
    {H G : Variety k} (φ : Variety.Morphism H G) (p : ℕ)
    (hpow : ∀ i : H.Coordinates, ∃ m : ℕ, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (p ^ m) = evalPolynomial (φ.toFun x).val q) :
    ∃ N : ℕ, ∀ i : H.Coordinates, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (p ^ N) = evalPolynomial (φ.toFun x).val q := by
  classical
  choose m q hq using hpow
  let N := Finset.univ.sup m
  refine ⟨N, fun i => ⟨q i ^ (p ^ (N - m i)), fun x => ?_⟩⟩
  have hi : m i ≤ N := Finset.le_sup (f := m) (Finset.mem_univ i)
  have he : m i + (N - m i) = N := Nat.add_sub_of_le hi
  change _ = MvPolynomial.eval₂ (RingHom.id k) (φ.toFun x).val _
  rw [MvPolynomial.eval₂_pow]
  change _ = evalPolynomial (φ.toFun x).val (q i) ^ (p ^ (N - m i))
  rw [← hq i x, ← pow_mul, ← pow_add, he]

variable (p n : ℕ) [ExpChar k p] [PerfectRing k p]

private theorem evalPolynomial_frobenius_root_coefficients
    {σ : Type*} (q : MvPolynomial σ k) (x : σ → k) :
    evalPolynomial (fun i => x i ^ (p ^ n)) q =
      (evalPolynomial x (MvPolynomial.map
        (iterateFrobeniusEquiv k p n).symm.toRingHom q)) ^ (p ^ n) := by
  let e := iterateFrobeniusEquiv k p n
  change _ = e (MvPolynomial.eval x (MvPolynomial.map e.symm.toRingHom q))
  have h := MvPolynomial.eval₂_comp e.toRingHom x
    (MvPolynomial.map e.symm.toRingHom q)
  rw [MvPolynomial.eval₂_map] at h
  simpa [evalPolynomial, e, iterateFrobeniusEquiv_def, iterateFrobenius_def,
    Function.comp_def] using h.symm

/-- Coordinate power descent already forces injectivity on points. -/
theorem Variety.Morphism.injective_of_coordinate_frobenius_powers
    {H G : Variety k} (φ : Variety.Morphism H G)
    (hpow : ∀ i : H.Coordinates, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (p ^ n) = evalPolynomial (φ.toFun x).val q) :
    Function.Injective φ.toFun := by
  intro x y hxy
  apply Variety.Point.ext
  funext i
  apply (iterateFrobeniusEquiv k p n).injective
  change x.val i ^ (p ^ n) = y.val i ^ (p ^ n)
  obtain ⟨q, hq⟩ := hpow i
  rw [hq, hq, hxy]

/-- Construct a regular reverse isogeny by extracting roots of polynomial
coefficients. The displayed factorization is through Frobenius, not through
the identity morphism. -/
theorem Morphism.exists_reverse_isogeny_of_coordinate_frobenius_powers
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hsurj : Function.Surjective φ.onPoints)
    (Fr : Monoid.End (Variety.Point G)) (hFr : Function.Bijective Fr)
    (hFrcoord : ∀ x i, (Fr x).val i = x.val i ^ (p ^ n))
    (hpow : ∀ i : H.Coordinates, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (p ^ n) = evalPolynomial (φ.onPoints x).val q) :
    ∃ ψ : Morphism G H, IsIsogeny ψ ∧ (φ.comp ψ).onPoints = Fr := by
  let e : Variety.Point H ≃* Variety.Point G :=
    MulEquiv.ofBijective φ.onPoints
      ⟨φ.toVariety.injective_of_coordinate_frobenius_powers p n hpow, hsurj⟩
  let f : Variety.Point G →* Variety.Point H := e.symm.toMonoidHom.comp Fr
  have hf (x : Variety.Point G) : φ.onPoints (f x) = Fr x :=
    e.apply_symm_apply (Fr x)
  let ψ : Morphism G H :=
    { toVariety :=
        { toFun := f
          regular := by
            intro i
            obtain ⟨q, hq⟩ := hpow i
            refine ⟨MvPolynomial.map (iterateFrobeniusEquiv k p n).symm.toRingHom q, ?_⟩
            intro x
            apply (iterateFrobeniusEquiv k p n).injective
            change (f x).val i ^ (p ^ n) = _ ^ (p ^ n)
            rw [hq, hf]
            have hx : (Fr x).val = fun j => x.val j ^ (p ^ n) := funext (hFrcoord x)
            rw [hx]
            exact evalPolynomial_frobenius_root_coefficients p n q x.val }
      map_one := f.map_one
      map_mul := f.map_mul }
  have hbij : Function.Bijective ψ.onPoints := e.symm.bijective.comp hFr
  refine ⟨ψ, ⟨hbij.2, ?_⟩, ?_⟩
  · have hker : ψ.kernel = ⊥ := (MonoidHom.ker_eq_bot_iff ψ.onPoints).mpr hbij.1
    rw [hker]
    infer_instance
  · ext x
    exact hf x

end Theory.AlgebraicGroup
