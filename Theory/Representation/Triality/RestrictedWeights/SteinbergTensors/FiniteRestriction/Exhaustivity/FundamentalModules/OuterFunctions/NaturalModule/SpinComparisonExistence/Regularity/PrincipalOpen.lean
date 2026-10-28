module

public import Theory.AlgebraicGroup.Variety.PrincipalOpenDescent
public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Theory.AlgebraicGroup.Morphism.Operations
public import Theory.AlgebraicGroup.Morphism.Basic

/-!
# Globalizing a homomorphism regular on one principal open

A point homomorphism with a regular representative on one nonempty principal
open of an affine algebraic group is regular everywhere. For each target
coordinate, consider the ideal of polynomial functions whose product with
that coordinate is polynomial. Translation and clearing denominators show
that this ideal has no common zero. The affine maximal-ideal point theorem
then makes it the unit ideal, supplying a global polynomial representative.

This is the globalization step after the root-product open chart in Steinberg
(6.2), `refs/KGroup/GLS3/Chapter2St2.tex`. It works for arbitrary affine
algebraic groups over an algebraically closed field and requires no
connectedness or separability assumption. The chart regularity premise is
explicit. The private denominator calculation follows
`Theory/AlgebraicGroup/Variety/PrincipalOpenDescent.lean`.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k]

private lemma clear_denominators {σ : Type u} (f : MvPolynomial σ k)
    (p : MvPolynomial (Option σ) k) :
    ∃ n : ℕ, ∃ q : MvPolynomial σ k, ∀ x : σ → k,
      evalPolynomial x f ≠ 0 →
      evalPolynomial x f ^ n *
          evalPolynomial (fun i => i.elim (evalPolynomial x f)⁻¹ x) p =
        evalPolynomial x q := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact ⟨0, MvPolynomial.C a, fun x hx => by simp [evalPolynomial]⟩
  | add p q hp hq =>
      obtain ⟨n, p', hp'⟩ := hp
      obtain ⟨m, q', hq'⟩ := hq
      refine ⟨n + m, f ^ m * p' + f ^ n * q', ?_⟩
      intro x hx
      simp only [evalPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_pow]
      change evalPolynomial x f ^ (n + m) *
          (evalPolynomial (fun i => i.elim (evalPolynomial x f)⁻¹ x) p +
            evalPolynomial (fun i => i.elim (evalPolynomial x f)⁻¹ x) q) = _
      rw [pow_add]
      calc
        _ = evalPolynomial x f ^ m *
              (evalPolynomial x f ^ n * evalPolynomial (fun i => i.elim (evalPolynomial x f)⁻¹ x) p) +
            evalPolynomial x f ^ n *
              (evalPolynomial x f ^ m * evalPolynomial (fun i => i.elim (evalPolynomial x f)⁻¹ x) q) := by ring
        _ = _ := by rw [hp' x hx, hq' x hx]; rfl
  | mul_X p i hp =>
      obtain ⟨n, p', hp'⟩ := hp
      cases i with
      | none =>
          refine ⟨n + 1, p', ?_⟩
          intro x hx
          rw [evalPolynomial_mul, evalPolynomial_X]
          simp only [Option.elim_none, pow_succ]
          calc
            _ = (evalPolynomial x f ^ n *
                evalPolynomial (fun i => i.elim (evalPolynomial x f)⁻¹ x) p) *
                (evalPolynomial x f * (evalPolynomial x f)⁻¹) := by ring
            _ = _ := by rw [hp' x hx, mul_inv_cancel₀ hx, mul_one]
      | some i =>
          refine ⟨n, p' * MvPolynomial.X i, ?_⟩
          intro x hx
          rw [evalPolynomial_mul, evalPolynomial_X, evalPolynomial_mul, evalPolynomial_X]
          simp only [Option.elim_some, ← mul_assoc, hp' x hx]

variable [IsAlgClosed k]

/-- A homomorphism regular on one nonempty principal open is regular everywhere. -/
private theorem exists_morphism_of_local_polynomial_functions
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (ψ : Variety.Point G →* Variety.Point H)
    (f : Variety.PolynomialFunction G)
    (hf : ∃ z, f z ≠ 0)
    (hloc : ∀ a : Variety.PolynomialFunction H,
      ∃ n : ℕ, ∃ p : Variety.PolynomialFunction G,
        ∀ x, f x ≠ 0 → f x ^ n * a (ψ x) = p x) :
    ∃ F : Morphism G H, F.onPoints = ψ := by
  refine ⟨⟨⟨ψ, ?_⟩, ψ.map_one, ψ.map_mul⟩, rfl⟩
  intro j
  let h : Variety.Point G → k := fun x => (ψ x).val j
  let I : Ideal (Variety.PolynomialFunction G) :=
    { carrier := {p | ∃ q : Variety.PolynomialFunction G, ∀ x, p x * h x = q x}
      zero_mem' := ⟨0, by intro x; exact zero_mul _⟩
      add_mem' := by
        rintro p q ⟨p', hp⟩ ⟨q', hq⟩
        refine ⟨p' + q', ?_⟩
        intro x
        change (p x + q x) * h x = p' x + q' x
        rw [add_mul, hp, hq]
      smul_mem' := by
        rintro p q ⟨q', hq⟩
        refine ⟨p * q', ?_⟩
        intro x
        change (p x * q x) * h x = p x * q' x
        rw [mul_assoc, hq] }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨y, hy⟩ := G.exists_pointPrime_eq_of_isMaximal m hm
    obtain ⟨z, hz⟩ := hf
    let t : Variety.Point G := z * y⁻¹
    let a : Variety.PolynomialFunction H :=
      Variety.PolynomialFunction.pullback
        (leftMulMorphism H (ψ t)⁻¹)
        (Variety.PolynomialFunction.ofPolynomial H (MvPolynomial.X j))
    obtain ⟨n, p, hp⟩ := hloc a
    let ft : Variety.PolynomialFunction G :=
      Variety.PolynomialFunction.pullback (leftMulMorphism G t) f
    let pt : Variety.PolynomialFunction G :=
      Variety.PolynomialFunction.pullback (leftMulMorphism G t) p
    have heq (x : Variety.Point G) (hx : ft x ≠ 0) :
        ft x ^ n * h x = pt x := by
      have hpx := hp (t * x) hx
      have ha : a (ψ (t * x)) = h x := by
        change evalPolynomial ((leftMulMorphism H (ψ t)⁻¹).toFun
          (ψ (t * x))).val (MvPolynomial.X j) = _
        rw [evalPolynomial_X, leftMulMorphism_apply]
        rw [show ψ (t * x) = ψ t * ψ x from ψ.map_mul t x, inv_mul_cancel_left]
      rw [ha] at hpx
      exact hpx
    have hmem : ft ^ (n + 1) ∈ I := by
      refine ⟨ft * pt, ?_⟩
      intro x
      change ft x ^ (n + 1) * h x = ft x * pt x
      by_cases hx : ft x = 0
      · simp [hx]
      · rw [pow_succ]
        calc
          _ = ft x * (ft x ^ n * h x) := by ring
          _ = _ := by rw [heq x hx]
    have hmemb : ft ^ (n + 1) ∈ (G.pointPrime y).asIdeal := by
      rw [hy]
      exact hIm hmem
    have hzero : ft y ^ (n + 1) = 0 := hmemb
    have hval : ft y = f z := by
      change f (t * y) = f z
      simp [t]
    rw [hval] at hzero
    exact (pow_ne_zero _ hz) hzero
  have hmem : (1 : Variety.PolynomialFunction G) ∈ I := by rw [hI]; trivial
  obtain ⟨p, hp⟩ := hmem
  obtain ⟨q, hq⟩ := p.representedBy
  refine ⟨q, ?_⟩
  intro x
  have hh : h x = p x := by
    have hx := hp x
    change 1 * h x = p x at hx
    simpa only [one_mul] using hx
  exact hh.trans (hq x)

/-- A regular chart representative on a nonempty principal open suffices. -/
public theorem Morphism.exists_of_nonempty_principalOpen
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (ψ : Variety.Point G →* Variety.Point H)
    (f : MvPolynomial G.Coordinates k)
    (hf : ∃ z : Variety.Point G, evalPolynomial z.val f ≠ 0)
    (F : Variety.Morphism (G.principalOpenChart f) H)
    (hF : ∀ x, F.toFun x = ψ ((G.principalOpenChartInclusion f).toFun x)) :
    ∃ Φ : Morphism G H, Φ.onPoints = ψ := by
  apply exists_morphism_of_local_polynomial_functions ψ
    (Variety.PolynomialFunction.ofPolynomial G f) hf
  intro a
  obtain ⟨p, hp⟩ := (Variety.PolynomialFunction.pullback F a).representedBy
  obtain ⟨n, q, hq⟩ := clear_denominators f p
  refine ⟨n, Variety.PolynomialFunction.ofPolynomial G q, ?_⟩
  intro x hx
  change evalPolynomial x.val f ≠ 0 at hx
  have hpx := hp (G.principalOpenChartLift f x hx)
  change a (F.toFun (G.principalOpenChartLift f x hx)) = _ at hpx
  rw [hF, Variety.principalOpenChartInclusion_lift] at hpx
  change evalPolynomial x.val f ^ n * a (ψ x) = evalPolynomial x.val q
  rw [hpx]
  exact hq x.val hx

end Theory.AlgebraicGroup
