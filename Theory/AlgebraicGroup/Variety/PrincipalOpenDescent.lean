module

public import Theory.AlgebraicGroup.Variety.PrincipalOpen
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Descent over two principal opens

The chart of a polynomial `f` is the presented affine variety obtained by
adjoining one coordinate `t` with `t * f = 1`. Its points are identified with
the principal-open points from `Variety.PrincipalOpen`.

For coprime polynomial functions `f` and `g`, a prescribed point map which
factors regularly on both charts is globally polynomial. We clear the powers
of each denominator, multiply once more by that denominator to extend the
identity across its zero locus, and use a Bézout identity for the two powers.
The argument concerns polynomial functions on rational points, consistently
with `Variety.Morphism`, and works over any field.

This extends the principal-open graph presentation described in GLS,
Chapter 2, §2.2, as used in `Variety.PrincipalOpen`.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k]

/-- The affine graph presentation of the principal open `f ≠ 0`.
The coordinate `none` is the inverse of `f`; `some i` is an original coordinate. -/
public abbrev Variety.principalOpenChart (V : Variety k) (f : MvPolynomial V.Coordinates k) :
    Variety k where
  Coordinates := Option V.Coordinates
  finiteCoordinates := inferInstance
  equations := MvPolynomial.rename some '' V.equations ∪
    {MvPolynomial.X none * MvPolynomial.rename some f - 1}

/-- Forgetting the inverse coordinate is a polynomial morphism. -/
@[expose]
public def Variety.principalOpenChartInclusion (V : Variety k) (f : MvPolynomial V.Coordinates k) :
    Variety.Morphism (V.principalOpenChart f) V where
  toFun x := ⟨fun i => x.val (some i), by
    intro p hp
    have h := x.isZero (MvPolynomial.rename some p) (Or.inl ⟨p, hp, rfl⟩)
    simpa only [evalPolynomial_rename, Function.comp_def] using h⟩
  regular i := ⟨MvPolynomial.X (some i), fun x => by simp [evalPolynomial]⟩

/-- Lift a point with nonzero `f` to the affine principal-open chart. -/
@[expose]
public def Variety.principalOpenChartLift {V : Variety k} (f : MvPolynomial V.Coordinates k)
    (x : Variety.Point V) (hx : evalPolynomial x.val f ≠ 0) :
    Variety.Point (V.principalOpenChart f) where
  val i := i.elim (evalPolynomial x.val f)⁻¹ x.val
  isZero := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · simpa only [evalPolynomial_rename, Function.comp_def, Option.elim_some] using x.isZero q hq
    · rcases Set.mem_singleton_iff.mp hp with rfl
      change (MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i => i.elim (evalPolynomial x.val f)⁻¹ x.val))
        (MvPolynomial.X none * MvPolynomial.rename some f - 1) = 0
      rw [map_sub, map_mul, map_one]
      simp only [MvPolynomial.eval₂Hom_X', Option.elim_none]
      change (evalPolynomial x.val f)⁻¹ *
        evalPolynomial (fun i => i.elim (evalPolynomial x.val f)⁻¹ x.val)
          (MvPolynomial.rename some f) - 1 = 0
      rw [evalPolynomial_rename]
      change (evalPolynomial x.val f)⁻¹ * evalPolynomial x.val f - 1 = 0
      rw [inv_mul_cancel₀ hx, sub_self]

/-- The chart inclusion lands in the nonvanishing locus of `f`. -/
public lemma Variety.principalOpenChart_nonzero {V : Variety k} (f : MvPolynomial V.Coordinates k)
    (x : Variety.Point (V.principalOpenChart f)) :
    evalPolynomial ((V.principalOpenChartInclusion f).toFun x).val f ≠ 0 := by
  have h := x.isZero (MvPolynomial.X none * MvPolynomial.rename some f - 1)
    (Or.inr rfl)
  have heq : x.val none * evalPolynomial ((V.principalOpenChartInclusion f).toFun x).val f = 1 := by
    apply sub_eq_zero.mp
    change (MvPolynomial.eval₂Hom (RingHom.id k) x.val)
      (MvPolynomial.X none * MvPolynomial.rename some f - 1) = 0 at h
    rw [map_sub, map_mul, map_one] at h
    simp only [MvPolynomial.eval₂Hom_X'] at h
    change x.val none * evalPolynomial x.val (MvPolynomial.rename some f) - 1 = 0 at h
    rw [evalPolynomial_rename] at h
    exact h
  exact fun hz => by rw [hz, mul_zero] at heq; exact zero_ne_one heq

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

/-- Functions given locally by polynomial numerators over powers of two
coprime polynomial functions have a global polynomial representative. -/
public lemma Variety.PolynomialFunction.exists_of_coprime_principalOpen
    {V : Variety k} (f g : Variety.PolynomialFunction V)
    (hfg : IsCoprime f g) (h : Variety.Point V → k)
    (hf : ∃ n : ℕ, ∃ p : Variety.PolynomialFunction V, ∀ x, f x ≠ 0 → f x ^ n * h x = p x)
    (hg : ∃ n : ℕ, ∃ p : Variety.PolynomialFunction V, ∀ x, g x ≠ 0 → g x ^ n * h x = p x) :
    ∃ p : Variety.PolynomialFunction V, ∀ x, h x = p x := by
  obtain ⟨n, p, hp⟩ := hf
  obtain ⟨m, q, hq⟩ := hg
  have hp' (x) : f x ^ (n + 1) * h x = f x * p x := by
    by_cases hx : f x = 0
    · simp [hx]
    · rw [pow_succ]
      calc
        _ = f x * (f x ^ n * h x) := by ring
        _ = _ := by rw [hp x hx]
  have hq' (x) : g x ^ (m + 1) * h x = g x * q x := by
    by_cases hx : g x = 0
    · simp [hx]
    · rw [pow_succ]
      calc
        _ = g x * (g x ^ m * h x) := by ring
        _ = _ := by rw [hq x hx]
  obtain ⟨a, b, hab⟩ := hfg.pow (m := n + 1) (n := m + 1)
  refine ⟨a * (f * p) + b * (g * q), ?_⟩
  intro x
  have habx := congrArg (fun t : Variety.PolynomialFunction V => t x) hab
  change a x * f x ^ (n + 1) + b x * g x ^ (m + 1) = 1 at habx
  change h x = a x * (f x * p x) + b x * (g x * q x)
  rw [← hp' x, ← hq' x]
  calc
    _ = (a x * f x ^ (n + 1) + b x * g x ^ (m + 1)) * h x := by rw [habx, one_mul]
    _ = _ := by ring

/-- The canonical chart lift lies over its prescribed point. -/
@[simp] public lemma Variety.principalOpenChartInclusion_lift
    {V : Variety k} (f : MvPolynomial V.Coordinates k)
    (x : Variety.Point V) (hx : evalPolynomial x.val f ≠ 0) :
    (V.principalOpenChartInclusion f).toFun (V.principalOpenChartLift f x hx) = x := by
  apply Variety.Point.ext
  rfl

/-- The extra chart coordinate is the inverse of the selected polynomial. -/
public lemma Variety.principalOpenChart_val_none
    {V : Variety k} (f : MvPolynomial V.Coordinates k)
    (x : Variety.Point (V.principalOpenChart f)) :
    x.val none = (evalPolynomial ((V.principalOpenChartInclusion f).toFun x).val f)⁻¹ := by
  have h := x.isZero (MvPolynomial.X none * MvPolynomial.rename some f - 1)
    (Or.inr rfl)
  change (MvPolynomial.eval₂Hom (RingHom.id k) x.val)
    (MvPolynomial.X none * MvPolynomial.rename some f - 1) = 0 at h
  rw [map_sub, map_mul, map_one, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_rename] at h
  have hmul := sub_eq_zero.mp h
  apply (mul_left_injective₀ (Variety.principalOpenChart_nonzero f x))
  dsimp only
  rw [inv_mul_cancel₀ (Variety.principalOpenChart_nonzero f x)]
  exact hmul

/-- The affine chart has precisely the points of the existing principal-open locus. -/
@[expose]
public def Variety.principalOpenChartPointEquiv
    (V : Variety k) (f : MvPolynomial V.Coordinates k) :
    Variety.Point (V.principalOpenChart f) ≃
      Variety.PrincipalOpenPoint V (fun _ : Unit => f) where
  toFun x := ⟨(V.principalOpenChartInclusion f).toFun x, fun _ => Variety.principalOpenChart_nonzero f x⟩
  invFun x := V.principalOpenChartLift f x.1 (x.2 ())
  left_inv x := by
    apply Variety.Point.ext
    funext i
    cases i with
    | none => exact (Variety.principalOpenChart_val_none f x).symm
    | some i => rfl
  right_inv x := by
    apply Subtype.ext
    exact Variety.principalOpenChartInclusion_lift f x.1 (x.2 ())

/-- Coordinatewise descent for a map regular on two coprime principal opens. -/
public lemma Variety.Morphism.exists_of_coprime_principalOpen_coordinates {V W : Variety k}
    (f g : Variety.PolynomialFunction V) (hfg : IsCoprime f g)
    (ψ : Variety.Point V → Variety.Point W)
    (hf : ∀ j, ∃ n : ℕ, ∃ p : Variety.PolynomialFunction V,
      ∀ x, f x ≠ 0 → f x ^ n * (ψ x).val j = p x)
    (hg : ∀ j, ∃ n : ℕ, ∃ p : Variety.PolynomialFunction V,
      ∀ x, g x ≠ 0 → g x ^ n * (ψ x).val j = p x) :
    ∃ F : Variety.Morphism V W, F.toFun = ψ := by
  refine ⟨⟨ψ, ?_⟩, rfl⟩
  intro j
  obtain ⟨p, hp⟩ := Variety.PolynomialFunction.exists_of_coprime_principalOpen
    f g hfg (fun x => (ψ x).val j) (hf j) (hg j)
  obtain ⟨q, hq⟩ := p.representedBy
  exact ⟨q, fun x => (hp x).trans (hq x)⟩

private lemma chart_coordinates {V W : Variety k} (f : MvPolynomial V.Coordinates k)
    (ψ : Variety.Point V → Variety.Point W)
    (F : Variety.Morphism (V.principalOpenChart f) W)
    (hF : ∀ x, F.toFun x = ψ ((V.principalOpenChartInclusion f).toFun x))
    (j : W.Coordinates) :
    ∃ n : ℕ, ∃ p : Variety.PolynomialFunction V,
      ∀ x, evalPolynomial x.val f ≠ 0 →
        evalPolynomial x.val f ^ n * (ψ x).val j = p x := by
  obtain ⟨p, hp⟩ := F.regular j
  obtain ⟨n, q, hq⟩ := clear_denominators f p
  refine ⟨n, Variety.PolynomialFunction.ofPolynomial V q, ?_⟩
  intro x hx
  have hFx := hF (V.principalOpenChartLift f x hx)
  rw [Variety.principalOpenChartInclusion_lift] at hFx
  rw [← hFx, hp]
  exact hq x.val hx

/-- Compatible regular factorizations of a prescribed point map through two
coprime principal-open charts give a global regular map with that point map. -/
public lemma Variety.Morphism.exists_of_coprime_principalOpen
    {V W : Variety k} (f g : MvPolynomial V.Coordinates k)
    (hfg : IsCoprime (Variety.PolynomialFunction.ofPolynomial V f)
      (Variety.PolynomialFunction.ofPolynomial V g))
    (ψ : Variety.Point V → Variety.Point W)
    (F : Variety.Morphism (V.principalOpenChart f) W)
    (G : Variety.Morphism (V.principalOpenChart g) W)
    (hF : ∀ x, F.toFun x = ψ ((V.principalOpenChartInclusion f).toFun x))
    (hG : ∀ x, G.toFun x = ψ ((V.principalOpenChartInclusion g).toFun x)) :
    ∃ Φ : Variety.Morphism V W, Φ.toFun = ψ := by
  apply Variety.Morphism.exists_of_coprime_principalOpen_coordinates _ _ hfg ψ
  · exact chart_coordinates f ψ F hF
  · exact chart_coordinates g ψ G hG

end Theory.AlgebraicGroup
