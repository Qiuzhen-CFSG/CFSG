module

public import Theory.AlgebraicGroup.Variety.PrincipalOpenDescent
public import Theory.AlgebraicGroup.Morphism.Reconstruction
public import Theory.AlgebraicGroup.Instance.SL

/-!
# Principal-open descent for SL₂

For `[[a,b],[c,d]]` in `SL₂`, the identity `d*a + (-b)*c = 1`
makes `a` and `c` coprime polynomial functions. Consequently regular maps on
the affine charts `a ≠ 0` and `c ≠ 0` which agree with a prescribed point map
descend to a global regular map. For a point-group homomorphism, reconstruction
upgrades this to an algebraic-group morphism with exactly that homomorphism.

The coordinate version accepts polynomial numerators divided by powers of
`a` and `c`; no global regularity or chart-cover premise is assumed. These
are the two elementary matrix charts used in SL₂ root-curve arguments.
The general principal-open construction and its source reference are in
`Variety.PrincipalOpenDescent`; the SL₂ specialization uses only `ad-bc=1`.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The first-column coordinate polynomial: row zero is `a`, row one is `c`. -/
@[expose]
public noncomputable def sl2FirstColumnPolynomial (i : Fin 2) :
    MvPolynomial (slVariety k 2).Coordinates k :=
  MvPolynomial.X (ULift.up (i, 0))

/-- Evaluation of a first-column coordinate polynomial. -/
@[simp] public lemma evalPolynomial_sl2FirstColumnPolynomial
    (x : (slVariety k 2).Coordinates → k) (i : Fin 2) :
    evalPolynomial x (sl2FirstColumnPolynomial i) = x (ULift.up (i, 0)) :=
  evalPolynomial_X x _

/-- The determinant-one identity is a Bézout identity for the first column. -/
public lemma sl2FirstColumn_isCoprime :
    IsCoprime (Variety.PolynomialFunction.ofPolynomial (slVariety k 2)
      (sl2FirstColumnPolynomial 0))
      (Variety.PolynomialFunction.ofPolynomial (slVariety k 2)
        (sl2FirstColumnPolynomial 1)) := by
  let E (i j : Fin 2) := Variety.PolynomialFunction.ofPolynomial (slVariety k 2)
    (MvPolynomial.X (ULift.up (i, j)))
  refine ⟨E 1 1, -E 0 1, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change E 1 1 x * evalPolynomial x.val (sl2FirstColumnPolynomial 0) +
    -(E 0 1 x) * evalPolynomial x.val (sl2FirstColumnPolynomial 1) = 1
  simp only [E, Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun,
    sl2FirstColumnPolynomial, evalPolynomial_X]
  have hdet := slPoint_det_eq_one 2 x
  rw [Matrix.det_fin_two] at hdet
  change x.val (ULift.up (0, 0)) * x.val (ULift.up (1, 1)) -
    x.val (ULift.up (0, 1)) * x.val (ULift.up (1, 0)) = 1 at hdet
  calc
    _ = x.val (ULift.up (0, 0)) * x.val (ULift.up (1, 1)) -
        x.val (ULift.up (0, 1)) * x.val (ULift.up (1, 0)) := by ring
    _ = 1 := hdet

/-- The two first-column principal opens cover all SL₂ points. -/
public lemma sl2FirstColumn_covers (x : Variety.Point (slVariety k 2)) :
    x.val (ULift.up (0, 0)) ≠ 0 ∨ x.val (ULift.up (1, 0)) ≠ 0 := by
  have hdet := slPoint_det_eq_one 2 x
  rw [Matrix.det_fin_two] at hdet
  change x.val (ULift.up (0, 0)) * x.val (ULift.up (1, 1)) -
    x.val (ULift.up (0, 1)) * x.val (ULift.up (1, 0)) = 1 at hdet
  by_cases ha : x.val (ULift.up (0, 0)) = 0
  · right
    intro hc
    simp [ha, hc] at hdet
  · exact Or.inl ha

/-- Compatible regular factorizations on the two first-column charts give a
regular map from SL₂ into any presented affine variety. -/
public lemma Variety.Morphism.exists_of_sl2_principalOpen {H : Variety k}
    (ψ : Variety.Point (slVariety k 2) → Variety.Point H)
    (Fa : Variety.Morphism ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 0)) H)
    (Fc : Variety.Morphism ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 1)) H)
    (ha : ∀ x, Fa.toFun x = ψ (((slVariety k 2).principalOpenChartInclusion
      (sl2FirstColumnPolynomial 0)).toFun x))
    (hc : ∀ x, Fc.toFun x = ψ (((slVariety k 2).principalOpenChartInclusion
      (sl2FirstColumnPolynomial 1)).toFun x)) :
    ∃ Φ : Variety.Morphism (slVariety k 2) H, Φ.toFun = ψ := by
  exact Variety.Morphism.exists_of_coprime_principalOpen
    (sl2FirstColumnPolynomial 0) (sl2FirstColumnPolynomial 1)
    sl2FirstColumn_isCoprime ψ Fa Fc ha hc

/-- A point-group homomorphism regular on the `a` and `c` charts is an
algebraic-group morphism, with the prescribed point homomorphism. -/
public lemma Morphism.exists_of_sl2_principalOpen {H : Variety k} [AlgebraicGroup H]
    (ψ : Variety.Point (slVariety k 2) →* Variety.Point H)
    (Fa : Variety.Morphism ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 0)) H)
    (Fc : Variety.Morphism ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 1)) H)
    (ha : ∀ x, Fa.toFun x = ψ (((slVariety k 2).principalOpenChartInclusion
      (sl2FirstColumnPolynomial 0)).toFun x))
    (hc : ∀ x, Fc.toFun x = ψ (((slVariety k 2).principalOpenChartInclusion
      (sl2FirstColumnPolynomial 1)).toFun x)) :
    ∃ Φ : AlgebraicGroup.Morphism (slVariety k 2) H, Φ.onPoints = ψ := by
  obtain ⟨F, hF⟩ := Variety.Morphism.exists_of_sl2_principalOpen ψ Fa Fc ha hc
  apply Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom ψ F.pullbackAlgHom
  intro p x
  change p (F.toFun x) = p (ψ x)
  rw [hF]

/-- Descent using explicit polynomial numerators over powers of `a` and `c`.
The exponents and numerators may depend on the target coordinate. -/
public lemma Morphism.exists_of_sl2_principalOpen_coordinates {H : Variety k} [AlgebraicGroup H]
    (ψ : Variety.Point (slVariety k 2) →* Variety.Point H)
    (ha : ∀ j, ∃ n : ℕ, ∃ p : MvPolynomial (slVariety k 2).Coordinates k,
      ∀ x, x.val (ULift.up (0, 0)) ≠ 0 →
        (ψ x).val j = evalPolynomial x.val p / x.val (ULift.up (0, 0)) ^ n)
    (hc : ∀ j, ∃ n : ℕ, ∃ p : MvPolynomial (slVariety k 2).Coordinates k,
      ∀ x, x.val (ULift.up (1, 0)) ≠ 0 →
        (ψ x).val j = evalPolynomial x.val p / x.val (ULift.up (1, 0)) ^ n) :
    ∃ Φ : AlgebraicGroup.Morphism (slVariety k 2) H, Φ.onPoints = ψ := by
  have local_regular (i : Fin 2)
      (hi : ∀ j, ∃ n : ℕ, ∃ p : MvPolynomial (slVariety k 2).Coordinates k,
        ∀ x, x.val (ULift.up (i, 0)) ≠ 0 →
          (ψ x).val j = evalPolynomial x.val p / x.val (ULift.up (i, 0)) ^ n) :
      ∀ j, ∃ n : ℕ, ∃ p : Variety.PolynomialFunction (slVariety k 2),
        ∀ x, (Variety.PolynomialFunction.ofPolynomial (slVariety k 2)
          (sl2FirstColumnPolynomial i)) x ≠ 0 →
        (Variety.PolynomialFunction.ofPolynomial (slVariety k 2)
          (sl2FirstColumnPolynomial i)) x ^ n * (ψ x).val j = p x := by
    intro j
    obtain ⟨n, p, hp⟩ := hi j
    refine ⟨n, Variety.PolynomialFunction.ofPolynomial (slVariety k 2) p, ?_⟩
    intro x hx
    simp only [Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun,
      sl2FirstColumnPolynomial, evalPolynomial_X] at hx ⊢
    rw [mul_comm]
    exact (eq_div_iff (pow_ne_zero n hx)).mp (hp x hx)
  obtain ⟨F, hF⟩ := Variety.Morphism.exists_of_coprime_principalOpen_coordinates
    _ _ sl2FirstColumn_isCoprime ψ (local_regular 0 ha) (local_regular 1 hc)
  apply Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom ψ F.pullbackAlgHom
  intro p x
  change p (F.toFun x) = p (ψ x)
  rw [hF]

end Theory.AlgebraicGroup
