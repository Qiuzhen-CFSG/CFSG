module

public import Theory.AlgebraicGroup.Irreducible.Basic
public import Theory.AlgebraicGroup.Jordan.Basic
public import Theory.AlgebraicGroup.Representations.Semisimple
public import Theory.AlgebraicGroup.Tori.Basic

universe u

/-! Laurent exponents associated to monomials on diagonal algebraic groups. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The integral Laurent exponent represented by a monomial in the entry and
inverse-entry coordinates of `D_n`. -/
@[expose]
public def dMonomialExponent (n : ℕ)
    (s : (dVariety k n).Coordinates →₀ ℕ) : Fin n → ℤ :=
  fun i ↦ (s (Sum.inl (ULift.up i)) : ℤ) -
    (s (Sum.inr (ULift.up i)) : ℤ)

/-- Aggregate the coefficients of a coordinate polynomial on `D_n` by the
Laurent exponent represented by each coordinate monomial. -/
@[expose]
public noncomputable def dLaurentCoefficients (n : ℕ)
    (p : MvPolynomial (dVariety k n).Coordinates k) :
    (Fin n → ℤ) →₀ k :=
  (AddMonoidAlgebra.coeff p).mapDomain (dMonomialExponent n)

/-- A coordinate monomial on `D_n` evaluates as the Laurent monomial whose
exponent is its entry exponent minus its inverse-entry exponent. -/
public lemma dMonomial_value_eq_laurent
    (n : ℕ)
    (s : (dVariety k n).Coordinates →₀ ℕ)
    (x : Variety.Point (dVariety k n)) :
    s.prod (fun c e ↦ x.val c ^ e) =
      ((↑(∏ i, (dPointEquiv n x i) ^ dMonomialExponent n s i) : k)) := by
  classical
  rw [Finsupp.prod_fintype]
  · rw [Fintype.prod_sum_type]
    have hentry :
        (∏ a : ULift.{u} (Fin n), x.val (Sum.inl a) ^ s (Sum.inl a)) =
          ∏ i : Fin n, x.val (Sum.inl (ULift.up i)) ^
            s (Sum.inl (ULift.up i)) := by
      apply Fintype.prod_equiv Equiv.ulift
      intro a
      rfl
    have hinv :
        (∏ a : ULift.{u} (Fin n), x.val (Sum.inr a) ^ s (Sum.inr a)) =
          ∏ i : Fin n, x.val (Sum.inr (ULift.up i)) ^
            s (Sum.inr (ULift.up i)) := by
      apply Fintype.prod_equiv Equiv.ulift
      intro a
      rfl
    rw [hentry, hinv]
    simp only [dMonomialExponent]
    push_cast
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    change (↑(dPointEquiv n x i) : k) ^ s (Sum.inl (ULift.up i)) *
        dPointEntryInv n x i ^ s (Sum.inr (ULift.up i)) =
      (↑(dPointEquiv n x i) : k) ^
        ((s (Sum.inl (ULift.up i)) : ℤ) -
          (s (Sum.inr (ULift.up i)) : ℤ))
    rw [← dPoint_unit_inv]
    simp [zpow_sub₀, zpow_natCast, div_eq_mul_inv]
    rfl
  · intro c
    simp

private lemma rightTranslationPullback_dMonomial
    (n : ℕ) (t : Variety.Point (dVariety k n))
    (s : (dVariety k n).Coordinates →₀ ℕ) :
    rightTranslationPullback (dVariety k n) t
        (Variety.PolynomialFunction.ofPolynomial (dVariety k n)
          (MvPolynomial.monomial s 1)) =
      (s.prod fun c e ↦ t.val c ^ e) •
        Variety.PolynomialFunction.ofPolynomial (dVariety k n)
          (MvPolynomial.monomial s 1) := by
  apply Variety.PolynomialFunction.ext
  intro x
  rw [rightTranslationPullback_apply, polynomialFunction_smul_apply]
  simp only [Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial,
    MvPolynomial.eval₂_monomial, RingHom.id_apply, one_mul]
  simp_rw [dPoint_mul_apply, mul_pow]
  rw [Finsupp.prod_mul]
  exact mul_comm _ _

/-- Every rational point of `D_n` is semisimple. -/
public theorem dVariety_all_semisimple (n : ℕ) :
    ∀ t : Variety.Point (dVariety k n),
      IsSemisimpleElement (dVariety k n) t := by
  intro t
  let T : Module.End k (Variety.PolynomialFunction (dVariety k n)) :=
    rightTranslationPullback (dVariety k n) t
  change Module.End.IsFinitelySemisimple T
  intro P hP hfinite
  let : Module.Finite k P := hfinite
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := k) (M := P)
  choose p hp using fun i ↦ (b i).val.representedBy
  classical
  let supports : Finset ((dVariety k n).Coordinates →₀ ℕ) :=
    Finset.univ.biUnion fun i : Fin m ↦ (p i).support
  let v : supports → Variety.PolynomialFunction (dVariety k n) :=
    fun d ↦ Variety.PolynomialFunction.ofPolynomial (dVariety k n)
      (MvPolynomial.monomial d.1 1)
  let μ : supports → k := fun d ↦ d.1.prod fun c e ↦ t.val c ^ e
  have hv (d : supports) : T (v d) = μ d • v d := by
    simpa [T, v, μ] using rightTranslationPullback_dMonomial n t d.1
  let W := Submodule.span k (Set.range v)
  have hbW (i : Fin m) : (b i).val ∈ W := by
    have hbpoly : (b i).val =
        Variety.PolynomialFunction.ofPolynomial (dVariety k n) (p i) := by
      apply Variety.PolynomialFunction.ext
      intro x
      exact hp i x
    rw [hbpoly]
    change evaluationAlgHom (dVariety k n) (p i) ∈ W
    rw [polynomial_eq_sum_monomial _ (p i) supports]
    · simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro d hd
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨d, hd⟩, rfl⟩
    · intro d hd
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hd⟩
  have hspan : P ≤ W := by
    let Q : Submodule k P := W.comap P.subtype
    have hQtop : Q = ⊤ := by
      apply top_unique
      rw [← hb, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbW i
    intro x hx
    change P.subtype ⟨x, hx⟩ ∈ W
    change ⟨x, hx⟩ ∈ Q
    rw [hQtop]
    exact Submodule.mem_top
  exact Module.End.isSemisimple_restrict_of_le_span_eigenvectors
    T P hP v μ hv hspan

end Theory.AlgebraicGroup
