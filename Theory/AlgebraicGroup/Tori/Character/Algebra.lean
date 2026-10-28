module

public import Theory.AlgebraicGroup.RightTranslation.Semisimple
public import Theory.AlgebraicGroup.Tori.Character.Operations

universe u

/-! The character-group algebra and scalar regular characters. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Scalar regular functions form a monoid homomorphism from the character
group. -/
@[expose]
public noncomputable def TorusCharacter.scalarPolynomialFunctionMonoidHom
    (T : Variety k) [AlgebraicGroup T] :
    TorusCharacter T →* Variety.PolynomialFunction T where
  toFun := TorusCharacter.scalarPolynomialFunction
  map_one' := by
    apply Variety.PolynomialFunction.ext
    intro x
    rw [TorusCharacter.scalarPolynomialFunction_apply]
    change ((dPointEquiv 1
      ((1 : TorusCharacter T).toVariety.toFun x) 0 : k)) = 1
    rfl
  map_mul' := by
    intro χ ψ
    apply Variety.PolynomialFunction.ext
    intro x
    rw [TorusCharacter.scalarPolynomialFunction_apply]
    change (χ * ψ).pointCharacter x =
      χ.scalarPolynomialFunction x * ψ.scalarPolynomialFunction x
    rw [TorusCharacter.scalarPolynomialFunction_apply,
      TorusCharacter.scalarPolynomialFunction_apply]
    change ((dPointEquiv 1
      ((χ * ψ).toVariety.toFun x) 0 : k)) =
      (dPointEquiv 1 (χ.toVariety.toFun x) 0 : k) *
        (dPointEquiv 1 (ψ.toVariety.toFun x) 0 : k)
    rfl

/-- Distinct algebraic characters have linearly independent scalar regular
functions. -/
public theorem torusCharacter_scalarPolynomialFunction_linearIndependent
    (T : Variety k) [AlgebraicGroup T] :
    LinearIndependent k
      (TorusCharacter.scalarPolynomialFunction (T := T)) := by
  let coeLinear : Variety.PolynomialFunction T →ₗ[k]
      (Variety.Point T → k) :=
    { toFun := fun f => f
      map_add' := by
        intro f g
        funext x
        rfl
      map_smul' := by
        intro c f
        funext x
        rw [Pi.smul_apply, polynomialFunction_smul_apply]
        rfl }
  apply LinearIndependent.of_comp coeLinear
  have hLI :=
    (linearIndependent_monoidHom (Variety.Point T) k).comp
      (TorusCharacter.pointCharacter (T := T))
      TorusCharacter.pointCharacter_injective
  have heq :
      (coeLinear ∘ TorusCharacter.scalarPolynomialFunction (T := T)) =
        ((fun f : Variety.Point T →* k => (f : Variety.Point T → k)) ∘
          TorusCharacter.pointCharacter (T := T)) := by
    funext χ x
    change (TorusCharacter.scalarPolynomialFunction χ) x =
      (TorusCharacter.pointCharacter χ x : k)
    rw [TorusCharacter.scalarPolynomialFunction_apply]
  rw [heq]
  exact hLI

private lemma commonEigenvector_eq_smul_scalarPolynomialFunction
    (T : Variety k) [AlgebraicGroup T]
    (φ : Variety.PolynomialFunction T) (μ : Variety.Point T → k)
    (hφ : ∀ g, rightTranslationPullback T g φ = μ g • φ) :
    φ = 0 ∨ ∃ χ : TorusCharacter T,
      φ = φ 1 • χ.scalarPolynomialFunction := by
  by_cases hzero : φ = 0
  · exact Or.inl hzero
  right
  have hc : φ 1 ≠ 0 := by
    intro hc
    apply hzero
    apply Variety.PolynomialFunction.ext
    intro g
    have heval := congrArg (fun q : Variety.PolynomialFunction T => q 1) (hφ g)
    rw [rightTranslationPullback_apply] at heval
    simpa [hc] using heval
  let q : Variety.PolynomialFunction T := (φ 1)⁻¹ • φ
  have hq_one : q 1 = 1 := by simp [q, hc]
  have hq_mul (x y : Variety.Point T) : q (x * y) = q x * q y := by
    have hxy : φ (x * y) = μ y * φ x := by
      have h := congrArg (fun a : Variety.PolynomialFunction T => a x) (hφ y)
      rw [rightTranslationPullback_apply] at h
      simpa only [polynomialFunction_smul_apply, smul_eq_mul] using h
    have hy : φ y = μ y * φ 1 := by
      have h := congrArg (fun a : Variety.PolynomialFunction T => a 1) (hφ y)
      rw [rightTranslationPullback_apply] at h
      simpa only [one_mul, polynomialFunction_smul_apply, smul_eq_mul] using h
    simp only [q, polynomialFunction_smul_apply]
    rw [hxy, hy]
    field_simp
  let point (x : Variety.Point T) : Variety.Point (KMult k) :=
    (dPointEquiv 1).symm (fun _ =>
      { val := q x
        inv := q x⁻¹
        val_inv := by rw [← hq_mul, mul_inv_cancel, hq_one]
        inv_val := by rw [← hq_mul, inv_mul_cancel, hq_one] })
  let qInv : Variety.PolynomialFunction T :=
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism T) q
  let m : Variety.Morphism T (KMult k) :=
    { toFun := point
      regular := by
        intro c
        cases c with
        | inl i =>
            obtain ⟨p, hp⟩ := q.representedBy
            exact ⟨p, by
              intro x
              change q x = evalPolynomial x.val p
              exact hp x⟩
        | inr i =>
            obtain ⟨p, hp⟩ := qInv.representedBy
            exact ⟨p, by
              intro x
              change q x⁻¹ = evalPolynomial x.val p
              exact hp x⟩ }
  let χ : TorusCharacter T :=
    { toVariety := m
      map_one := by
        change point 1 = 1
        apply (dPointEquiv 1).injective
        rw [dPointEquiv_one]
        rw [show dPointEquiv 1 (point 1) = (fun _ : Fin 1 =>
            { val := q 1
              inv := q (1 : Variety.Point T)⁻¹
              val_inv := by rw [← hq_mul, mul_inv_cancel, hq_one]
              inv_val := by rw [← hq_mul, inv_mul_cancel, hq_one] }) by
          exact Equiv.apply_symm_apply (dPointEquiv 1) _]
        funext i
        apply Units.ext
        exact hq_one
      map_mul := by
        intro x y
        change point (x * y) = point x * point y
        apply (dPointEquiv 1).injective
        rw [dPointEquiv_mul]
        simp only [point, Equiv.apply_symm_apply]
        funext i
        apply Units.ext
        exact hq_mul x y }
  refine ⟨χ, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  rw [polynomialFunction_smul_apply,
    TorusCharacter.scalarPolynomialFunction_apply]
  change φ x = φ 1 * q x
  simp [q, hc]

/-- Every regular function on a commutative algebraic group of semisimple
points lies in the span of its scalar algebraic characters. -/
public theorem polynomialFunction_mem_span_scalarCharacters
    [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t)
    (f : Variety.PolynomialFunction T) :
    f ∈ Submodule.span k
      (Set.range fun χ : TorusCharacter T => χ.scalarPolynomialFunction) := by
  obtain ⟨v, hv, hsum⟩ :=
    exists_rightTranslateOrbitSpan_commonEigen_decomposition T hcomm hsemi f
  rw [← hsum]
  classical
  change (∑ μ ∈ v.support,
      ((v μ : rightTranslateOrbitSpan T f) :
        Variety.PolynomialFunction T)) ∈ _
  apply Submodule.sum_mem
  intro μ hμ
  rcases commonEigenvector_eq_smul_scalarPolynomialFunction T
      ((v μ : rightTranslateOrbitSpan T f) : Variety.PolynomialFunction T)
      μ (hv μ) with hzero | ⟨χ, hχ⟩
  · rw [hzero]
    exact Submodule.zero_mem _
  · rw [hχ]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self χ))

/-- Scalar regular functions identify the character-group algebra with the
full polynomial-function algebra. -/
@[expose]
public noncomputable def torusCharacterAlgebraEquiv
    [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t) :
    MonoidAlgebra k (TorusCharacter T) ≃ₐ[k]
      Variety.PolynomialFunction T := by
  letI : Semiring k :=
    (inferInstance : CommRing k).toCommSemiring.toSemiring
  have hscalar (χ : TorusCharacter T) :
      TorusCharacter.scalarPolynomialFunctionMonoidHom T χ =
        χ.scalarPolynomialFunction := by
    change TorusCharacter.scalarPolynomialFunction χ =
      χ.scalarPolynomialFunction
    rfl
  have hLIpoint :=
    (linearIndependent_monoidHom (Variety.Point T) k).comp
      (TorusCharacter.pointCharacter (T := T))
      TorusCharacter.pointCharacter_injective
  have hlininj :=
    linearIndependent_iff_injective_finsuppLinearCombination.mp hLIpoint
  have heinj : ∀ ⦃a b : MonoidAlgebra k (TorusCharacter T)⦄,
      ((MonoidAlgebra.lift k (Variety.PolynomialFunction T) (TorusCharacter T))
        (TorusCharacter.scalarPolynomialFunctionMonoidHom T)) a =
      ((MonoidAlgebra.lift k (Variety.PolynomialFunction T) (TorusCharacter T))
        (TorusCharacter.scalarPolynomialFunctionMonoidHom T)) b → a = b := by
    intro a b hab
    apply MonoidAlgebra.coeff_injective
    apply hlininj
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
    ext x
    let ev : (Variety.Point T → k) →ₗ[k] k :=
      { toFun := fun f => f x
        map_add' := by
          intro f g
          rfl
        map_smul' := by
          intro c f
          rfl }
    have hev (f : Variety.Point T → k) : ev f = f x := rfl
    have hx := congrArg (polynomialFunctionEvalAddHom T x) hab
    change ev (a.coeff.sum
      (fun i c => c • (((fun f : Variety.Point T →* k =>
        (f : Variety.Point T → k)) ∘
          TorusCharacter.pointCharacter) i))) =
      ev (b.coeff.sum
        (fun i c => c • (((fun f : Variety.Point T →* k =>
          (f : Variety.Point T → k)) ∘
            TorusCharacter.pointCharacter) i)))
    simp only [MonoidAlgebra.lift_apply, hscalar] at hx
    rw [map_finsuppSum, map_finsuppSum] at hx
    simp only [polynomialFunctionEvalAddHom_apply,
      TorusCharacter.scalarPolynomialFunction_apply,
      polynomialFunction_smul_apply] at hx
    rw [map_finsuppSum, map_finsuppSum]
    simp_rw [LinearMap.map_smul]
    simpa only [hev, Function.comp_apply, smul_eq_mul] using hx
  have hesurj : ∀ f : Variety.PolynomialFunction T, ∃ a : MonoidAlgebra k (TorusCharacter T),
      ((MonoidAlgebra.lift k (Variety.PolynomialFunction T) (TorusCharacter T))
        (TorusCharacter.scalarPolynomialFunctionMonoidHom T)) a = f := by
    intro f
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
      (polynomialFunction_mem_span_scalarCharacters T hcomm hsemi f)
    refine ⟨MonoidAlgebra.ofCoeff c, ?_⟩
    simpa only [MonoidAlgebra.lift_apply,
      MonoidAlgebra.coeff_ofCoeff, hscalar] using hc
  apply AlgEquiv.ofBijective
  constructor
  · intro a b hab
    exact heinj hab
  · intro f
    exact hesurj f

private lemma torusCharacterAlgebraEquiv_single
    [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t)
    (χ : TorusCharacter T) (r : k) :
      torusCharacterAlgebraEquiv T hcomm hsemi
        (MonoidAlgebra.single χ r) =
      r • χ.scalarPolynomialFunction := by
  change
    ((MonoidAlgebra.lift k (Variety.PolynomialFunction T) (TorusCharacter T))
      (TorusCharacter.scalarPolynomialFunctionMonoidHom T))
      (MonoidAlgebra.single χ r) = _
  rw [MonoidAlgebra.lift_single]
  rfl

/-- The character-group-algebra presentation is contravariantly natural. -/
public theorem torusCharacterAlgebraEquiv_naturality
    [IsAlgClosed k]
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hcommG : IsMulCommutative (Variety.Point G))
    (hsemiG : ∀ g : Variety.Point G, IsSemisimpleElement G g)
    (hcommH : IsMulCommutative (Variety.Point H))
    (hsemiH : ∀ h : Variety.Point H, IsSemisimpleElement H h)
    (f : AlgebraicGroup.Morphism G H) :
    f.toVariety.pullbackAlgHom.comp
        (torusCharacterAlgebraEquiv H hcommH hsemiH).toAlgHom =
      (torusCharacterAlgebraEquiv G hcommG hsemiG).toAlgHom.comp
        (MonoidAlgebra.mapDomainAlgHom k k (TorusCharacter.pullback f)) := by
  apply MonoidAlgebra.algHom_ext
  · intro χ
    calc
      f.toVariety.pullbackAlgHom
          ((torusCharacterAlgebraEquiv H hcommH hsemiH)
            (MonoidAlgebra.single χ 1)) =
          f.toVariety.pullbackAlgHom
            ((1 : k) • χ.scalarPolynomialFunction) :=
        congrArg f.toVariety.pullbackAlgHom
          (torusCharacterAlgebraEquiv_single H hcommH hsemiH χ 1)
      _ = (TorusCharacter.pullback f χ).scalarPolynomialFunction := by
        simp only [one_smul]
        exact TorusCharacter.pullback_scalarPolynomialFunction f χ
      _ = (torusCharacterAlgebraEquiv G hcommG hsemiG)
          (MonoidAlgebra.single (TorusCharacter.pullback f χ) 1) := by
        rw [torusCharacterAlgebraEquiv_single, one_smul]
      _ = (torusCharacterAlgebraEquiv G hcommG hsemiG)
          ((MonoidAlgebra.mapDomainAlgHom k k (TorusCharacter.pullback f))
            (MonoidAlgebra.single χ 1)) := by simp
  · apply AlgHom.ext
    intro r
    exact ((f.toVariety.pullbackAlgHom.comp
      (torusCharacterAlgebraEquiv H hcommH hsemiH).toAlgHom).commutes r).trans
      (((torusCharacterAlgebraEquiv G hcommG hsemiG).toAlgHom.comp
        (MonoidAlgebra.mapDomainAlgHom k k
          (TorusCharacter.pullback f))).commutes r).symm

end Theory.AlgebraicGroup

