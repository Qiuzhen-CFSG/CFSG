module

public import Theory.AlgebraicGroup.CoordinateRing.Basic

universe u

/-!
The identity law for right-translation pullback.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- Pullback by right multiplication by the identity fixes every polynomial
function. -/
public lemma rightMul_pullback_one
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    (AlgebraicGroup.rightMulMorphism G 1).pullbackAlgHom f = f := by
  apply Variety.PolynomialFunction.ext
  intro g
  change f (g * 1) = f g
  rw [mul_one]

end

/-!
Composition of right-translation pullbacks on polynomial functions.
-/

section

variable {k : Type u} [Field k]

/-- Pulling back successively by right multiplication by `h` and by `x` is
pullback by right multiplication by `x * h`. -/
public lemma rightMul_pullback_comp
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) (x h : Variety.Point G) :
    (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom
        ((AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom f) =
      (AlgebraicGroup.rightMulMorphism G (x * h)).pullbackAlgHom f := by
  apply Variety.PolynomialFunction.ext
  intro g
  change f ((g * x) * h) = f (g * (x * h))
  rw [mul_assoc]

end

/-!
Every polynomial function has all of its right translates in one finite
dimensional span, extracted from a finite pure-tensor expansion of its
coordinate comultiplication.
-/

section

open scoped TensorProduct

variable {k : Type u} [Field k]

/-- Concrete finite tensor data controlling every right translate of one
polynomial function. -/
public structure RightTranslateSpanData
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) where
  n : ℕ
  left : Fin n → Variety.PolynomialFunction G
  right : Fin n → Variety.PolynomialFunction G
  comultiplication_eq :
    AlgebraicGroup.coordinateComultiplication G f =
      ∑ i, left i ⊗ₜ[k] right i
  translate_eq : ∀ h : Variety.Point G,
    (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom f =
      ∑ i, (right i h) • left i

/-- A finite tensor expansion of `Δ(f)` simultaneously expresses every right
translate of `f` as a linear combination of the left tensor factors. -/
public lemma exists_finite_rightTranslate_span
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    Nonempty (RightTranslateSpanData G f) := by
  rcases TensorProduct.exists_sum_tmul_eq
      (AlgebraicGroup.coordinateComultiplication G f) with
    ⟨n, a, b, hcomul⟩
  refine ⟨⟨n, a, b, hcomul, ?_⟩⟩
  · intro h
    apply Variety.PolynomialFunction.ext
    intro g
    have heval := AlgebraicGroup.coordinateComultiplication_apply G f g h
    rw [hcomul] at heval
    change f (g * h) = (∑ i, (b i h) • a i) g
    have heval' : ∑ i, a i g * b i h = f (g * h) := by
      change polynomialFunctionEvalAddHom (Variety.prod G G)
          ((Variety.prodPointEquiv G G).symm (g, h))
          (polynomialFunctionTensor G G (∑ i, a i ⊗ₜ[k] b i)) =
        f (g * h) at heval
      simpa only [map_sum, polynomialFunctionTensor_tmul,
        polynomialFunctionEvalAddHom_apply,
        polynomialFunctionLeft_apply, polynomialFunctionRight_apply,
        polynomialFunction_mul_apply,
        Equiv.apply_symm_apply] using heval
    calc
      f (g * h) = ∑ i, a i g * b i h := heval'.symm
      _ = ∑ i, b i h * a i g := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      _ = (∑ i, (b i h) • a i) g := by
        change (∑ i, b i h * a i g) =
          polynomialFunctionEvalAddHom G g (∑ i, (b i h) • a i)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [polynomialFunctionEvalAddHom_apply,
          polynomialFunction_smul_apply]

end

/-!
The linear span of the right-translation orbit of a polynomial function.
-/

section

variable {k : Type u} [Field k]

/-- The `k`-linear span of all right translates of `f`. -/
@[expose]
public noncomputable def rightTranslateOrbitSpan
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    Submodule k (Variety.PolynomialFunction G) :=
  Submodule.span k (Set.range fun h : Variety.Point G ↦
    (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom f)

/-- The right-translation orbit span of one polynomial function is finitely
generated. -/
public lemma rightTranslateOrbitSpan_fg
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    (AlgebraicGroup.rightTranslateOrbitSpan G f).FG := by
  let data := Classical.choice
    (AlgebraicGroup.exists_finite_rightTranslate_span G f)
  let upper : Submodule k (Variety.PolynomialFunction G) :=
    Submodule.span k (Set.range data.left)
  have hupper : upper.FG :=
    Submodule.fg_span (Set.finite_range data.left)
  apply hupper.of_le
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨h, rfl⟩
  change (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom f ∈ upper
  rw [data.translate_eq h]
  apply Submodule.sum_mem
  intro i hi
  exact upper.smul_mem (data.right i h) (Submodule.subset_span ⟨i, rfl⟩)

/-- The right-translation orbit span is a finite-dimensional `k`-vector
space. -/
public noncomputable instance rightTranslateOrbitSpan_moduleFinite
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    Module.Finite k (AlgebraicGroup.rightTranslateOrbitSpan G f) :=
  Module.Finite.of_fg_top
    ((Submodule.fg_top (AlgebraicGroup.rightTranslateOrbitSpan G f)).mpr
      (AlgebraicGroup.rightTranslateOrbitSpan_fg G f))

end

/-!
Right-translation stability of the finite orbit span.
-/

section

variable {k : Type u} [Field k]

/-- The finite orbit span is stable under every right translation. -/
public lemma rightTranslateOrbitSpan_stable
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) (x : Variety.Point G) :
    ∀ q ∈ AlgebraicGroup.rightTranslateOrbitSpan G f,
      (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom q ∈
        AlgebraicGroup.rightTranslateOrbitSpan G f := by
  intro q hq
  apply Submodule.span_induction (p := fun q _ ↦
    (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom q ∈
      AlgebraicGroup.rightTranslateOrbitSpan G f) ?_ ?_ ?_ ?_ hq
  · intro q hgenerator
    rcases hgenerator with ⟨h, rfl⟩
    rw [AlgebraicGroup.rightMul_pullback_comp]
    exact Submodule.subset_span ⟨x * h, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb hta htb
    rw [map_add]
    exact Submodule.add_mem _ hta htb
  · intro r a ha hta
    rw [map_smul]
    exact Submodule.smul_mem _ r hta

end

end Theory.AlgebraicGroup
