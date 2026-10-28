module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Theory.AlgebraicGroup.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Point

universe u

/-!
Finite radical presentations of reduced finite-type algebras and the
algebraic groups obtained from Hopf algebra structures on them.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

/-- A finite radical polynomial presentation of an algebra. -/
public structure ReducedFiniteTypeAlgebraPresentation
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] where
  Coordinates : Type u
  finiteCoordinates : Finite Coordinates
  relations : Ideal (MvPolynomial Coordinates k)
  equiv : (MvPolynomial Coordinates k ⧸ relations) ≃ₐ[k] A
  relations_fg : relations.FG
  relations_isRadical : relations.IsRadical

/-- The affine zero locus attached to a finite radical presentation. -/
@[expose]
public def ReducedFiniteTypeAlgebraPresentation.toVariety
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (P : ReducedFiniteTypeAlgebraPresentation k A) : Variety k where
  Coordinates := P.Coordinates
  finiteCoordinates := P.finiteCoordinates
  equations := P.relations

section AlgebraPresentation

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]

public lemma ReducedFiniteTypeAlgebraPresentation.vanishingIdeal_univ
    (P : ReducedFiniteTypeAlgebraPresentation k A) :
    vanishingIdeal (Set.univ : Set (Variety.Point P.toVariety)) = P.relations := by
  let : Finite P.Coordinates := P.finiteCoordinates
  ext p
  constructor
  · intro hp
    have hp' : p ∈ MvPolynomial.vanishingIdeal k
        (MvPolynomial.zeroLocus k P.relations) := by
      intro x hx
      let y : Variety.Point P.toVariety := ⟨x, by
        intro q hq
        convert hx q hq using 1
        all_goals rfl⟩
      convert hp y (Set.mem_univ y) using 1
      all_goals rfl
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical,
      P.relations_isRadical.radical] at hp'
    exact hp'
  · intro hp x _
    exact x.isZero p hp

public noncomputable def ReducedFiniteTypeAlgebraPresentation.coordinateRingAlgEquiv
    (P : ReducedFiniteTypeAlgebraPresentation k A) :
    coordinateRing P.toVariety ≃ₐ[k] A := by
  change (MvPolynomial P.Coordinates k ⧸
      vanishingIdeal (Set.univ : Set (Variety.Point P.toVariety))) ≃ₐ[k] A
  rw [P.vanishingIdeal_univ]
  exact P.equiv

public noncomputable def ReducedFiniteTypeAlgebraPresentation.polynomialFunctionAlgEquiv
    (P : ReducedFiniteTypeAlgebraPresentation k A) :
    A ≃ₐ[k] Variety.PolynomialFunction P.toVariety :=
  P.coordinateRingAlgEquiv.symm.trans
    (coordinateRingAlgEquivPolynomialFunction P.toVariety)

@[expose]
public noncomputable def ReducedFiniteTypeAlgebraPresentation.pointCharacterEquiv
    (P : ReducedFiniteTypeAlgebraPresentation k A) :
    Variety.Point P.toVariety ≃ WithConv (A →ₐ[k] k) where
  toFun := fun x => WithConv.toConv <|
    (polynomialFunctionPointAlgHom P.toVariety x).comp
      P.polynomialFunctionAlgEquiv.toAlgHom
  invFun := fun φ => (polynomialFunctionPointAlgHomEquiv P.toVariety).symm <|
    φ.ofConv.comp P.polynomialFunctionAlgEquiv.symm.toAlgHom
  left_inv := by
    intro x
    apply (polynomialFunctionPointAlgHomEquiv P.toVariety).injective
    change (polynomialFunctionPointAlgHomEquiv P.toVariety)
        ((polynomialFunctionPointAlgHomEquiv P.toVariety).symm
          (((polynomialFunctionPointAlgHomEquiv P.toVariety) x).comp
            P.polynomialFunctionAlgEquiv.toAlgHom |>.comp
              P.polynomialFunctionAlgEquiv.symm.toAlgHom)) =
      (polynomialFunctionPointAlgHomEquiv P.toVariety) x
    rw [(polynomialFunctionPointAlgHomEquiv P.toVariety).apply_symm_apply]
    apply AlgHom.ext
    intro f
    simp
  right_inv := by
    intro φ
    apply WithConv.ofConv_injective
    change ((polynomialFunctionPointAlgHomEquiv P.toVariety)
        ((polynomialFunctionPointAlgHomEquiv P.toVariety).symm
          (φ.ofConv.comp P.polynomialFunctionAlgEquiv.symm.toAlgHom))).comp
          P.polynomialFunctionAlgEquiv.toAlgHom = φ.ofConv
    rw [(polynomialFunctionPointAlgHomEquiv P.toVariety).apply_symm_apply]
    apply AlgHom.ext
    intro a
    simp

end AlgebraPresentation

section HopfPresentation

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
  [HopfAlgebra k A]

@[expose, implicit_reducible]
public noncomputable def ReducedFiniteTypeAlgebraPresentation.pointGroup
    (P : ReducedFiniteTypeAlgebraPresentation k A) :
    Group (Variety.Point P.toVariety) :=
  P.pointCharacterEquiv.group

public noncomputable def ReducedFiniteTypeAlgebraPresentation.coordinateElement
    (P : ReducedFiniteTypeAlgebraPresentation k A) (i : P.Coordinates) : A :=
  P.polynomialFunctionAlgEquiv.symm
    (Variety.PolynomialFunction.ofPolynomial P.toVariety (MvPolynomial.X i))

public noncomputable def ReducedFiniteTypeAlgebraPresentation.mulCoordinateFunction
    (P : ReducedFiniteTypeAlgebraPresentation k A) (i : P.Coordinates) :
    Variety.PolynomialFunction (Variety.prod P.toVariety P.toVariety) :=
  polynomialFunction_prod_algEquiv P.toVariety P.toVariety
    (TensorProduct.map P.polynomialFunctionAlgEquiv.toLinearMap
      P.polynomialFunctionAlgEquiv.toLinearMap
      (Coalgebra.comul (P.coordinateElement i)))

public noncomputable def ReducedFiniteTypeAlgebraPresentation.invCoordinateFunction
    (P : ReducedFiniteTypeAlgebraPresentation k A) (i : P.Coordinates) :
    Variety.PolynomialFunction P.toVariety :=
  P.polynomialFunctionAlgEquiv
    (HopfAlgebra.antipode k (P.coordinateElement i))

public noncomputable def ReducedFiniteTypeAlgebraPresentation.mulPolynomial
    (P : ReducedFiniteTypeAlgebraPresentation k A) (i : P.Coordinates) :
    MvPolynomial (P.Coordinates ⊕ P.Coordinates) k :=
  Classical.choose (P.mulCoordinateFunction i).representedBy

public noncomputable def ReducedFiniteTypeAlgebraPresentation.invPolynomial
    (P : ReducedFiniteTypeAlgebraPresentation k A) (i : P.Coordinates) :
    MvPolynomial P.Coordinates k :=
  Classical.choose (P.invCoordinateFunction i).representedBy

omit [IsAlgClosed k] in
public lemma polynomialFunction_prod_algEquiv_apply
    (V W : Variety k)
    (t : Variety.PolynomialFunction V ⊗[k] Variety.PolynomialFunction W)
    (x : Variety.Point V) (y : Variety.Point W) :
    polynomialFunction_prod_algEquiv V W t
        ((Variety.prodPointEquiv V W).symm (x, y)) =
      Algebra.TensorProduct.lift
        (polynomialFunctionPointAlgHom V x)
        (polynomialFunctionPointAlgHom W y)
        (fun _ _ => Commute.all _ _) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add]
      simp only [Variety.PolynomialFunction.toFun, Subring.coe_add, Pi.add_apply]
      exact congrArg₂ (· + ·) ha hb
  | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul]
      change polynomialFunctionTensor V W (a ⊗ₜ[k] b)
          ((Variety.prodPointEquiv V W).symm (x, y)) = _
      rw [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
        polynomialFunctionLeft_apply, polynomialFunctionRight_apply]
      simp

public lemma ReducedFiniteTypeAlgebraPresentation.pointCharacterEquiv_coordinateElement
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (x : Variety.Point P.toVariety) (i : P.Coordinates) :
    P.pointCharacterEquiv x (P.coordinateElement i) = x.val i := by
  change polynomialFunctionPointAlgHom P.toVariety x
      (P.polynomialFunctionAlgEquiv
        (P.polynomialFunctionAlgEquiv.symm
          (Variety.PolynomialFunction.ofPolynomial P.toVariety
            (MvPolynomial.X i)))) = x.val i
  rw [P.polynomialFunctionAlgEquiv.apply_symm_apply]
  simp only [polynomialFunctionPointAlgHom_apply]
  unfold Variety.PolynomialFunction.ofPolynomial
    Variety.PolynomialFunction.toFun evalPolynomial
  exact MvPolynomial.eval_X i

public lemma ReducedFiniteTypeAlgebraPresentation.pointCharacterEquiv_mul
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (x y : Variety.Point P.toVariety) :
    P.pointCharacterEquiv
        (@Mul.mul (Variety.Point P.toVariety) P.pointGroup.toMul x y) =
      P.pointCharacterEquiv x * P.pointCharacterEquiv y :=
  P.pointCharacterEquiv.apply_symm_apply _

public lemma ReducedFiniteTypeAlgebraPresentation.mulCoordinateFunction_apply
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (x y : Variety.Point P.toVariety) (i : P.Coordinates) :
    P.mulCoordinateFunction i
        ((Variety.prodPointEquiv P.toVariety P.toVariety).symm (x, y)) =
      (@Mul.mul (Variety.Point P.toVariety) P.pointGroup.toMul x y).val i := by
  rw [← P.pointCharacterEquiv_coordinateElement
    (@Mul.mul (Variety.Point P.toVariety) P.pointGroup.toMul x y) i]
  rw [P.pointCharacterEquiv_mul, AlgHom.convMul_apply]
  unfold ReducedFiniteTypeAlgebraPresentation.mulCoordinateFunction
  rw [polynomialFunction_prod_algEquiv_apply]
  have hmap (t : A ⊗[k] A) :
      Algebra.TensorProduct.lift
          (polynomialFunctionPointAlgHom P.toVariety x)
          (polynomialFunctionPointAlgHom P.toVariety y)
          (fun _ _ => Commute.all _ _)
          (TensorProduct.map
            P.polynomialFunctionAlgEquiv.toLinearMap
            P.polynomialFunctionAlgEquiv.toLinearMap t) =
        Algebra.TensorProduct.lift
          (P.pointCharacterEquiv x).ofConv
          (P.pointCharacterEquiv y).ofConv
          (fun _ _ => Commute.all _ _) t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add]; rw [ha, hb]
    | tmul a b =>
        rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
          Algebra.TensorProduct.lift_tmul]
        rfl
  exact hmap (Coalgebra.comul (R := k) (P.coordinateElement i))

public lemma ReducedFiniteTypeAlgebraPresentation.pointCharacterEquiv_inv
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (x : Variety.Point P.toVariety) :
    P.pointCharacterEquiv
        (@Inv.inv (Variety.Point P.toVariety) P.pointGroup.toInv x) =
      (P.pointCharacterEquiv x)⁻¹ :=
  P.pointCharacterEquiv.apply_symm_apply _

public lemma ReducedFiniteTypeAlgebraPresentation.invCoordinateFunction_apply
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (x : Variety.Point P.toVariety) (i : P.Coordinates) :
    P.invCoordinateFunction i x =
      (@Inv.inv (Variety.Point P.toVariety) P.pointGroup.toInv x).val i := by
  rw [← P.pointCharacterEquiv_coordinateElement
    (@Inv.inv (Variety.Point P.toVariety) P.pointGroup.toInv x) i]
  rw [P.pointCharacterEquiv_inv]
  rfl

public lemma ReducedFiniteTypeAlgebraPresentation.mulPolynomial_spec
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (i : P.Coordinates) (x y : Variety.Point P.toVariety) :
    (@Mul.mul (Variety.Point P.toVariety) P.pointGroup.toMul x y).val i =
      evalPolynomial (Sum.elim x.val y.val) (P.mulPolynomial i) := by
  rw [← P.mulCoordinateFunction_apply]
  exact Classical.choose_spec (P.mulCoordinateFunction i).representedBy
    ((Variety.prodPointEquiv P.toVariety P.toVariety).symm (x, y))

public lemma ReducedFiniteTypeAlgebraPresentation.invPolynomial_spec
    (P : ReducedFiniteTypeAlgebraPresentation k A)
    (i : P.Coordinates) (x : Variety.Point P.toVariety) :
    (@Inv.inv (Variety.Point P.toVariety) P.pointGroup.toInv x).val i =
      evalPolynomial x.val (P.invPolynomial i) := by
  rw [← P.invCoordinateFunction_apply]
  exact Classical.choose_spec (P.invCoordinateFunction i).representedBy x

/-- A reduced finite-type Hopf presentation determines an algebraic group. -/
@[expose, reducible]
public noncomputable def ReducedFiniteTypeAlgebraPresentation.algebraicGroup
    (P : ReducedFiniteTypeAlgebraPresentation k A) :
    AlgebraicGroup P.toVariety where
  toGroup := P.pointGroup
  mulPolynomial := P.mulPolynomial
  invPolynomial := P.invPolynomial
  mul_regular := P.mulPolynomial_spec
  inv_regular := P.invPolynomial_spec

end HopfPresentation

/-- Every reduced finite-type algebra admits a finite radical presentation. -/
public theorem ReducedFiniteTypeAlgebraPresentation.exists
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsReduced A] :
    Nonempty (ReducedFiniteTypeAlgebraPresentation k A) := by
  let : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨ι, hι, f, hf, hker⟩ :=
    Algebra.FinitePresentation.iff_quotient_mvPolynomial'.mp
      (inferInstance : Algebra.FinitePresentation k A)
  let : Fintype ι := hι
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  refine ⟨{
    Coordinates := ι
    finiteCoordinates := inferInstance
    relations := RingHom.ker f.toRingHom
    equiv := e
    relations_fg := hker
    relations_isRadical := ?_ }⟩
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact isReduced_of_injective e e.injective

end Theory.AlgebraicGroup
