module

public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Theory.AlgebraicGroup.Variety.CoordinateRing

universe u

/-!
# Polynomial functions and coordinate rings

This module equips polynomial functions with their algebra structure, constructs
pullbacks, and identifies polynomial functions and coordinate rings on affine
products with tensor products.  On a pure coordinate-ring tensor, the product
equivalence evaluates as the product of the two factor functions.  The proof
transports the tensor through the coordinate-ring equivalences and reduces to
the defining left and right projection formulas for `polynomialFunctionTensor`.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- Constant polynomial functions give the canonical scalar map. -/
public noncomputable def polynomialFunctionScalar (V : Variety k) :
    k →+* Variety.PolynomialFunction V where
  toFun := fun r ↦ Variety.PolynomialFunction.ofPolynomial V (MvPolynomial.C r)
  map_one' := by
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]
  map_mul' := by
    intro r s
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]
  map_zero' := by
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]
  map_add' := by
    intro r s
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]

public noncomputable instance polynomialFunctionAlgebra (V : Variety k) :
    Algebra k (Variety.PolynomialFunction V) :=
  (polynomialFunctionScalar V).toAlgebra

@[simp] public lemma polynomialFunction_algebraMap_apply
    (V : Variety k) (r : k) (x : Variety.Point V) :
    (algebraMap k (Variety.PolynomialFunction V) r) x = r := by
  change evalPolynomial x.val (MvPolynomial.C r) = r
  simp [evalPolynomial]

@[expose]
public def polynomialFunctionEvalAddHom (V : Variety k) (x : Variety.Point V) :
    Variety.PolynomialFunction V →+ k where
  toFun := fun f ↦ f x
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

@[simp] public lemma polynomialFunctionEvalAddHom_apply
    (V : Variety k) (x : Variety.Point V) (f : Variety.PolynomialFunction V) :
    polynomialFunctionEvalAddHom V x f = f x := rfl

@[simp] public lemma polynomialFunction_mul_apply
    (V : Variety k) (f g : Variety.PolynomialFunction V) (x : Variety.Point V) :
    (f * g) x = f x * g x := rfl

@[simp] public lemma polynomialFunction_zero_apply
    (V : Variety k) (x : Variety.Point V) :
    (0 : Variety.PolynomialFunction V) x = 0 := rfl

@[simp] public lemma polynomialFunction_smul_apply
    (V : Variety k) (r : k) (f : Variety.PolynomialFunction V)
    (x : Variety.Point V) : (r • f) x = r * f x := by
  change (algebraMap k (Variety.PolynomialFunction V) r * f) x = r * f x
  rw [polynomialFunction_mul_apply, polynomialFunction_algebraMap_apply]

/-- Evaluation of a polynomial as a polynomial function, as an algebra map. -/
@[expose] public def evaluationAlgHom (V : Variety k) :
    MvPolynomial V.Coordinates k →ₐ[k] Variety.PolynomialFunction V where
  toRingHom := evaluationRingHom (V := V)
  commutes' := by
    intro r
    apply Variety.PolynomialFunction.ext
    intro x
    rfl

/-- Pull a polynomial function back along the first product projection. -/
@[expose]
public def polynomialFunctionLeft (V W : Variety k) :
    Variety.PolynomialFunction V →ₐ[k]
      Variety.PolynomialFunction (Variety.prod V W) where
  toFun := fun f ↦ ⟨fun z ↦ f (Variety.prodPointEquiv V W z).1, by
    rcases f.representedBy with ⟨p, hp⟩
    refine ⟨MvPolynomial.rename Sum.inl p, fun z ↦ ?_⟩
    rw [evalPolynomial_rename]
    change f ((Variety.prodPointEquiv V W z).1) = _
    rw [hp]
    congr 1⟩
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl
  commutes' := by
    intro r
    apply Variety.PolynomialFunction.ext
    intro z
    change (algebraMap k (Variety.PolynomialFunction V) r)
        (Variety.prodPointEquiv V W z).1 =
      (algebraMap k (Variety.PolynomialFunction (Variety.prod V W)) r) z
    rw [polynomialFunction_algebraMap_apply,
      polynomialFunction_algebraMap_apply]

@[simp] public lemma polynomialFunctionLeft_apply (V W : Variety k)
    (f : Variety.PolynomialFunction V)
    (z : Variety.Point (Variety.prod V W)) :
    polynomialFunctionLeft V W f z =
      f (Variety.prodPointEquiv V W z).1 := rfl

/-- Pull a polynomial function back along the second product projection. -/
@[expose]
public def polynomialFunctionRight (V W : Variety k) :
    Variety.PolynomialFunction W →ₐ[k]
      Variety.PolynomialFunction (Variety.prod V W) where
  toFun := fun f ↦ ⟨fun z ↦ f (Variety.prodPointEquiv V W z).2, by
    rcases f.representedBy with ⟨p, hp⟩
    refine ⟨MvPolynomial.rename Sum.inr p, fun z ↦ ?_⟩
    rw [evalPolynomial_rename]
    change f ((Variety.prodPointEquiv V W z).2) = _
    rw [hp]
    congr 1⟩
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl
  commutes' := by
    intro r
    apply Variety.PolynomialFunction.ext
    intro z
    change (algebraMap k (Variety.PolynomialFunction W) r)
        (Variety.prodPointEquiv V W z).2 =
      (algebraMap k (Variety.PolynomialFunction (Variety.prod V W)) r) z
    rw [polynomialFunction_algebraMap_apply,
      polynomialFunction_algebraMap_apply]

@[simp] public lemma polynomialFunctionRight_apply (V W : Variety k)
    (f : Variety.PolynomialFunction W)
    (z : Variety.Point (Variety.prod V W)) :
    polynomialFunctionRight V W f z =
      f (Variety.prodPointEquiv V W z).2 := rfl

/-- Multiplication of functions pulled back from the two factors. -/
public noncomputable def polynomialFunctionTensor (V W : Variety k) :
    Variety.PolynomialFunction V ⊗[k] Variety.PolynomialFunction W →ₐ[k]
      Variety.PolynomialFunction (Variety.prod V W) :=
  Algebra.TensorProduct.lift (polynomialFunctionLeft V W)
    (polynomialFunctionRight V W) (fun _ _ ↦ Commute.all _ _)

@[simp] public lemma polynomialFunctionTensor_tmul (V W : Variety k)
    (f : Variety.PolynomialFunction V) (g : Variety.PolynomialFunction W) :
    polynomialFunctionTensor V W (f ⊗ₜ[k] g) =
      polynomialFunctionLeft V W f * polynomialFunctionRight V W g := by
  simp [polynomialFunctionTensor]

public theorem polynomialFunctionTensor_injective (V W : Variety k) :
    Function.Injective (polynomialFunctionTensor V W) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  let b := Module.Free.chooseBasis k (Variety.PolynomialFunction V)
  let c := TensorProduct.equivFinsuppOfBasisLeft b z
  have hzsum : c.sum (fun i g ↦ b i ⊗ₜ[k] g) = z := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    exact (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z
  have hc : c = 0 := by
    apply Finsupp.ext
    intro i
    apply Variety.PolynomialFunction.ext
    intro y
    change c i y = 0
    let q : Variety.PolynomialFunction V := c.sum (fun j g ↦ (g y) • b j)
    have hq : q = 0 := by
      apply Variety.PolynomialFunction.ext
      intro x
      let zxy := (Variety.prodPointEquiv V W).symm (x, y)
      have hxy := congrArg
        (polynomialFunctionEvalAddHom (Variety.prod V W) zxy) hz
      rw [← hzsum] at hxy
      have hzx : Variety.prodPointEquiv V W zxy = (x, y) :=
        (Variety.prodPointEquiv V W).apply_symm_apply (x, y)
      have hxy' : c.sum (fun j g ↦ b j x * g y) = 0 := by
        simpa only [map_finsuppSum, Finsupp.sum_apply,
          polynomialFunctionTensor_tmul, map_mul,
          polynomialFunctionEvalAddHom_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, polynomialFunction_mul_apply,
          polynomialFunction_zero_apply, hzx, map_zero] using hxy
      have hqeval := map_finsuppSum (polynomialFunctionEvalAddHom V x) c
        (fun j g ↦ (g y) • b j)
      change (polynomialFunctionEvalAddHom V x)
        (c.sum (fun j g ↦ (g y) • b j)) = 0
      rw [hqeval]
      simpa only [polynomialFunctionEvalAddHom_apply, Pi.smul_apply,
        smul_eq_mul, polynomialFunction_smul_apply, mul_comm] using hxy'
    have hrepr := congrArg (fun f ↦ b.repr f i) hq
    by_cases hci : c i = 0
    · rw [hci]
      rfl
    · have hi : ¬ c i = 0 → c i y = 0 := by
        simpa [q, map_finsuppSum, Finsupp.sum, Finsupp.single_apply] using hrepr
      exact hi hci
  have heq : (TensorProduct.equivFinsuppOfBasisLeft b) z =
      (TensorProduct.equivFinsuppOfBasisLeft b) 0 := by
    simp [c, hc]
  exact (TensorProduct.equivFinsuppOfBasisLeft b).injective heq

public theorem polynomialFunctionTensor_surjective (V W : Variety k) :
    Function.Surjective (polynomialFunctionTensor V W) := by
  intro f
  rcases f.representedBy with ⟨p, hp⟩
  let e := MvPolynomial.tensorEquivSum k V.Coordinates W.Coordinates k
  let t := e.symm p
  let E := Algebra.TensorProduct.map (evaluationAlgHom V) (evaluationAlgHom W)
  refine ⟨E t, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro z
  have hpoly : (polynomialFunctionTensor V W).comp E =
      (evaluationAlgHom (Variety.prod V W)).comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext
    · apply MvPolynomial.algHom_ext
      intro i
      change polynomialFunctionTensor V W (E (MvPolynomial.X i ⊗ₜ[k] 1)) =
        evaluationAlgHom (Variety.prod V W) (e (MvPolynomial.X i ⊗ₜ[k] 1))
      dsimp only [E, e]
      rw [Algebra.TensorProduct.map_tmul,
        MvPolynomial.tensorEquivSum_X_tmul_one,
        polynomialFunctionTensor_tmul]
      apply Variety.PolynomialFunction.ext
      intro w
      rw [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
        polynomialFunctionRight_apply]
      change evalPolynomial (Variety.prodPointEquiv V W w).1.val
          (MvPolynomial.X i) *
          evalPolynomial (Variety.prodPointEquiv V W w).2.val 1 =
        evalPolynomial w.val (MvPolynomial.X (Sum.inl i))
      simp [evalPolynomial, Variety.prodPointEquiv]
    · apply MvPolynomial.algHom_ext
      intro i
      change polynomialFunctionTensor V W (E (1 ⊗ₜ[k] MvPolynomial.X i)) =
        evaluationAlgHom (Variety.prod V W) (e (1 ⊗ₜ[k] MvPolynomial.X i))
      dsimp only [E, e]
      rw [Algebra.TensorProduct.map_tmul,
        MvPolynomial.tensorEquivSum_one_tmul_X,
        polynomialFunctionTensor_tmul]
      apply Variety.PolynomialFunction.ext
      intro w
      rw [polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
        polynomialFunctionRight_apply]
      change evalPolynomial (Variety.prodPointEquiv V W w).1.val 1 *
          evalPolynomial (Variety.prodPointEquiv V W w).2.val
            (MvPolynomial.X i) =
        evalPolynomial w.val (MvPolynomial.X (Sum.inr i))
      simp [evalPolynomial, Variety.prodPointEquiv]
  have ht := DFunLike.congr_fun hpoly t
  have ht' : polynomialFunctionTensor V W (E t) =
      evaluationAlgHom (Variety.prod V W) (e t) := ht
  change polynomialFunctionTensor V W (E t) z = f z
  rw [ht']
  change evalPolynomial z.val (e t) = f z
  rw [show e t = p from e.apply_symm_apply p]
  exact (hp z).symm

/-- Polynomial functions on an affine product are the tensor product of the
polynomial-function algebras of the two factors. -/
@[expose]
public noncomputable def polynomialFunction_prod_algEquiv (V W : Variety k) :
    Variety.PolynomialFunction V ⊗[k] Variety.PolynomialFunction W ≃ₐ[k]
      Variety.PolynomialFunction (Variety.prod V W) := by
  have hF : Function.Bijective (polynomialFunctionTensor V W) :=
    ⟨polynomialFunctionTensor_injective V W,
      polynomialFunctionTensor_surjective V W⟩
  exact AlgEquiv.ofBijective (polynomialFunctionTensor V W) hF

@[simp]
private theorem polynomialFunction_prod_algEquiv_apply
    (V W : Variety k)
    (t : Variety.PolynomialFunction V ⊗[k] Variety.PolynomialFunction W) :
    polynomialFunction_prod_algEquiv V W t = polynomialFunctionTensor V W t := rfl

/-- The first-isomorphism equivalence from the coordinate ring to polynomial
functions, upgraded to a `k`-algebra equivalence. -/
public noncomputable def coordinateRingAlgEquivPolynomialFunction
    (V : Variety k) : coordinateRing V ≃ₐ[k] Variety.PolynomialFunction V :=
  AlgEquiv.ofRingEquiv (f := coordinateRingEquivPolynomialFunction V) (by
    intro r
    apply Variety.PolynomialFunction.ext
    intro x
    rw [show algebraMap k (coordinateRing V) r =
      Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
        (MvPolynomial.C r) from rfl]
    simp [evaluationRingHom, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]
    exact (polynomialFunction_algebraMap_apply V r x).symm)

@[simp] public theorem coordinateRingAlgEquivPolynomialFunction_mk
    (V : Variety k) (p : MvPolynomial V.Coordinates k) :
    coordinateRingAlgEquivPolynomialFunction V
        (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V))) p) =
      evaluationRingHom p := by
  change coordinateRingEquivPolynomialFunction V
        (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V))) p) =
      evaluationRingHom p
  rw [coordinateRingEquivPolynomialFunction_mk]

/-- Pullback of polynomial functions, upgraded from a ring homomorphism to a
`k`-algebra homomorphism. -/
@[expose]
public def Variety.Morphism.pullbackAlgHom {V W : Variety k}
    (f : Variety.Morphism V W) :
    Variety.PolynomialFunction W →ₐ[k] Variety.PolynomialFunction V where
  toRingHom := f.pullbackRingHom
  commutes' := by
    intro r
    apply Variety.PolynomialFunction.ext
    intro x
    change (algebraMap k (Variety.PolynomialFunction W) r) (f.toFun x) =
      (algebraMap k (Variety.PolynomialFunction V) r) x
    rw [polynomialFunction_algebraMap_apply,
      polynomialFunction_algebraMap_apply]

/-- Mutually inverse polynomial morphisms induce an algebra equivalence on
polynomial-function algebras, contravariantly by pullback. -/
public noncomputable def polynomialFunctionAlgEquivOfInverseMorphisms
    {V W : Variety k} (f : Variety.Morphism V W) (g : Variety.Morphism W V)
    (hgf : ∀ x, g.toFun (f.toFun x) = x)
    (hfg : ∀ y, f.toFun (g.toFun y) = y) :
    Variety.PolynomialFunction W ≃ₐ[k] Variety.PolynomialFunction V := by
  refine AlgEquiv.ofAlgHom f.pullbackAlgHom g.pullbackAlgHom ?_ ?_
  · apply AlgHom.ext
    intro a
    apply Variety.PolynomialFunction.ext
    intro x
    change a (g.toFun (f.toFun x)) = a x
    rw [hgf]
  · apply AlgHom.ext
    intro a
    apply Variety.PolynomialFunction.ext
    intro y
    change a (f.toFun (g.toFun y)) = a y
    rw [hfg]

/-- Mutually inverse polynomial morphisms induce an algebra equivalence of
coordinate rings. -/
public noncomputable def coordinateRingAlgEquivOfInverseMorphisms
    {V W : Variety k} (f : Variety.Morphism V W) (g : Variety.Morphism W V)
    (hgf : ∀ x, g.toFun (f.toFun x) = x)
    (hfg : ∀ y, f.toFun (g.toFun y) = y) :
    coordinateRing W ≃ₐ[k] coordinateRing V :=
  (coordinateRingAlgEquivPolynomialFunction W).trans
    ((polynomialFunctionAlgEquivOfInverseMorphisms f g hgf hfg).trans
      (coordinateRingAlgEquivPolynomialFunction V).symm)

/-- Restrict a polynomial morphism to closed subvarieties when it maps the
source closed set into the target closed set. -/
@[expose]
public def Variety.Morphism.restrictClosedSubvariety
    {V W : Variety k} (f : Variety.Morphism V W)
    {S : Set (Variety.Point V)} {T : Set (Variety.Point W)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed W T)
    (hmap : ∀ x, x ∈ S → f.toFun x ∈ T) :
    Variety.Morphism (Variety.closedSubvariety hS)
      (Variety.closedSubvariety hT) where
  toFun := fun x => (Variety.closedSubvarietyPointEquiv hT).symm
    ⟨f.toFun (Variety.closedSubvarietyPointEquiv hS x).1,
      hmap _ (Variety.closedSubvarietyPointEquiv hS x).2⟩
  regular := by
    intro i
    rcases f.regular i with ⟨p, hp⟩
    refine ⟨p, fun x => ?_⟩
    change (f.toFun (Variety.closedSubvarietyPointEquiv hS x).1).val i =
      evalPolynomial x.val p
    rw [hp]
    rfl

@[simp]
public lemma Variety.Morphism.restrictClosedSubvariety_apply
    {V W : Variety k} (f : Variety.Morphism V W)
    {S : Set (Variety.Point V)} {T : Set (Variety.Point W)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed W T)
    (hmap : ∀ x, x ∈ S → f.toFun x ∈ T)
    (x : Variety.Point (Variety.closedSubvariety hS)) :
    (Variety.closedSubvarietyPointEquiv hT
      (f.restrictClosedSubvariety hS hT hmap |>.toFun x)).1 =
      f.toFun (Variety.closedSubvarietyPointEquiv hS x).1 := by
  change (Variety.closedSubvarietyPointEquiv hT
    ((Variety.closedSubvarietyPointEquiv hT).symm
      ⟨f.toFun (Variety.closedSubvarietyPointEquiv hS x).1,
        hmap _ (Variety.closedSubvarietyPointEquiv hS x).2⟩)).1 = _
  rw [Equiv.apply_symm_apply]

/-- Tensoring the coordinate-ring/polynomial-function equivalences of two
varieties gives an algebra equivalence on their tensor products. -/
public noncomputable def coordinateRingTensorAlgEquivPolynomialFunction
    (V W : Variety k) :
    coordinateRing V ⊗[k] coordinateRing W ≃ₐ[k]
      Variety.PolynomialFunction V ⊗[k] Variety.PolynomialFunction W :=
  Algebra.TensorProduct.congr (coordinateRingAlgEquivPolynomialFunction V)
    (coordinateRingAlgEquivPolynomialFunction W)

@[simp]
private theorem coordinateRingTensorAlgEquivPolynomialFunction_tmul
    (V W : Variety k) (a : coordinateRing V) (b : coordinateRing W) :
    coordinateRingTensorAlgEquivPolynomialFunction V W (a ⊗ₜ[k] b) =
      coordinateRingAlgEquivPolynomialFunction V a ⊗ₜ[k]
        coordinateRingAlgEquivPolynomialFunction W b := by
  change
    (Algebra.TensorProduct.map
      (coordinateRingAlgEquivPolynomialFunction V).toAlgHom
      (coordinateRingAlgEquivPolynomialFunction W).toAlgHom) (a ⊗ₜ[k] b) =
      coordinateRingAlgEquivPolynomialFunction V a ⊗ₜ[k]
        coordinateRingAlgEquivPolynomialFunction W b
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- The coordinate ring of the custom affine product is the tensor product of
the coordinate rings of its factors. -/
public noncomputable def coordinateRing_prod_equiv_tensorProduct
    (V W : Variety k) :
    coordinateRing V ⊗[k] coordinateRing W ≃ₐ[k]
      coordinateRing (Variety.prod V W) :=
  (coordinateRingTensorAlgEquivPolynomialFunction V W).trans
    ((polynomialFunction_prod_algEquiv V W).trans
      (coordinateRingAlgEquivPolynomialFunction (Variety.prod V W)).symm)

private theorem coordinateRing_prod_equiv_tensorProduct_tmul_apply_aux
    (V W : Variety k) (a : coordinateRing V) (b : coordinateRing W)
    (z : Variety.Point (Variety.prod V W)) :
    (coordinateRingAlgEquivPolynomialFunction (Variety.prod V W)
        (coordinateRing_prod_equiv_tensorProduct V W (a ⊗ₜ[k] b))) z =
      (coordinateRingAlgEquivPolynomialFunction V a)
          (Variety.prodPointEquiv V W z).1 *
      (coordinateRingAlgEquivPolynomialFunction W b)
          (Variety.prodPointEquiv V W z).2 := by
  simp [coordinateRing_prod_equiv_tensorProduct,
    coordinateRingTensorAlgEquivPolynomialFunction_tmul,
    polynomialFunction_prod_algEquiv_apply, polynomialFunctionTensor_tmul,
    polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
    polynomialFunctionRight_apply]

public theorem coordinateRing_prod_equiv_tensorProduct_tmul_apply
    (V W : Variety k) (a : coordinateRing V) (b : coordinateRing W)
    (z : Variety.Point (Variety.prod V W)) :
    (coordinateRingAlgEquivPolynomialFunction (Variety.prod V W)
        (coordinateRing_prod_equiv_tensorProduct V W (a ⊗ₜ[k] b))) z =
      (coordinateRingAlgEquivPolynomialFunction V a)
          (Variety.prodPointEquiv V W z).1 *
      (coordinateRingAlgEquivPolynomialFunction W b)
          (Variety.prodPointEquiv V W z).2 :=
  coordinateRing_prod_equiv_tensorProduct_tmul_apply_aux V W a b z

/-! Polynomial-function algebras on affine varieties are reduced. -/

public instance Variety.polynomialFunction_isReduced (V : Variety k) :
    IsReduced (Variety.PolynomialFunction V) := by
  refine IsReduced.mk ?_
  intro f hf
  apply Variety.PolynomialFunction.ext
  intro x
  let ev : Variety.PolynomialFunction V →+* k :=
    { toFun := fun q => q x
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact (isReduced_iff k).mp inferInstance (f x) (hf.map ev)

end Theory.AlgebraicGroup
