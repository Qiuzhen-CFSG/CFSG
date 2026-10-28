module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.FirstCohomologySemidirect
public import Theory.SpecificGroups.SL2.Affine

/-!
# Frobenius central corrections extending through the natural endpoint

The square roots of the two row products give a natural SL₂(4) cocycle.
Adding its scalar multiples constructs actual automorphisms of the full
special affine endpoint. They fix the translations and diagonal torus,
and add precisely a Frobenius central correction to the upper root.
These are the exceptional central corrections needed for whole-Borel
amalgam compatibility; no extension or compatibility premise is used.
-/

public section
open Matrix SemidirectProduct
namespace Representation.SL2FourNaturalExtensions
open SL2FourNatural OneCohomology

/-- Square roots of the two row products in the existing natural model. -/
@[expose] def rowProduct (g : SL) : V := fun i => fieldFrobenius (g.val i 0 * g.val i 1)

private theorem frobenius_square (x : F) : fieldFrobenius (x ^ 2) = x := by
  simpa only [fieldFrobenius_apply, ← pow_mul] using pow_four x

private theorem row_identity (a b u v w t : F) (hd : u*t+v*w=1) :
    fieldFrobenius ((a*u+b*w)*(a*v+b*t)) =
      a*fieldFrobenius (u*v)+b*fieldFrobenius (w*t)+fieldFrobenius (a*b) := by
  have he : (a*u+b*w)*(a*v+b*t) = a^2*(u*v)+b^2*(w*t)+a*b*(u*t+v*w) := by ring
  rw [he,hd,mul_one]
  simp only [map_add,map_mul,frobenius_square]

/-- The explicit row-product correction is a genuine natural cocycle. -/
theorem rowProduct_mul (g h : SL) : rowProduct (g*h) = action g (rowProduct h) + rowProduct g := by
  have hd : h.val 0 0*h.val 1 1+h.val 0 1*h.val 1 0=1 := by
    simpa only [Matrix.det_fin_two,sub_eq_add_neg,CharTwo.neg_eq] using h.property
  funext i
  change fieldFrobenius ((g*h).val i 0*(g*h).val i 1) = _
  simpa only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    action_apply,Matrix.mulVec,dotProduct,Pi.add_apply,rowProduct] using
    row_identity (g.val i 0) (g.val i 1) _ _ _ _ hd

/-- The same correction in the natural cohomology space over F₄. -/
@[expose] def rowProductCocycle : cocycles ((specialLinearNatural 2 : Representation F SL V)) :=
  ⟨rowProduct, fun g h => rowProduct_mul g h⟩

/-- A scalar multiple of the central correction gives an automorphism of
exactly the existing special affine endpoint. -/
@[expose] def centralCorrection (k : F) : MulAut (Matrix.SL2.Affine F) :=
  splitCocycleAut (specialLinearNatural 2) (Matrix.SL2.naturalAction F)
    (fun _ _ => rfl) (k • rowProductCocycle)

/-- The complete original quotient coordinate is unchanged. -/
theorem centralCorrection_right (k : F) (x : Matrix.SL2.Affine F) :
    (centralCorrection k x).right = x.right := rfl

/-- Formula on the original translation coordinate. -/
theorem centralCorrection_left (k : F) (x : Matrix.SL2.Affine F) :
    (centralCorrection k x).left.toAdd = x.left.toAdd + k • rowProduct x.right := rfl

/-- Every original translation is fixed pointwise. -/
theorem centralCorrection_inl (k : F) (v : Multiplicative V) :
    centralCorrection k (inl v) = inl v := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change v.toAdd + k • rowProduct 1 = v.toAdd
    have hz : rowProduct 1 = 0 := by funext i; fin_cases i <;> simp [rowProduct]
    rw [hz,smul_zero,add_zero]
  · rfl

/-- The correction fixes every diagonal actor, including the full cubic torus. -/
theorem centralCorrection_diagonal (k : F) (g : SL)
    (hg01 : g.val 0 1 = 0) (hg10 : g.val 1 0 = 0) :
    centralCorrection k (inr g) = inr g := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change 0 + k • rowProduct g = 0
    have hz : rowProduct g = 0 := by
      funext i
      fin_cases i <;> simp [rowProduct,hg01,hg10]
    rw [hz,smul_zero,zero_add]
  · rfl

/-- On the upper root the correction is the precise Frobenius central shear. -/
theorem centralCorrection_upper (k x : F) :
    centralCorrection k (inr (upper x)) =
      inl (Multiplicative.ofAdd ![k*x^2,0]) * inr (upper x) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    rw [centralCorrection_left]
    simp only [SemidirectProduct.left_inr, toAdd_one, SemidirectProduct.mul_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
      mul_one, toAdd_ofAdd]
    change 0 + k • rowProduct (upper x) = ![k*x^2,0]
    funext i
    fin_cases i <;> simp [rowProduct,upper,fieldFrobenius_apply]
  · simp [centralCorrection_right]

end Representation.SL2FourNaturalExtensions
