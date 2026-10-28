module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction
public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.Morphism.Power
public import Mathlib.Algebra.CharP.Two

/-!
# Root and torus calculations for the D4 Frobenius differential

The actual Frobenius in `Geometry` kills the tangent of every root subgroup.
Indeed, its composite with the given algebraic root parametrization factors
through squaring on the affine line. The pullback of its coordinate is a
square, which every derivation kills in characteristic two. Surjectivity of
the differential of the parametrizing isomorphism gives the entire root
subgroup tangent, independently of any tangent spanning assertion.

Squaring on a torus likewise has zero differential: transport to its genuine
diagonal-group model and apply the same coordinate calculation. Consequently,
if the actual Frobenius squares torus points, and the torus and root subgroup
tangents span the ambient tangent, its full differential vanishes. Those two
geometric inputs remain explicit in the assembly theorem below. In particular,
point generation or density is not used as a substitute for tangent spanning.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, 6.2 and
10.5--10.8, `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup Theory.AlgebraicGroup.Bor1

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

omit [IsAlgClosed k] in
private theorem differential_eq_zero_of_coordinate_square
    {G : Variety k} [AlgebraicGroup G] (f : Morphism G G)
    (hf : ∀ x i, (f.onPoints x).val i = x.val i ^ 2) :
    identityTangentMorphismLinearMap f = 0 := by
  apply LinearMap.ext
  intro D
  apply coordinateTangentMap_injective G
  funext i
  let a := Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)
  have ha : f.toVariety.pullbackAlgHom a = a * a := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (f.onPoints x).val (MvPolynomial.X i) =
      evalPolynomial x.val (MvPolynomial.X i) * evalPolynomial x.val (MvPolynomial.X i)
    simp only [evalPolynomial_X, hf, pow_two]
  change D (f.toVariety.pullbackAlgHom a) = 0
  rw [ha, Derivation.leibniz]
  exact CharTwo.add_self_eq_zero _

private def additiveSquare : Morphism (KPlus k) (KPlus k) where
  toVariety := {
    toFun := fun x => kPlusPoint (x.val PUnit.unit ^ 2)
    regular := by
      intro i
      refine ⟨MvPolynomial.X PUnit.unit ^ 2, ?_⟩
      intro x
      simp [evalPolynomial]
      rfl }
  map_one := by
    change kPlusPoint ((0 : k) ^ 2) = kPlusPoint 0
    simp
  map_mul := by
    intro x y
    change kPlusPoint ((x * y).val PUnit.unit ^ 2) =
      kPlusPoint (x.val PUnit.unit ^ 2) * kPlusPoint (y.val PUnit.unit ^ 2)
    rw [kPlusPoint_coordinate_mul, kPlusPoint_mul, CharTwo.add_sq]

omit [IsAlgClosed k] in
private theorem additiveSquare_differential_eq_zero :
    identityTangentMorphismLinearMap (additiveSquare (k := k)) = 0 :=
  differential_eq_zero_of_coordinate_square _ (fun _ _ => rfl)

omit [CharP k 2] in
private theorem iso_differential_surjective
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (e : Iso H G) : Function.Surjective (identityTangentMorphismLinearMap e.hom) := by
  intro D
  refine ⟨identityTangentMorphismLinearMap e.inv D, ?_⟩
  have he : e.hom.comp e.inv = Morphism.id G :=
    Morphism.ext _ _ (funext e.inv_hom_id)
  have hd := LinearMap.congr_fun (identityTangentMorphismLinearMap_comp e.inv e.hom) D
  rw [he, identityTangentMorphismLinearMap_id] at hd
  exact hd.symm

variable {K : Variety k} [AlgebraicGroup K]

/-- Frobenius kills the full tangent of each actual root subgroup, using the
specified root parametrization and its algebraic inverse. -/
public theorem Geometry.frobenius_differential_root_eq_zero
    (S : Geometry K) (a : S.roots.Root) :
    (identityTangentMorphismLinearMap S.frobenius).comp
      (identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion) = 0 := by
  let x := (S.roots.rootSubgroup a).inclusion.comp (S.rootParameter a).hom
  have he : S.frobenius.comp x = x.comp additiveSquare := by
    apply Morphism.ext
    funext t
    exact S.frobenius_root a (t.val PUnit.unit)
  have hx : identityTangentMorphismLinearMap (S.frobenius.comp x) = 0 := by
    rw [he, identityTangentMorphismLinearMap_comp, additiveSquare_differential_eq_zero,
      LinearMap.comp_zero]
  apply LinearMap.ext
  intro D
  obtain ⟨E, rfl⟩ := iso_differential_surjective (S.rootParameter a) D
  exact LinearMap.congr_fun hx E

omit [IsAlgClosed k] in
private theorem diagonal_square_differential_eq_zero (n : ℕ) :
    identityTangentMorphismLinearMap
      (commutativeNpowMorphism (dVariety k n) (dVariety_isMulCommutative n) 2) = 0 := by
  apply differential_eq_zero_of_coordinate_square
  intro x i
  change ((npowMorphism (dVariety k n) 2).toFun x).val i = _
  rw [npowMorphism_apply, pow_two, dPoint_mul_apply, pow_two]

private theorem torus_square_differential_eq_zero
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T) :
    identityTangentMorphismLinearMap
      (commutativeNpowMorphism T hT.isMulCommutative 2) = 0 := by
  obtain ⟨n, ⟨e⟩⟩ := hT
  let f := commutativeNpowMorphism T (IsTorus.isMulCommutative ⟨n, ⟨e⟩⟩) 2
  let g := commutativeNpowMorphism (dVariety k n) (dVariety_isMulCommutative n) 2
  have he : f.comp e.hom = e.hom.comp g := by
    apply Morphism.ext
    funext x
    change (npowMorphism T 2).toFun (e.hom.onPoints x) =
      e.hom.onPoints ((npowMorphism (dVariety k n) 2).toFun x)
    simp only [npowMorphism_apply, map_pow]
  have hd : identityTangentMorphismLinearMap (f.comp e.hom) = 0 := by
    rw [he, identityTangentMorphismLinearMap_comp, diagonal_square_differential_eq_zero,
      LinearMap.comp_zero]
  apply LinearMap.ext
  intro D
  obtain ⟨E, rfl⟩ := iso_differential_surjective e D
  exact LinearMap.congr_fun hd E

/-- The toral calculation, conditional only on identifying the actual
Frobenius point action on the chosen torus. -/
public theorem Geometry.frobenius_differential_torus_eq_zero_of_square
    (S : Geometry K)
    (hT : ∀ t : Variety.Point S.torus.carrierVariety,
      S.frobenius.onPoints (S.torus.includePoint t) = S.torus.includePoint (t ^ 2)) :
    (identityTangentMorphismLinearMap S.frobenius).comp
      (identityTangentMorphismLinearMap S.torus.inclusion) = 0 := by
  let f := commutativeNpowMorphism S.torus.carrierVariety
    S.maximalTorus.1.isMulCommutative 2
  have he : S.frobenius.comp S.torus.inclusion = S.torus.inclusion.comp f := by
    apply Morphism.ext
    funext t
    change S.frobenius.onPoints (S.torus.includePoint t) =
      S.torus.includePoint ((npowMorphism S.torus.carrierVariety 2).toFun t)
    rw [npowMorphism_apply]
    exact hT t
  rw [← identityTangentMorphismLinearMap_comp, he,
    identityTangentMorphismLinearMap_comp, torus_square_differential_eq_zero S.maximalTorus.1,
    LinearMap.comp_zero]

/-- Assemble the root and torus calculations once their tangent ranges are
proved to span. Both remaining geometric premises are explicit. -/
public theorem Geometry.frobenius_differential_eq_zero_of_torus_square_of_tangent_span
    (S : Geometry K)
    (hT : ∀ t : Variety.Point S.torus.carrierVariety,
      S.frobenius.onPoints (S.torus.includePoint t) = S.torus.includePoint (t ^ 2))
    (hspan : LinearMap.range (identityTangentMorphismLinearMap S.torus.inclusion) ⊔
      (⨆ a : S.roots.Root,
        LinearMap.range (identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion))
        = ⊤) :
    identityTangentMorphismLinearMap S.frobenius = 0 := by
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply sup_le
  · rintro _ ⟨D, rfl⟩
    exact LinearMap.congr_fun (S.frobenius_differential_torus_eq_zero_of_square hT) D
  · apply iSup_le
    intro a
    rintro _ ⟨D, rfl⟩
    exact LinearMap.congr_fun (S.frobenius_differential_root_eq_zero a) D

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
