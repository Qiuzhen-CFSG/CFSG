module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.GraphField
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity.SpinTangents
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.ZeroDifferential
public import Theory.AlgebraicGroup.Morphism.Power

/-!
# Lang surjectivity for the concrete Spin graph-field map

Ordinary Frobenius squares the root parameters and the four coroot coordinates.
Squaring has zero differential in characteristic two. The proved tangent span
for the actual Spin torus and root subgroups therefore makes the full Frobenius
differential zero. Positive powers and the graph-field composite inherit this,
and connected zero-differential Lang surjectivity supplies the conjugator used
by `Descent`.

The local derivative calculations follow the private calculations in
`ClassBound/Fusion/ConnectedLang/FrobeniusDifferential`. Here the concrete
pinning, coordinate isomorphism and `Pinning.torus_root_tangent_span`
discharge their geometric premises.
Source: Steinberg, §§6.2 and 10.1–10.8, `refs/KGroup/GLS3/Chapter2St2.tex`;
GLS3 §2.2 for the graph-field convention.
-/

public section

noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
open Theory.AlgebraicGroup Theory.AlgebraicGroup.Bor1
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.CorootTorus
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
omit [IsAlgClosed k] in
private theorem differential_eq_zero_of_coordinate_square
    {G : Variety k} [AlgebraicGroup G] (f : Morphism G G)
    (hf : ∀ x i, (f.onPoints x).val i = x.val i ^ 2) :
    Bor1.identityTangentMorphismLinearMap f = 0 := by
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
    Bor1.identityTangentMorphismLinearMap (additiveSquare (k := k)) = 0 :=
  differential_eq_zero_of_coordinate_square _ (fun _ _ => rfl)

omit [CharP k 2] in
private theorem iso_differential_surjective
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (e : Iso H G) : Function.Surjective (Bor1.identityTangentMorphismLinearMap e.hom) := by
  intro D
  refine ⟨Bor1.identityTangentMorphismLinearMap e.inv D, ?_⟩
  have he : e.hom.comp e.inv = Morphism.id G :=
    Morphism.ext _ _ (funext e.inv_hom_id)
  have hd := LinearMap.congr_fun (Bor1.identityTangentMorphismLinearMap_comp e.inv e.hom) D
  rw [he, Bor1.identityTangentMorphismLinearMap_id] at hd
  exact hd.symm

omit [IsAlgClosed k] in
private theorem diagonal_square_differential_eq_zero (n : ℕ) :
    Bor1.identityTangentMorphismLinearMap
      (commutativeNpowMorphism (dVariety k n) (dVariety_isMulCommutative n) 2) = 0 := by
  apply differential_eq_zero_of_coordinate_square
  intro x i
  change ((npowMorphism (dVariety k n) 2).toFun x).val i = _
  rw [npowMorphism_apply, pow_two, dPoint_mul_apply, pow_two]

variable (k)
private theorem frobenius_root_differential (r : RootIndex) :
    (Bor1.identityTangentMorphismLinearMap (regularFrobeniusLift k 1)).comp
      (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k r).inclusion) = 0 := by
  let x := (rootClosedSubgroup k r).inclusion.comp (rootParametrization k r).hom
  have he : (regularFrobeniusLift k 1).comp x = x.comp additiveSquare := by
    apply Morphism.ext
    funext t
    change (regularFrobeniusLift k 1).onPoints (x.onPoints t) =
      x.onPoints (additiveSquare.onPoints t)
    rw [regularFrobeniusLift_onPoints]
    conv_lhs => rw [← kPlusPoint_coordinate t]
    change frobeniusPointAut k 1
      ((rootClosedSubgroup k r).includePoint ((rootParametrization k r).value (t.val PUnit.unit))) =
        (rootClosedSubgroup k r).includePoint
          ((rootParametrization k r).value (t.val PUnit.unit ^ 2))
    simp only [rootParametrization_inclusion, GraphField.frobenius_rootPoint, pow_one]
  have hx : Bor1.identityTangentMorphismLinearMap ((regularFrobeniusLift k 1).comp x) = 0 := by
    rw [he, Bor1.identityTangentMorphismLinearMap_comp, additiveSquare_differential_eq_zero,
      LinearMap.comp_zero]
  apply LinearMap.ext
  intro D
  obtain ⟨E, rfl⟩ := iso_differential_surjective (rootParametrization k r) D
  exact LinearMap.congr_fun hx E

private theorem frobenius_torus_differential :
    (Bor1.identityTangentMorphismLinearMap (regularFrobeniusLift k 1)).comp
      (Bor1.identityTangentMorphismLinearMap (closedSubgroup k).inclusion) = 0 := by
  let x := (closedSubgroup k).inclusion.comp (coordinateIso k).hom
  let s := commutativeNpowMorphism (dVariety k 4) (dVariety_isMulCommutative 4) 2
  have he : (regularFrobeniusLift k 1).comp x = x.comp s := by
    apply Morphism.ext
    funext t
    change (regularFrobeniusLift k 1).onPoints
      ((closedSubgroup k).inclusion.onPoints ((coordinateIso k).hom.onPoints t)) =
        (closedSubgroup k).inclusion.onPoints ((coordinateIso k).hom.onPoints ((npowMorphism (dVariety k 4) 2).toFun t))
    rw [npowMorphism_apply, coordinateIso_hom_apply, inclusion_parameterPoint, regularFrobeniusLift_onPoints,
      GraphField.frobenius_parameter, coordinateIso_hom_apply, inclusion_parameterPoint,
      dPointEquiv_pow]
    rfl
  have hx : Bor1.identityTangentMorphismLinearMap ((regularFrobeniusLift k 1).comp x) = 0 := by
    rw [he, Bor1.identityTangentMorphismLinearMap_comp,
      diagonal_square_differential_eq_zero, LinearMap.comp_zero]
  apply LinearMap.ext
  intro D
  obtain ⟨E, rfl⟩ := iso_differential_surjective (coordinateIso k) D
  exact LinearMap.congr_fun hx E

/-- The ordinary Frobenius kills the whole tangent of the concrete Spin variety. -/
theorem frobenius_one_differential_eq_zero :
    Bor1.identityTangentMorphismLinearMap (regularFrobeniusLift k 1) = 0 := by
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← torus_root_tangent_span k]
  apply sup_le
  · rintro _ ⟨D, rfl⟩
    exact LinearMap.congr_fun (frobenius_torus_differential k) D
  · apply iSup_le
    intro r
    rintro _ ⟨D, rfl⟩
    exact LinearMap.congr_fun (frobenius_root_differential k r) D

/-- Every positive graph-field map on the actual Spin variety has zero differential. -/
theorem graphField_differential_eq_zero (n : ℕ) (hn : 0 < n) :
    Bor1.identityTangentMorphismLinearMap (GraphField.regularSigma k n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [GraphField.regularSigma, Bor1.identityTangentMorphismLinearMap_comp,
    show m.succ = m + 1 from rfl, regularFrobeniusLift_add,
    Bor1.identityTangentMorphismLinearMap_comp,
    frobenius_one_differential_eq_zero, LinearMap.comp_zero, LinearMap.zero_comp]

/-- Lang surjectivity for the literal Spin graph-field endomorphism. -/
theorem graphField_lang_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun g : Points k => g * (GraphField.sigma k n g)⁻¹) := by
  have h := langMorphism_surjective_of_differential_eq_zero (GraphField.regularSigma k n)
    (GraphField.regularSigma_isSteinberg k n hn).1 (isConnected k)
    (graphField_differential_eq_zero k n hn)
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨x, by simpa only [langMorphism_apply, GraphField.regularSigma_onPoints, map_inv] using hx⟩

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
