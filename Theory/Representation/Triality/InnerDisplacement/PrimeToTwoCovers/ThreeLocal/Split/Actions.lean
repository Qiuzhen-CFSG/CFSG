module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.RelativeNormalizer
public import Mathlib.Tactic.Group

/-!
# Split triality torus reflection and inversion

The four original D₄ coroot words give the simple-reflection equations.
Composing these equations shows that the longest folded Weyl word inverts
the full torus. In the graph-field fixed coordinates, the central reflection
sends (x, y) to (x, Norm(x) / y), where x is an extension-field unit and y
is a unit of the actual fixed field. The two unit groups are not identified.

The equations descend through the faithful map from the original carrier
to the split matrices. They supply the actions used by the three-primary
normalizer configuration and its primary generator construction.

Source: GLS3 §§2.3–2.4, especially the coroot conjugation equation; the
nondefining-characteristic multiplier calculation of §6.1, Theorem 6.1.4.
-/

@[expose] public section
noncomputable section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
open Standard Standard.Parabolics Standard.ConcreteBruhat
open Standard.ConcreteBruhat.TorusCoordinates
open Theory.AlgebraicGroup.StandardRootSystem

private def reflect {U : Type*} [CommGroup U] (i : Fin 4) (a : Fin 4 → U) : Fin 4 → U :=
  match i with
  | 0 => ![(a 0)⁻¹ * a 1, a 1, a 2, a 3]
  | 1 => ![a 0, a 0 * a 2 * a 3 * (a 1)⁻¹, a 2, a 3]
  | 2 => ![a 0, a 1, (a 2)⁻¹ * a 1, a 3]
  | 3 => ![a 0, a 1, a 2, (a 3)⁻¹ * a 1]

private theorem simple_conjugation (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (a : Coordinates P) :
    MulAut.conj (weylWord P i 1) (product P a) = product P (reflect i a) := by
  change MulAut.conj (weylWord P i 1)
    (torusWord P 0 (a 0) * torusWord P 2 (a 2) * torusWord P 3 (a 3) *
      torusWord P 1 (a 1)) = _
  simp only [map_mul, MulAut.conj_apply, RootConjugation.weylWord_torusWord_conjugation P hp]
  simp only [← product_single P hp, ← product_mul P hp]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [reflect, typeDCartanMatrix, zpow_neg, zpow_ofNat] <;> group

private theorem conjugation_mul {G : Type*} [Group G] (x y z : G) :
    MulAut.conj (x * y) z = MulAut.conj x (MulAut.conj y z) := by
  rw [map_mul, MulAut.mul_apply]

private def rotate {U : Type*} [CommGroup U] (a : Fin 4 → U) : Fin 4 → U :=
  reflect 0 (reflect 2 (reflect 3 (reflect 1 a)))

private theorem rotation_conjugation (P : Parameters) (hp : P.prime = 2)
    (a : Coordinates P) :
    MulAut.conj (splitRepresentative P hp (.r 1)) (product P a) =
      product P (rotate a) := by
  have he : splitRepresentative P hp (.r 1) =
      weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 * weylWord P 1 1 := by
    simp [splitRepresentative, weylElementary, elementaryInclusion_simple_arms,
      elementaryInclusion_simple_central, show (1 : ZMod 6).val = 1 from rfl]
  refine (congrArg (fun g : SplitGroup P => MulAut.conj g (product P a)) he).trans ?_
  simp only [conjugation_mul, simple_conjugation P hp, rotate]

private theorem rotate_three {U : Type*} [CommGroup U] (a : Fin 4 → U) :
    rotate (rotate (rotate a)) = a⁻¹ := by
  funext j
  fin_cases j <;> simp [rotate, reflect, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- The longest relative Weyl word inverts the full split torus. -/
private theorem longest_conjugation (P : Parameters) (hp : P.prime = 2)
    (a : Coordinates P) :
    MulAut.conj (splitRepresentative P hp (.r 3)) (product P a) =
      (product P a)⁻¹ := by
  have he : (DihedralGroup.r (3 : ZMod 6)) =
      .r 1 * .r 1 * .r 1 := by decide
  have hw : splitRepresentative P hp (.r 3) =
      splitRepresentative P hp (.r 1) * splitRepresentative P hp (.r 1) *
        splitRepresentative P hp (.r 1) := by
    exact (congrArg (splitRepresentative P hp) he).trans
      ((splitRepresentative_mul P hp _ _).trans
        (congrArg (fun g => g * splitRepresentative P hp (.r 1))
          (splitRepresentative_mul P hp _ _)))
  refine (congrArg (fun g : SplitGroup P => MulAut.conj g (product P a)) hw).trans ?_
  simp only [conjugation_mul, rotation_conjugation P hp, rotate_three]
  exact map_inv (productHom P hp) a

/-- The field norm, expressed in the fixed units of the original parameters. -/
def normUnit (P : Parameters) (x : (ExtensionField P)ˣ) : (fixedField P)ˣ :=
  restrictUnit P (x * frobenius P x * frobenius P (frobenius P x)) (by
    simp only [map_mul, frobenius_three]
    ac_rfl)

@[simp] theorem fixedUnit_normUnit (P : Parameters) (x : (ExtensionField P)ˣ) :
    fixedUnit P (normUnit P x) = x * frobenius P x * frobenius P (frobenius P x) :=
  fixedUnit_restrictUnit P _ _

/-- The fixed-field unit inclusion is faithful. -/
theorem fixedUnit_injective (P : Parameters) : Function.Injective (fixedUnit P) :=
  fun _ _ h => Units.ext (Subtype.ext (congrArg Units.val h))

/-- The actual field norm is multiplicative, including on its three-primary part. -/
def normUnitHom (P : Parameters) : (ExtensionField P)ˣ →* (fixedField P)ˣ where
  toFun := normUnit P
  map_one' := by
    apply fixedUnit_injective P
    simp
  map_mul' x y := by
    apply fixedUnit_injective P
    simp only [fixedUnit_normUnit, map_mul]
    ac_rfl

@[simp] theorem normUnitHom_apply (P : Parameters) (x : (ExtensionField P)ˣ) :
    normUnitHom P x = normUnit P x := rfl

/-- Literal coordinates in the descended torus, retaining both unequal factors. -/
def torusElement (P : Parameters) (hp : P.prime = 2)
    (x : (ExtensionField P)ˣ) (y : (fixedField P)ˣ) : Carrier P :=
  (torusMulEquiv P hp (x, y)).val

theorem carrierToSplit_torusElement (P : Parameters) (hp : P.prime = 2)
    (x : (ExtensionField P)ˣ) (y : (fixedField P)ˣ) :
    FixedDescent.carrierToSplit P hp (torusElement P hp x y) =
      product P (expand P (x, y)) := by
  simp only [torusElement, torusMulEquiv_val, FixedDescent.carrierToSplit_toCarrier,
    inclusion_orbitElementary]

/-- The central reflection fixes the extension coordinate and reflects the
fixed-field coordinate through its actual field norm. -/
theorem central_torusElement_conjugation (P : Parameters) (hp : P.prime = 2)
    (x : (ExtensionField P)ˣ) (y : (fixedField P)ˣ) :
    simpleRepresentative P hp .central * torusElement P hp x y *
      (simpleRepresentative P hp .central)⁻¹ =
        torusElement P hp x (normUnit P x * y⁻¹) := by
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul, map_inv, carrierToSplit_torusElement,
    RelativeNormalizer.carrierToSplit_simple, splitRepresentative_simple,
    elementaryInclusion_simple_central]
  change MulAut.conj (weylWord P 1 1) (product P (expand P (x, y))) = _
  rw [simple_conjugation P hp]
  apply congrArg (product P)
  funext j
  fin_cases j <;> simp [reflect, expand, map_mul, map_inv]

/-- The central dihedral involution acts by inversion on the original torus. -/
theorem inverter_torusElement_conjugation (P : Parameters) (hp : P.prime = 2)
    (x : (ExtensionField P)ˣ) (y : (fixedField P)ˣ) :
    weylRepresentative P hp (.r 3) * torusElement P hp x y *
      (weylRepresentative P hp (.r 3))⁻¹ = (torusElement P hp x y)⁻¹ := by
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul, map_inv, carrierToSplit_torusElement,
    FixedDescent.carrierToSplit_representative]
  exact longest_conjugation P hp _

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
