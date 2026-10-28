module

public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Basic

/-!
# Factor-compatible coordinates for the quaternion-product square form

For two commuting quaternion eights with common center of order two, the
images of their marked generators `i,j` give four coordinates on the actual
central quotient. All four generators square to the unique nonidentity
central element. The commutator pairing is one within each marked pair and
zero between the factors.

Pairing with the opposite generator therefore gives the coordinate map.
The four marked images map to the standard basis, so the map is surjective;
the intrinsic quotient has order sixteen, which proves bijectivity.
Expanding the quadratic form gives `x² + xy + y²` on each factor. This is the
coordinate identification needed to transport the intrinsic square-isometry
group to the concrete four-dimensional plus form.

Source: Aschbacher–Smith, Lemma 14.2.21, refs/quasithin.pdf,
printed p.988, PDF p.1005, the `Q₈ * Q₈` orthogonal-action step.
-/

public section

open scoped commutatorElement
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

private abbrev qgen : Fin 2 → QuaternionGroup 2 := ![QuaternionGroup.a 1, QuaternionGroup.xa 0]

/-- The images of the quaternion generators `i = a 1` and `j = xa 0`
in the actual quotient by the center. -/
def factorVector (B : Subgroup Q) (e : B ≃* QuaternionGroup 2) (i : Fin 2) :
    d.SquareSpace := Additive.ofMul (QuotientGroup.mk' (center Q) (e.symm (qgen i) : Q))

/-- Each marked generator squares to the common nonidentity central involution. -/
theorem factorVector_quadraticForm (B : Subgroup Q) (e : B ≃* QuaternionGroup 2)
    (i : Fin 2) : d.quadraticForm (d.factorVector B e i) = 1 := by
  rw [d.quadraticForm_apply, factorVector, d.binarySquare_mk, d.centerCoordinate_eq_one_iff]
  intro h
  have hval := congrArg Subtype.val h
  have hB : e.symm (qgen i) ^ 2 = 1 := Subtype.ext hval
  have hh : qgen i ^ 2 = 1 := by simpa only [map_pow, map_one, e.apply_symm_apply] using congrArg e hB
  exact (by decide : ∀ i : Fin 2, qgen i ^ 2 ≠ 1) i hh

/-- The two quaternion generators form a symplectic pair in the central quotient. -/
theorem factorVector_polar (B : Subgroup Q) (e : B ≃* QuaternionGroup 2)
    (i j : Fin 2) : d.quadraticForm.polarBilin (d.factorVector B e i)
      (d.factorVector B e j) = if i = j then 0 else 1 := by
  rw [factorVector, factorVector, d.polarBilin_mk]
  by_cases h : i = j
  · subst j
    simp only [ite_true, commutatorElement_self]
    exact (d.centerCoordinate_eq_zero_iff _).mpr (Subtype.ext rfl)
  · rw [if_neg h, d.centerCoordinate_eq_one_iff]
    intro he
    have hB : ⁅e.symm (qgen i), e.symm (qgen j)⁆ = 1 := by
      apply B.subtype_injective
      rw [map_commutatorElement, map_one]
      exact congrArg (fun z : center Q => (z : Q)) he
    have hh : ⁅qgen i, qgen j⁆ = 1 := by
      simpa only [map_commutatorElement, map_one, e.apply_symm_apply] using congrArg e hB
    exact (by decide : ∀ i j : Fin 2, i ≠ j → ⁅qgen i, qgen j⁆ ≠ 1) i j h hh

/-- Commutation of the actual factors makes their quotient planes orthogonal. -/
theorem factorVector_cross (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i j : Fin 2) :
    d.quadraticForm.polarBilin (d.factorVector d.left eL i)
      (d.factorVector d.right eR j) = 0 := by
  rw [factorVector, factorVector, d.polarBilin_mk, d.centerCoordinate_eq_zero_iff]
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (d.commute _ (eL.symm (qgen i)).property _ (eR.symm (qgen j)).property)

private theorem factorVector_cross_rev (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i j : Fin 2) :
    d.quadraticForm.polarBilin (d.factorVector d.right eR i)
      (d.factorVector d.left eL j) = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact d.factorVector_cross eL eR j i

private noncomputable def coordinateMap (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) :
    d.SquareSpace →ₗ[ZMod 2] ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) where
  toFun v :=
    (![d.quadraticForm.polarBilin v (d.factorVector d.left eL 1),
       d.quadraticForm.polarBilin v (d.factorVector d.left eL 0)],
     ![d.quadraticForm.polarBilin v (d.factorVector d.right eR 1),
       d.quadraticForm.polarBilin v (d.factorVector d.right eR 0)])
  map_add' v w := by
    ext i <;> fin_cases i <;> simp [LinearMap.add_apply]
  map_smul' a v := by
    ext i <;> fin_cases i <;> simp [LinearMap.smul_apply]

private theorem coordinateMap_left (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i : Fin 2) :
    d.coordinateMap eL eR (d.factorVector d.left eL i) = (Pi.single i 1, 0) := by
  ext j <;> fin_cases j <;> fin_cases i <;>
    simp [coordinateMap, -QuadraticMap.polarBilin_apply_apply,
      d.factorVector_polar, d.factorVector_cross]

private theorem coordinateMap_right (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i : Fin 2) :
    d.coordinateMap eL eR (d.factorVector d.right eR i) = (0, Pi.single i 1) := by
  ext j <;> fin_cases j <;> fin_cases i <;>
    simp [coordinateMap, -QuadraticMap.polarBilin_apply_apply,
      d.factorVector_polar, d.factorVector_cross_rev]

private def coordinateLift (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2)
    (v : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) : d.SquareSpace :=
  v.1 0 • d.factorVector d.left eL 0 + v.1 1 • d.factorVector d.left eL 1 +
  v.2 0 • d.factorVector d.right eR 0 + v.2 1 • d.factorVector d.right eR 1

private theorem coordinateMap_lift (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2)
    (v : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    d.coordinateMap eL eR (d.coordinateLift eL eR v) = v := by
  simp only [coordinateLift, map_add, map_smul, d.coordinateMap_left, d.coordinateMap_right]
  ext i <;> fin_cases i <;> simp

private theorem coordinateMap_bijective (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) :
    Function.Bijective (d.coordinateMap eL eR) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨fun v => ⟨d.coordinateLift eL eR v, d.coordinateMap_lift eL eR v⟩, ?_⟩
  change Nat.card (Q ⧸ center Q) = _
  rw [d.quotient_card]
  simp

/-- Factor-compatible coordinates on the intrinsic square space. The first pair
is marked by the left quaternion model, the second by the right model. -/
noncomputable def coordinates (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) :
    d.SquareSpace ≃ₗ[ZMod 2] ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  LinearEquiv.ofBijective (d.coordinateMap eL eR) (d.coordinateMap_bijective eL eR)

/-- The inverse coordinate map is the indicated linear combination of the
four actual quaternion-generator images. -/
theorem coordinates_symm_apply (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2)
    (v : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    (d.coordinates eL eR).symm v =
      v.1 0 • d.factorVector d.left eL 0 + v.1 1 • d.factorVector d.left eL 1 +
      v.2 0 • d.factorVector d.right eR 0 + v.2 1 • d.factorVector d.right eR 1 := by
  change (d.coordinates eL eR).symm v = d.coordinateLift eL eR v
  apply (d.coordinates eL eR).injective
  exact ((d.coordinates eL eR).apply_symm_apply v).trans (d.coordinateMap_lift eL eR v).symm

private theorem quadraticForm_lift (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2)
    (v : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    d.quadraticForm (d.coordinateLift eL eR v) =
      v.1 0 ^ 2 + v.1 0 * v.1 1 + v.1 1 ^ 2 +
      v.2 0 ^ 2 + v.2 0 * v.2 1 + v.2 1 ^ 2 := by
  have hadd (u w : d.SquareSpace) :
      d.quadraticForm (u + w) = d.quadraticForm u + d.quadraticForm w +
        d.quadraticForm.polarBilin u w := QuadraticMap.map_add _ u w
  simp only [coordinateLift, hadd, QuadraticMap.map_smul, LinearMap.map_add₂,
    map_smul, LinearMap.smul_apply, d.factorVector_quadraticForm,
    d.factorVector_polar, d.factorVector_cross]
  simp only [Fin.zero_ne_one, ite_false, smul_eq_mul, mul_one, mul_zero, add_zero]
  ring

/-- Squaring in `Q` becomes the orthogonal sum of the two anisotropic binary
planes, with the coordinates marked by the embedded quaternion factors. -/
theorem quadraticForm_coordinates (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (v : d.SquareSpace) :
    d.quadraticForm v =
      ((d.coordinates eL eR v).1 0) ^ 2 +
      (d.coordinates eL eR v).1 0 * (d.coordinates eL eR v).1 1 +
      ((d.coordinates eL eR v).1 1) ^ 2 +
      ((d.coordinates eL eR v).2 0) ^ 2 +
      (d.coordinates eL eR v).2 0 * (d.coordinates eL eR v).2 1 +
      ((d.coordinates eL eR v).2 1) ^ 2 := by
  have hv : v = d.coordinateLift eL eR (d.coordinates eL eR v) := by
    unfold coordinateLift
    rw [← d.coordinates_symm_apply, LinearEquiv.symm_apply_apply]
  calc
    d.quadraticForm v = d.quadraticForm (d.coordinateLift eL eR (d.coordinates eL eR v)) :=
      congrArg d.quadraticForm hv
    _ = _ := d.quadraticForm_lift eL eR _

omit [Finite Q] in
/-- The first marked vector is the image of `i` under the given factor embedding. -/
theorem factorVector_zero (B : Subgroup Q) (e : B ≃* QuaternionGroup 2) :
    d.factorVector B e 0 =
      Additive.ofMul (QuotientGroup.mk' (center Q) (e.symm (QuaternionGroup.a 1) : Q)) := by rfl

omit [Finite Q] in
/-- The second marked vector is the image of `j` under the given factor embedding. -/
theorem factorVector_one (B : Subgroup Q) (e : B ≃* QuaternionGroup 2) :
    d.factorVector B e 1 =
      Additive.ofMul (QuotientGroup.mk' (center Q) (e.symm (QuaternionGroup.xa 0) : Q)) := by rfl

/-- Coordinates are the polar pairings with the opposite generator of each factor. -/
theorem coordinates_apply (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (v : d.SquareSpace) :
    d.coordinates eL eR v =
      (![d.quadraticForm.polarBilin v (d.factorVector d.left eL 1),
         d.quadraticForm.polarBilin v (d.factorVector d.left eL 0)],
       ![d.quadraticForm.polarBilin v (d.factorVector d.right eR 1),
         d.quadraticForm.polarBilin v (d.factorVector d.right eR 0)]) := by rfl

/-- The two left generators map to the first two standard basis vectors. -/
@[simp] theorem coordinates_left (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i : Fin 2) :
    d.coordinates eL eR (d.factorVector d.left eL i) = (Pi.single i 1, 0) :=
  d.coordinateMap_left eL eR i

/-- The two right generators map to the last two standard basis vectors. -/
@[simp] theorem coordinates_right (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i : Fin 2) :
    d.coordinates eL eR (d.factorVector d.right eR i) = (0, Pi.single i 1) :=
  d.coordinateMap_right eL eR i

/-- Coordinates chosen from the two model witnesses already contained in `d`. -/
noncomputable def squareCoordinates :
    d.SquareSpace ≃ₗ[ZMod 2] ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  d.coordinates (Classical.choice d.left_model) (Classical.choice d.right_model)

/-- The intrinsic square form has the explicit two-quaternion polynomial,
without any additional choice of models in its hypotheses. -/
theorem quadraticForm_squareCoordinates (v : d.SquareSpace) :
    d.quadraticForm v =
      (d.squareCoordinates v).1 0 ^ 2 +
      (d.squareCoordinates v).1 0 * (d.squareCoordinates v).1 1 +
      (d.squareCoordinates v).1 1 ^ 2 +
      (d.squareCoordinates v).2 0 ^ 2 +
      (d.squareCoordinates v).2 0 * (d.squareCoordinates v).2 1 +
      (d.squareCoordinates v).2 1 ^ 2 :=
  d.quadraticForm_coordinates (Classical.choice d.left_model)
    (Classical.choice d.right_model) v

end Subgroup.QuaternionCentralProductData
