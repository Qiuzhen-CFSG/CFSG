module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry.Chart

/-!
# The exterior action on the original minus-six form

The signed chart identifies its image with the fixed space of the signed
Frobenius involution. Commutation of the actual SU₄ compound action with
that involution therefore supplies a unique preimage for each acted-on
vector. Injectivity of the chart proves linearity and the group laws;
Pfaffian preservation proves that the resulting maps are isometries of
the original minus quadratic form.

The construction provides every field of `ExteriorRealization` and its
literal `SignedCoordinates` witness. No descent, transport, image,
recognition, or model-simplicity hypothesis remains. This is the geometry
used in the dimension-six reduction of Aschbacher–Smith A.2.17, printed
pp.38–39, with matrix conventions from GLS3 §2.7.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison.Geometry
open Atlas.Order20160A8.Bivectors
variable (p n : ℕ) [Fact p.Prime] [NeZero n]
variable (F : Type) [Field F] [Finite F] (hcard : Nat.card F = p ^ n)

local notation "C" => coordinates p n F hcard

theorem exterior_mem_range (g : SU p n) (v : Space F 2) :
    exterior p n g (C v) ∈ Set.range C := by
  apply (mem_range_coordinates_iff p n F hcard _).mpr
  rw [signedTwist_exterior, coordinates_fixed]

private def descendedFun (g : SU p n) (v : Space F 2) : Space F 2 :=
  (exterior_mem_range p n F hcard g v).choose

private theorem coordinates_descendedFun (g : SU p n) (v : Space F 2) :
    C (descendedFun p n F hcard g v) = exterior p n g (C v) :=
  (exterior_mem_range p n F hcard g v).choose_spec

private def descendedMap (g : SU p n) : Space F 2 →ₗ[F] Space F 2 where
  toFun := descendedFun p n F hcard g
  map_add' v w := by
    apply coordinates_injective p n F hcard
    rw [map_add, coordinates_descendedFun, coordinates_descendedFun,
      coordinates_descendedFun, map_add, map_add]
  map_smul' c v := by
    apply coordinates_injective p n F hcard
    change C (descendedFun p n F hcard g (c • v)) =
      C (c • descendedFun p n F hcard g v)
    rw [coordinates_descendedFun, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      coordinates_descendedFun, map_smul]

private def descendedEquiv (g : SU p n) : Space F 2 ≃ₗ[F] Space F 2 where
  __ := descendedMap p n F hcard g
  invFun := descendedMap p n F hcard g⁻¹
  left_inv v := by
    apply coordinates_injective p n F hcard
    change C (descendedFun p n F hcard g⁻¹ (descendedFun p n F hcard g v)) = C v
    rw [coordinates_descendedFun, coordinates_descendedFun]
    change (exterior p n g⁻¹ * exterior p n g) (C v) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    apply coordinates_injective p n F hcard
    change C (descendedFun p n F hcard g (descendedFun p n F hcard g⁻¹ v)) = C v
    rw [coordinates_descendedFun, coordinates_descendedFun]
    change (exterior p n g * exterior p n g⁻¹) (C v) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

def orthogonalAction : SU p n →* FullOrthogonal F where
  toFun g := ⟨descendedEquiv p n F hcard g, by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    apply (coefficient p n F hcard).injective
    rw [← coordinates_quadratic, ← coordinates_quadratic]
    exact (congrArg pfaffian (coordinates_descendedFun p n F hcard g v)).trans
      (exterior_pfaffian p n g (C v))⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply coordinates_injective p n F hcard
    change C (descendedFun p n F hcard 1 v) = C v
    rw [coordinates_descendedFun, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply coordinates_injective p n F hcard
    change C (descendedFun p n F hcard (g * h) v) =
      C (descendedFun p n F hcard g (descendedFun p n F hcard h v))
    rw [coordinates_descendedFun, coordinates_descendedFun, coordinates_descendedFun, map_mul]
    rfl

theorem orthogonalAction_intertwines (g : SU p n) (v : Space F 2) :
    C ((orthogonalAction p n F hcard g).val v) = exteriorMap g.val.val (C v) :=
  coordinates_descendedFun p n F hcard g v

@[expose] def realization : ExteriorRealization F (Extension p n) (unitaryForm p n) where
  coefficient := coefficient p n F hcard
  coordinates := C
  coordinates_injective := coordinates_injective p n F hcard
  coordinates_span := coordinates_span p n F hcard
  quadratic := coordinates_quadratic p n F hcard
  action := orthogonalAction p n F hcard
  intertwines := orthogonalAction_intertwines p n F hcard

def signedCoordinates : SignedCoordinates (realization p n F hcard) where
  root := root p n F hcard
  coefficient_fixed := coefficient_fixed p n F hcard
  root_equation := root_equation p n F hcard
  root_conjugate := root_conjugate p n F hcard
  skew_ne_zero := skew_ne_zero p n F hcard
  coordinates_eq _ := rfl

end ClassicalOrthogonal.Minus.OddSixComparison.Geometry
