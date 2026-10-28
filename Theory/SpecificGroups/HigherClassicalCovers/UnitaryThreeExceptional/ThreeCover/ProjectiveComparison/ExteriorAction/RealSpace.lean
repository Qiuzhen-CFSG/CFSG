module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorOrthogonal

/-!
# The real exterior space for the identity Hermitian form

The literal SU₄(3) compound action commutes with the conjugate Hodge involution
`(w₀,…,w₅) ↦ (conj(w₅),-conj(w₄),conj(w₃),conj(w₂),-conj(w₁),conj(w₀))`.
Its fixed space is exactly the published bivector embedding of F₃⁶.
The Pfaffian becomes the sum of six squares and is preserved by this action.

The proof compares the Pfaffian polarization with the Hermitian pairing.
It adapts the argument of `OddSixComparison/Geometry/SignedExterior.lean`
to the identity Gram matrix, retaining the original cube conjugation.
The compound matrix and Pfaffian identities are the attributed ATLAS port
(copyright Gerald Höhn and ATLAS contributors; see LICENSES/ATLAS.txt).
Source: the classical-group constructions of GLS3 §2.7. This supplies the
geometric action used in the concrete cover comparison for I.1.4(5), p.408.

-/

public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
open Matrix Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary

abbrev SU4 := (UnitaryFourThree.form 4).specialSubgroup
local notation "E" => FiniteField.Nine

private def specialExterior {K : Type} [Field K]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 4 K) :
    J.specialSubgroup →* (Six K ≃ₗ[K] Six K) where
  toFun g := Atlas.Order20160A8.Exterior.exteriorAction
    ⟨g.val.val, congrArg Units.val (((J.mem_specialSubgroup_iff g.val).mp g.property).2)⟩
  map_one' := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : Six K →ₗ[K] Six K => f w) exteriorMap_one
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : Six K →ₗ[K] Six K => f w)
      (exteriorMap_mul g.val.val h.val.val)

private theorem specialExterior_apply {K : Type} [Field K]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 4 K)
    (g : J.specialSubgroup) (w : Six K) :
    specialExterior J g w = exteriorMap g.val.val w := rfl

private theorem specialExterior_pfaffian {K : Type} [Field K]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 4 K)
    (g : J.specialSubgroup) (w : Six K) :
    pfaffian (specialExterior J g w) = pfaffian w := by
  have hd : g.val.val.det = 1 :=
    congrArg Units.val (((J.mem_specialSubgroup_iff g.val).mp g.property).2)
  change pfaffian (exteriorMap g.val.val w) = _
  rw [pfaffian_exteriorMap, hd, one_mul]

private theorem special_det {K : Type} [Field K]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 4 K) (g : J.specialSubgroup) :
    g.val.val.det = 1 :=
  congrArg Units.val (((J.mem_specialSubgroup_iff g.val).mp g.property).2)

theorem exteriorSU_det (g : SU4) : g.val.val.det = 1 :=
  special_det (UnitaryFourThree.form 4) g

def exteriorSU : SU4 →* (Six E ≃ₗ[E] Six E) := specialExterior (UnitaryFourThree.form 4)

@[simp] theorem exteriorSU_apply (g : SU4) (w : Six E) :
    exteriorSU g w = exteriorMap g.val.val w :=
  specialExterior_apply (UnitaryFourThree.form 4) g w

theorem exteriorSU_pfaffian (g : SU4) (w : Six E) :
    pfaffian (exteriorSU g w) = pfaffian w :=
  specialExterior_pfaffian (UnitaryFourThree.form 4) g w

private theorem exterior_transpose (A : Matrix (Fin 4) (Fin 4) E) (w z : Six E) :
    dotProduct (exteriorMap A w) z = dotProduct w (exteriorMap A.transpose z) := by
  have ht : compound A.transpose = (compound A).transpose := by
    funext i j
    simp [compound, Matrix.transpose_apply, mul_comm]
  simp only [exteriorMap, Matrix.toLin'_apply, ht]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem exterior_conjugate (A : Matrix (Fin 4) (Fin 4) E) (w : Six E) :
    (fun i => star (exteriorMap A w i)) = exteriorMap (A.map star) (fun i => star (w i)) := by
  funext i
  simp [exteriorMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, compound, mul_comm]

private def pairing (w z : Six E) : E :=
  w 0 * z 5 - w 1 * z 4 + w 2 * z 3 + w 3 * z 2 - w 4 * z 1 + w 5 * z 0

private theorem pairing_polar (w z : Six E) :
    pairing w z = pfaffian (w + z) - pfaffian w - pfaffian z := by
  simp only [pairing, pfaffian_apply, Pi.add_apply]
  ring

private theorem pairing_ext {w z : Six E}
    (h : ∀ t, pairing w t = pairing z t) : w = z := by
  funext i
  fin_cases i
  · simpa [pairing] using h (Pi.single 5 1)
  · simpa [pairing] using h (Pi.single 4 1)
  · simpa [pairing] using h (Pi.single 3 1)
  · simpa [pairing] using h (Pi.single 2 1)
  · simpa [pairing] using h (Pi.single 1 1)
  · simpa [pairing] using h (Pi.single 0 1)

def realTwist (w : Six E) : Six E :=
  ![star (w 5), -star (w 4), star (w 3), star (w 2), -star (w 1), star (w 0)]

private theorem pairing_twist (w z : Six E) :
    pairing (realTwist w) z = dotProduct (fun i => star (w i)) z := by
  simp [pairing, realTwist, dotProduct, Fin.sum_univ_succ]
  ring

private theorem exterior_pairing (g : SU4) (w z : Six E) :
    pairing (exteriorSU g w) (exteriorSU g z) = pairing w z := by
  rw [pairing_polar, ← map_add, exteriorSU_pfaffian, exteriorSU_pfaffian,
    exteriorSU_pfaffian, ← pairing_polar]

private theorem exterior_hermitian (g : SU4) (w z : Six E) :
    pairing (realTwist (exteriorSU g w)) (exteriorSU g z) =
      pairing (realTwist w) z := by
  rw [pairing_twist, pairing_twist, exteriorSU_apply, exteriorSU_apply,
    exterior_conjugate, exterior_transpose]
  have hu : (g.val.val.map star).transpose * g.val.val = 1 := by
    have h := (((UnitaryFourThree.form 4).mem_specialSubgroup_iff g.val).mp g.property).1
    change (g.val.val.map star).transpose * 1 * g.val.val = 1 at h
    simpa only [mul_one] using h
  have he := congrArg (fun A => exteriorMap A z) hu
  simp only [exteriorMap_mul, LinearMap.comp_apply, exteriorMap_one,
    LinearMap.id_apply] at he
  rw [he]

theorem realTwist_exterior (g : SU4) (w : Six E) :
    realTwist (exteriorSU g w) = exteriorSU g (realTwist w) := by
  apply pairing_ext
  intro z
  obtain ⟨t, rfl⟩ := (exteriorSU g).surjective z
  rw [exterior_hermitian, exterior_pairing]

theorem realTwist_bivector (v : Vector) : realTwist (bivector v) = bivector v := by
  funext i
  fin_cases i <;> simp [realTwist, bivector]

def realCoordinates (w : Six E) : Vector :=
  ![(w 0).re, (w 0).im, (w 1).re, (w 1).im, (w 2).re, (w 2).im]

theorem bivector_realCoordinates {w : Six E} (h : realTwist w = w) :
    bivector (realCoordinates w) = w := by
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  change star (w 2) = w 3 at h3
  change -star (w 1) = w 4 at h4
  change star (w 0) = w 5 at h5
  funext i
  fin_cases i <;> simp [bivector, pair, realCoordinates, h3, h4, h5]

theorem exterior_bivector (g : SU4) (v : Vector) :
    bivector (realCoordinates (exteriorSU g (bivector v))) = exteriorSU g (bivector v) := by
  apply bivector_realCoordinates
  rw [realTwist_exterior, realTwist_bivector]

theorem exterior_norm (g : SU4) (v : Vector) :
    norm (realCoordinates (exteriorSU g (bivector v))) = norm v := by
  apply (algebraMap (ZMod 3) E).injective
  rw [← pfaffian_bivector, exterior_bivector, exteriorSU_pfaffian, pfaffian_bivector]


end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
