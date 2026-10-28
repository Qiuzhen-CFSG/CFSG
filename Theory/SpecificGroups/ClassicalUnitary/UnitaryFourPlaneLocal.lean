module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup

/-!
# The determinant-one factor of the unitary plane parabolic

Restriction to the invariant coordinate plane is the upper-left two-by-two
matrix block. The vanishing lower-left block makes restriction multiplicative;
restriction of the inverse proves that its values lie in GL₂. Its determinant
kernel is the local factor, normal relative to the plane parabolic. We retain
both the intrinsic subgroup and its embedded copy in SU₄, with a canonical
multiplicative equivalence and literal vector-action compatibility.

This is the initial local construction for Aschbacher--Smith F.1.12(I)(6),
printed pp.263–264. Identification of the kernel of restriction with the
Hermitian radical, the quotient calculation and the orthogonal block theorem
are separate obligations; none is assumed in this definition.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
variable (F : Type*) [Field F] [Finite F] (J : HermitianForm 4 F)

/-- The matrix of the action on the first two coordinates. -/
def restrictionMatrix (g : planeParabolicSU F J) : Matrix (Fin 2) (Fin 2) F :=
  !![g.val.val.val 0 0, g.val.val.val 0 1;
     g.val.val.val 1 0, g.val.val.val 1 1]

omit [Finite F] in
theorem restrictionMatrix_one : restrictionMatrix F J 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem restrictionMatrix_mul (g h : planeParabolicSU F J) :
    restrictionMatrix F J (g * h) = restrictionMatrix F J g * restrictionMatrix F J h := by
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F J h.val).mp h.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [restrictionMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h20,h30,h21,h31]

/-- Restriction is invertible, since restriction of the inverse is its inverse. -/
def restriction : planeParabolicSU F J →* GL (Fin 2) F :=
  MonoidHom.toHomUnits {
    toFun := restrictionMatrix F J
    map_one' := restrictionMatrix_one F J
    map_mul' := restrictionMatrix_mul F J }

@[simp] theorem restriction_val (g : planeParabolicSU F J) :
    (restriction F J g).val = restrictionMatrix F J g := rfl

/-- Literal restriction: applying the matrix to a vector in the coordinate plane. -/
theorem restriction_mulVec (g : planeParabolicSU F J) (v : Fin 2 → F) :
    g.val.val.val.mulVec ![v 0,v 1,0,0] =
      ![((restriction F J g).val.mulVec v) 0,
        ((restriction F J g).val.mulVec v) 1,0,0] := by
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F J g.val).mp g.property
  ext i
  fin_cases i <;>
    simp [restriction_val, restrictionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, h20,h30,h21,h31]

/-- Determinant on the invariant two-space. -/
def planeDet : planeParabolicSU F J →* Fˣ := GeneralLinearGroup.det.comp (restriction F J)

/-- The determinant-one local factor, intrinsically inside the plane parabolic. -/
def localInParabolic : Subgroup (planeParabolicSU F J) := (planeDet F J).ker

instance localInParabolic_normal : (localInParabolic F J).Normal :=
  inferInstanceAs (planeDet F J).ker.Normal

theorem mem_localInParabolic (g : planeParabolicSU F J) :
    g ∈ localInParabolic F J ↔ (restrictionMatrix F J g).det = 1 := by
  change planeDet F J g = 1 ↔ _
  exact Units.ext_iff

/-- The same local factor as a subgroup of SU₄. -/
def localFactor : Subgroup (SU F J) :=
  (localInParabolic F J).map (planeParabolicSU F J).subtype

theorem local_le_planeParabolic : localFactor F J ≤ planeParabolicSU F J :=
  Subgroup.map_subtype_le _

@[simp] theorem local_subgroupOf : (localFactor F J).subgroupOf (planeParabolicSU F J) =
    localInParabolic F J := by
  change Subgroup.comap _ (Subgroup.map _ _) = _
  apply Subgroup.comap_map_eq_self
  intro x hx
  have he : x = 1 := Subtype.ext hx
  exact he ▸ (localInParabolic F J).one_mem

/-- Normality is relative to the parabolic, not to SU₄. -/
instance local_normal_in_plane : ((localFactor F J).subgroupOf (planeParabolicSU F J)).Normal := by
  rw [local_subgroupOf]
  infer_instance

/-- Determinant-one restriction has its natural SL₂ codomain. -/
def localRestriction : localInParabolic F J →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨restrictionMatrix F J g.val, (mem_localInParabolic F J g.val).mp g.property⟩
  map_one' := Subtype.ext (restrictionMatrix_one F J)
  map_mul' g h := Subtype.ext (restrictionMatrix_mul F J g.val h.val)

/-- The intrinsic subgroup and its embedded SU₄ copy are canonically identical. -/
def localFactorEquiv : localInParabolic F J ≃* localFactor F J :=
  Subgroup.equivMapOfInjective _ _ Subtype.val_injective

/-- The restriction homomorphism on the embedded local factor. -/
def factorRestriction : localFactor F J →* SpecialLinearGroup (Fin 2) F :=
  (localRestriction F J).comp (localFactorEquiv F J).symm.toMonoidHom

/-- Ambient membership uses parabolic membership and the actual two-space determinant. -/
theorem mem_localFactor (g : SU F J) : g ∈ localFactor F J ↔
    ∃ h : g ∈ planeParabolicSU F J,
      (restrictionMatrix F J ⟨g,h⟩).det = 1 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.property, (mem_localInParabolic F J a).mp ha⟩
  · rintro ⟨h,hd⟩
    exact ⟨⟨g,h⟩, (mem_localInParabolic F J ⟨g,h⟩).mpr hd, rfl⟩

variable [CharP F 2]

/-- In characteristic two every two-subgroup of the plane parabolic lies in
its determinant-one factor: the multiplicative field has no two-torsion. -/
theorem two_subgroup_le_localFactor (S : Subgroup (SU F J))
    (hS : IsPGroup 2 S) (hSP : S ≤ planeParabolicSU F J) : S ≤ localFactor F J := by
  intro x hx
  let f : S →* Fˣ := (planeDet F J).comp (Subgroup.inclusion hSP)
  obtain ⟨k,hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hS) ⟨x,hx⟩
  have hd : f ⟨x,hx⟩ ^ (2 ^ k) = 1 := by
    simpa only [map_pow, map_one] using congrArg f hk
  have he : f ⟨x,hx⟩ = 1 := by
    apply Units.ext
    apply (iterateFrobeniusEquiv F 2 k).injective
    change (f ⟨x,hx⟩ : F) ^ (2 ^ k) = (1 : F) ^ (2 ^ k)
    simpa using congrArg Units.val hd
  apply (mem_localFactor F J x).mpr
  refine ⟨hSP hx, ?_⟩
  exact congrArg Units.val he

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
