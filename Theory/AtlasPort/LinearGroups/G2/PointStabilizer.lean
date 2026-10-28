module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/PointStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.VectorStabilizer
public import Theory.AtlasPort.LinearGroups.G2.SingularAction
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-! Split the first-point stabilizer into a nonzero scalar and a vector stabilizer; singular-vector reduction also proves projective transitivity. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion
open scoped LinearAlgebra.Projectivization
variable {K : Type*} [Field K]

theorem first_basis_ne_zero : (basisVector 0 : Carrier K) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [basisVector] at this

/-- The designated actual singular projective point. -/
def firstPoint : SingularPoints K := singularPointMk K (basisVector 0)
  first_basis_ne_zero (by simp [trace,basisVector]) (by simp [SplitOctonion.norm,basisVector])

/-- The actual stabilizer for the singular projective action. -/
abbrev pointStabilizer := MulAction.stabilizer (Model K) (firstPoint (K := K))

theorem mem_pointStabilizer_iff (g : Model K) : g ∈ pointStabilizer ↔
    ∃ a : Kˣ, g.val (basisVector 0) = a • (basisVector 0 : Carrier K) := by
  change g • firstPoint = firstPoint ↔ _
  rw [firstPoint,singularPointMk_smul]
  constructor
  · intro h
    have h := congrArg Subtype.val h
    change Projectivization.mk K (g.val (basisVector 0)) _ =
      Projectivization.mk K (basisVector 0) _ at h
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
    exact ⟨a,ha.symm⟩
  · rintro ⟨a,ha⟩
    apply Subtype.ext
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    exact ⟨a,ha.symm⟩

def lineScalar (g : pointStabilizer (K := K)) : Kˣ :=
  Units.mk0 (g.val.val (basisVector 0) 0) (by
    obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff g.val).mp g.property
    rw [ha]
    simp [basisVector,Units.smul_def])

theorem lineScalar_action (g : pointStabilizer (K := K)) :
    g.val.val (basisVector 0) = (lineScalar g : K) • (basisVector 0 : Carrier K) := by
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff g.val).mp g.property
  simp only [lineScalar,Units.val_mk0,ha]
  simp [basisVector,Units.smul_def]

theorem torus_first_basis (a b : Kˣ) :
    (torus a b).val (basisVector 0) = (a : K) • basisVector 0 := by
  ext i; fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]

def lineSection (a : Kˣ) : pointStabilizer (K := K) :=
  ⟨torus a 1,(mem_pointStabilizer_iff _).mpr ⟨a,by
    simpa only [Units.smul_def] using torus_first_basis a 1⟩⟩

def normalizePoint (g : pointStabilizer (K := K)) : fixingFirstVector (K := K) :=
  ⟨(lineSection (lineScalar g)).val⁻¹*g.val,by
    change (torus (lineScalar g) 1).val.symm (g.val.val (basisVector 0)) = _
    apply (torus (lineScalar g) 1).val.injective
    rw [LinearEquiv.apply_symm_apply,lineScalar_action,torus_first_basis]⟩

def assemblePoint (a : Kˣ) (h : fixingFirstVector (K := K)) : pointStabilizer (K := K) :=
  ⟨(lineSection a).val*h.val,(mem_pointStabilizer_iff _).mpr ⟨a,by
    change (torus a 1).val (h.val.val (basisVector 0)) = _
    rw [h.property,torus_first_basis]
    rfl⟩⟩

@[simp] theorem lineScalar_assemble (a : Kˣ) (h : fixingFirstVector (K := K)) :
    lineScalar (assemblePoint a h) = a := by
  apply Units.ext
  change (torus a 1).val (h.val.val (basisVector 0)) 0 = a.val
  rw [h.property,torus_first_basis]
  simp [basisVector]

/-- Scalar on the first vector, followed by its actual vector stabilizer. -/
def pointStabilizerEquiv : pointStabilizer (K := K) ≃ Kˣ × fixingFirstVector (K := K) where
  toFun g := (lineScalar g,normalizePoint g)
  invFun p := assemblePoint p.1 p.2
  left_inv g := by
    apply Subtype.ext
    change (lineSection (lineScalar g)).val *
      ((lineSection (lineScalar g)).val⁻¹*g.val) = g.val
    exact mul_inv_cancel_left _ _
  right_inv p := by
    apply Prod.ext
    · exact lineScalar_assemble _ _
    · change normalizePoint (assemblePoint p.1 p.2) = p.2
      apply Subtype.ext
      change (lineSection (lineScalar (assemblePoint p.1 p.2))).val⁻¹ *
        ((lineSection p.1).val*p.2.val) = p.2.val
      rw [lineScalar_assemble]
      exact inv_mul_cancel_left _ _

theorem card_pointStabilizer [Finite K] :
    Nat.card (pointStabilizer (K := K)) = (Nat.card K - 1) *
      (Nat.card K ^ 5 * Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  rw [Nat.card_congr pointStabilizerEquiv,Nat.card_prod,Nat.card_units,card_fixingFirstVector_SL2]


theorem exists_smul_firstPoint (p : SingularPoints K) :
    ∃ g : Model K, g • p = firstPoint := by
  obtain ⟨g,hg,r,hr,hx⟩ := singular_vector_reduction_first p.val.rep
    p.property.1 p.property.2 p.val.rep_nonzero
  refine ⟨g,?_⟩
  rw [← singularPointMk_rep K p,singularPointMk_smul,firstPoint]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨r,hx.symm⟩

instance singularPoints_pretransitive : MulAction.IsPretransitive (Model K) (SingularPoints K) where
  exists_smul_eq p q := by
    obtain ⟨g,hg⟩ := exists_smul_firstPoint p
    obtain ⟨h,hh⟩ := exists_smul_firstPoint q
    refine ⟨h⁻¹*g,?_⟩
    rw [SemigroupAction.mul_smul,hg,← hh,inv_smul_smul]


/-- The scalar induced on the stabilized one-dimensional subspace. -/
def lineScalarHom : pointStabilizer (K := K) →* Kˣ where
  toFun := lineScalar
  map_one' := by apply Units.ext; simp [lineScalar,basisVector]
  map_mul' g h := by
    apply Units.ext
    change g.val.val (h.val.val (basisVector 0)) 0 =
      (lineScalar g : K) * (lineScalar h : K)
    rw [lineScalar_action h,map_smul,lineScalar_action g]
    simp [basisVector,mul_comm]

theorem lineScalar_section (a : Kˣ) : lineScalarHom (lineSection a) = a := by
  apply Units.ext
  change (torus a 1).val (basisVector 0) 0 = a.val
  rw [torus_first_basis]
  simp [basisVector]

theorem lineScalarHom_surjective : Function.Surjective (lineScalarHom (K := K)) :=
  fun a => ⟨lineSection a,lineScalar_section a⟩

/-- The scalar kernel is exactly the actual vector stabilizer pulled into the point stabilizer. -/
theorem lineScalarHom_kernel : (lineScalarHom (K := K)).ker =
    (fixingFirstVector (K := K)).comap pointStabilizer.subtype := by
  ext g
  change lineScalar g = 1 ↔ g.val.val (basisVector 0) = basisVector 0
  constructor
  · intro h
    rw [lineScalar_action,h]
    simp
  · intro h
    apply Units.ext
    change g.val.val (basisVector 0) 0 = 1
    rw [h]
    simp [basisVector]
end Atlas.G2
