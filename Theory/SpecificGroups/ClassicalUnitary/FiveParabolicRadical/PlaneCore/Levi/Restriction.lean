module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Basis

/-!
# Restriction to the marked isotropic plane

Restrict an element of the exact special-unitary plane stabilizer and use
`planeEquiv` to express its action in GL₂. The corrected-basis matrix Levi is
a section, so restriction is surjective whenever a trace-one scalar is given.
The constructed unipotents fix the plane pointwise and lie in its kernel.
Exhausting that kernel is a separate matrix calculation.

Source: the plane-parabolic calculation underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- Restriction of a plane stabilizer to its invariant plane. -/
def planeLinearAction : specialStabilizer J (plane F) →* (plane F ≃ₗ[F] plane F) where
  toFun g :=
    { toFun := fun v => ⟨linearAction J g.val v,
        ((mem_specialStabilizer_iff J _ g.val).mp g.property v).mpr v.property⟩
      invFun := fun v => ⟨linearAction J g.val⁻¹ v,
        ((mem_specialStabilizer_iff J _ g.val⁻¹).mp g⁻¹.property v).mpr v.property⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change linearAction J g.val⁻¹ (linearAction J g.val v.val) = v.val
        rw [map_inv]
        exact (linearAction J g.val).symm_apply_apply v.val
      right_inv := by
        intro v
        apply Subtype.ext
        change linearAction J g.val (linearAction J g.val⁻¹ v.val) = v.val
        rw [map_inv]
        exact (linearAction J g.val).apply_symm_apply v.val
      map_add' := by intro v w; apply Subtype.ext; exact map_add (linearAction J g.val) _ _
      map_smul' := by intro a v; apply Subtype.ext; exact map_smul (linearAction J g.val) _ _ }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change linearAction J 1 v.val = v.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change linearAction J (g.val * h.val) v.val =
      linearAction J g.val (linearAction J h.val v.val)
    rw [map_mul]
    rfl

/-- The same action in the ordered coordinates `(v 0,v 2)` of the plane. -/
def planeCoordinateAction : specialStabilizer J (plane F) →*
    ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) where
  toFun g := (planeEquiv F).symm.trans ((planeLinearAction J g).trans (planeEquiv F))
  map_one' := by ext v; simp [planeLinearAction]
  map_mul' g h := by ext v; simp [map_mul]

/-- The restriction homomorphism to the actual general linear matrix group. -/
def planeRestriction : specialStabilizer J (plane F) →* GL (Fin 2) F :=
  ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F))).symm.toMonoidHom).comp
      (planeCoordinateAction J)

omit [CharP F 2] in
theorem planeRestriction_mulVec (g : specialStabilizer J (plane F)) (v : Fin 2 → F) :
    (planeRestriction J g).val *ᵥ v =
      planeEquiv F (planeLinearAction J g ((planeEquiv F).symm v)) := by
  have h := congrArg (fun e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => e v)
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F))).apply_symm_apply
        (planeCoordinateAction J g))
  exact h

/-- In the corrected basis the first two columns still parametrize the marked plane. -/
theorem planeLeviGL_plane (c : F) (A : GL (Fin 2) F) (v : Fin 2 → F) :
    (planeLeviGL J c A).val *ᵥ ((planeEquiv F).symm v).val =
      ((planeEquiv F).symm (A.val *ᵥ v)).val := by
  rw [planeLeviGL_val]
  ext i
  fin_cases i <;>
    simp [planeBasis, planeBlockMatrix, planeBasisInv, planeEquiv,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

theorem planeLeviSU_mem_stabilizer (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : GL (Fin 2) F) :
    planeLeviSU J c hc hJ A ∈ specialStabilizer J (plane F) := by
  have hmem (B : GL (Fin 2) F) (v : plane F) :
      linearAction J (planeLeviSU J c hc hJ B) v.val ∈ plane F := by
    change (planeLeviGL J c B).val *ᵥ v.val ∈ plane F
    have h := planeLeviGL_plane J c B (planeEquiv F v)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h]
    exact Subtype.property _
  rw [mem_specialStabilizer_iff]
  intro v
  constructor
  · intro hv
    have h := hmem A⁻¹ ⟨_, hv⟩
    change linearAction J (planeLeviSU J c hc hJ A⁻¹)
      (linearAction J (planeLeviSU J c hc hJ A) v) ∈ plane F at h
    rw [map_inv, map_inv] at h
    simpa using h
  · intro hv
    exact hmem A ⟨v, hv⟩

/-- An explicit Levi section into the exact SU plane stabilizer. -/
def planeLeviStabilizer (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    GL (Fin 2) F →* specialStabilizer J (plane F) :=
  (planeLeviSU J c hc hJ).codRestrict _ (planeLeviSU_mem_stabilizer J c hc hJ)

@[simp] theorem planeRestriction_section (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : GL (Fin 2) F) :
    planeRestriction J (planeLeviStabilizer J c hc hJ A) = A := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  funext i
  have h := planeRestriction_mulVec J (planeLeviStabilizer J c hc hJ A) (Pi.single j 1)
  have hh := planeLeviGL_plane J c A (Pi.single j 1)
  have he : planeLinearAction J (planeLeviStabilizer J c hc hJ A)
      ((planeEquiv F).symm (Pi.single j 1)) =
        (planeEquiv F).symm (A.val *ᵥ Pi.single j 1) := Subtype.ext hh
  rw [he, LinearEquiv.apply_symm_apply] at h
  exact congrFun h i

theorem planeRestriction_surjective (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : Function.Surjective (planeRestriction J) :=
  fun A => ⟨planeLeviStabilizer J c hc hJ A, planeRestriction_section J c hc hJ A⟩

theorem planeLeviStabilizer_injective (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : Function.Injective (planeLeviStabilizer J c hc hJ) := by
  intro A B h
  have h := congrArg (planeRestriction J) h
  simpa using h

/-- The projective image of the full matrix Levi. -/
def planeLeviParabolic (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    GL (Fin 2) F →* planeParabolic J :=
  ((project J).subgroupMap (specialStabilizer J (plane F))).comp
    (planeLeviStabilizer J c hc hJ)

/-- The already constructed unipotent group lies in the restriction kernel. -/
theorem parameters_le_ker_restriction (hJ : J.form = 1) :
    (Parameters.toStabilizer hJ).range ≤ (planeRestriction J).ker := by
  rintro _ ⟨u, rfl⟩
  change planeRestriction J (Parameters.toStabilizer hJ u) = 1
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [planeRestriction_mulVec, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have h : planeLinearAction J (Parameters.toStabilizer hJ u)
      ((planeEquiv F).symm (Pi.single j 1)) = (planeEquiv F).symm (Pi.single j 1) := by
    apply Subtype.ext
    exact Parameters.toSU_fixes_plane hJ u _ (Subtype.property _)
  rw [h, LinearEquiv.apply_symm_apply]


omit [CharP F 2] in
/-- The restriction kernel is exactly the pointwise fixer of the marked plane. -/
theorem planeRestriction_eq_one_iff (g : specialStabilizer J (plane F)) :
    planeRestriction J g = 1 ↔
      ∀ v : plane F, linearAction J g.val v.val = v.val := by
  constructor
  · intro hg v
    have he := planeRestriction_mulVec J g (planeEquiv F v)
    rw [hg, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec,
      LinearEquiv.symm_apply_apply] at he
    have hf := (planeEquiv F).injective he.symm
    exact congrArg Subtype.val hf
  · intro hg
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [planeRestriction_mulVec, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have he : planeLinearAction J g ((planeEquiv F).symm (Pi.single j 1)) =
        (planeEquiv F).symm (Pi.single j 1) := Subtype.ext (hg _)
    rw [he, LinearEquiv.apply_symm_apply]

/-- The special-linear Levi inside the exact SU plane stabilizer. -/
def planeSLStabilizer (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F →* specialStabilizer J (plane F) :=
  (planeLeviStabilizer J c hc hJ).comp planeSLtoGL

/-- Its actual image in the projective plane parabolic. -/
def planeSLParabolic (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F →* planeParabolic J :=
  (planeLeviParabolic J c hc hJ).comp planeSLtoGL

/-- Conjugating the hyperbolic basis does not change scalar matrices. -/
theorem planeLeviGL_eq_scalar_iff (c : F) (A : GL (Fin 2) F) (a : Fˣ) :
    planeLeviGL J c A = GeneralLinearGroup.scalar (Fin 5) a ↔
      planeBlockGL J A = GeneralLinearGroup.scalar (Fin 5) a := by
  have hs : MulAut.conj (planeBasisGL c) (GeneralLinearGroup.scalar (Fin 5) a) =
      GeneralLinearGroup.scalar (Fin 5) a := by
    change planeBasisGL c * GeneralLinearGroup.scalar (Fin 5) a * (planeBasisGL c)⁻¹ = _
    rw [← GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]
  change MulAut.conj (planeBasisGL c) (planeBlockGL J A) = _ ↔ _
  constructor
  · intro h
    exact (MulAut.conj (planeBasisGL c)).injective (h.trans hs.symm)
  · intro h
    rw [h, hs]

/-- The special-linear Levi has no projective scalar kernel. -/
theorem planeSLParabolic_injective (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : Function.Injective (planeSLParabolic J c hc hJ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro A hA
  have hp : project J (planeLeviSU J c hc hJ (planeSLtoGL A)) = 1 :=
    congrArg Subtype.val hA
  have hs : ProjGenLinGroup.mk (planeLeviGL J c (planeSLtoGL A)) = 1 :=
    congrArg Subtype.val hp
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨a, ha⟩ := hs
  have hb := (planeLeviGL_eq_scalar_iff J c (planeSLtoGL A) a).mp ha.symm
  have hm := congrArg (fun B : GL (Fin 5) F => B.val 2 2) hb
  have haone : a = 1 := by
    apply Units.ext
    simpa [planeBlockGL, planeBlockMatrix, planeMiddleScalar] using hm.symm
  subst a
  have hunit : planeLeviStabilizer J c hc hJ (planeSLtoGL A) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change planeLeviGL J c (planeSLtoGL A) = 1
    simpa using ha.symm
  have he := congrArg (planeRestriction J) hunit
  have hgl : planeSLtoGL A = 1 := by simpa using he
  apply Subtype.ext
  exact congrArg Units.val hgl

/-- The subgroup generated by the unipotents and the special-linear Levi.
Identification with the solvable residual requires a separate perfection proof. -/
def planeRadicalLevi (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Subgroup (planeParabolic J) :=
  projectiveUnipotent J hJ ⊔ (planeSLParabolic J c hc hJ).range

end Theory.SpecificGroups.UnitaryFive.PlaneCore
