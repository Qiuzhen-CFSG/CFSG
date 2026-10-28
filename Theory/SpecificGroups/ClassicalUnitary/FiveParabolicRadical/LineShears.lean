module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Mathlib.GroupTheory.PGroup

/-!
# A normal two-subgroup in the unitary-five line parabolic

Shears fixing a subspace pointwise and acting trivially on its quotient form
an elementary two-subgroup in characteristic two. They are normalized by the
subspace stabilizer. Apply this construction inside the special unitary line
stabilizer, then take its image in the projective parabolic.

The interchange of coordinates zero and one is a unitary shear along the
chosen isotropic line. Its off-diagonal entry shows that it is not scalar,
so its projective image witnesses nontriviality, including over the field
of order four. No restriction excluding the unitary parameter `q = 2` is used.

This constructs a subgroup of the unipotent radical, not an identification
of the entire radical or the canonical two-core.

Source: the isotropic-line transvection construction in classical unitary
groups; Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12 and its proof, printed pp. 263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix

namespace Theory.SpecificGroups.UnitaryFive

variable {F V G : Type*} [Field F] [AddCommGroup V] [Module F V] [Group G]

/-- Elements acting trivially on a subspace and its quotient. -/
def shearSubgroup (ρ : G →* (V ≃ₗ[F] V)) (W : Submodule F V) : Subgroup G where
  carrier := {g | (∀ v ∈ W, ρ g v = v) ∧ ∀ v, ρ g v - v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    constructor
    · intro v hv
      simp only [map_mul, LinearEquiv.mul_apply, hb v hv, ha v hv]
    · intro v
      have h := ha (ρ b v - v) (hb' v)
      rw [map_sub] at h
      have he : ρ (a * b) v - v = (ρ b v - v) + (ρ a v - v) := by
        simp only [map_mul, LinearEquiv.mul_apply]
        rw [← h]
        abel
      rw [he]
      exact W.add_mem (hb' v) (ha' v)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    constructor
    · intro v hv
      apply (ρ a).injective
      simpa using (ha v hv).symm
    · intro v
      have h := W.neg_mem (ha' (ρ a⁻¹ v))
      simpa using h

theorem shearSubgroup_normal (ρ : G →* (V ≃ₗ[F] V)) (W : Submodule F V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) : (shearSubgroup ρ W).Normal := by
  constructor
  rintro a ⟨ha, ha'⟩ g
  constructor
  · intro v hv
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [ha _ (hW g⁻¹ v hv)]
    simp
  · intro v
    have h := hW g _ (ha' (ρ g⁻¹ v))
    simpa using h

theorem shearSubgroup_isPGroup [CharP F 2]
    (ρ : G →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ) (W : Submodule F V) :
    IsPGroup 2 (shearSubgroup ρ W) := by
  intro a
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply hρ
  ext v
  have h := a.property.1 (ρ a.val v - v) (a.property.2 v)
  rw [map_sub] at h
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hadd (w : V) : w + w = 0 := by
    simpa [two_smul] using congrArg (fun c : F => c • w) htwo
  have he : ρ a.val (ρ a.val v) = v := by
    have : ρ a.val (ρ a.val v) = (ρ a.val v - v) + ρ a.val v :=
      (sub_eq_iff_eq_add).mp h
    rw [this]
    have : (ρ a.val v - v) + ρ a.val v = (ρ a.val v + ρ a.val v) - v := by abel
    rw [this, hadd, zero_sub]
    exact neg_eq_iff_add_eq_zero.mpr (hadd v)
  simpa [pow_two] using he

end Theory.SpecificGroups.UnitaryFive

namespace Theory.SpecificGroups.UnitaryFive

variable {F : Type*} [Field F]

/-- Interchange of the first two coordinates, a unitary transvection in characteristic two. -/
def lineSwapMatrix : Matrix (Fin 5) (Fin 5) F :=
  (1 : Matrix (Fin 5) (Fin 5) F).submatrix (Equiv.swap 0 1) id

theorem lineSwapMatrix_sq : (lineSwapMatrix : Matrix (Fin 5) (Fin 5) F) * lineSwapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Equiv.swap_apply_def]

def lineSwapGL : GL (Fin 5) F :=
  ⟨lineSwapMatrix, lineSwapMatrix, lineSwapMatrix_sq, lineSwapMatrix_sq⟩

variable [CharP F 2]

theorem lineSwapMatrix_det : (lineSwapMatrix : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  rw [lineSwapMatrix, Matrix.det_permute]
  simp [CharTwo.neg_eq]

set_option maxRecDepth 2048 in
def lineSwap (J : HermitianForm 5 F) (hJ : J.form = 1) : J.specialSubgroup := by
  refine ⟨lineSwapGL, ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · have hc : J.conjTranspose lineSwapMatrix = lineSwapMatrix := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HermitianForm.conjTranspose, lineSwapMatrix, Matrix.one_apply, Equiv.swap_apply_def]
    change J.conjTranspose lineSwapMatrix * J.form * lineSwapMatrix = J.form
    rw [hJ, hc, mul_one, lineSwapMatrix_sq]
  · exact Units.ext (lineSwapMatrix_det (F := F))

theorem lineSwap_apply (J : HermitianForm 5 F) (hJ : J.form = 1) (v : Fin 5 → F) :
    linearAction J (lineSwap J hJ) v = ![v 1, v 0, v 2, v 3, v 4] := by
  change lineSwapMatrix *ᵥ v = _
  ext i
  fin_cases i <;>
    simp [lineSwapMatrix, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Equiv.swap_apply_def]

end Theory.SpecificGroups.UnitaryFive

namespace Theory.SpecificGroups.UnitaryFive

variable {F : Type*} [Field F] [CharP F 2]

def lineStabilizerAction (J : HermitianForm 5 F) :
    specialStabilizer J (line F) →* ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
  (linearAction J).comp (specialStabilizer J (line F)).subtype

omit [CharP F 2] in
theorem lineStabilizerAction_injective (J : HermitianForm 5 F) :
    Function.Injective (lineStabilizerAction J) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)).injective
  exact h

def lineShears (J : HermitianForm 5 F) : Subgroup (specialStabilizer J (line F)) :=
  shearSubgroup (lineStabilizerAction J) (line F)

instance lineShears_normal (J : HermitianForm 5 F) : (lineShears J).Normal := by
  apply shearSubgroup_normal
  intro g v hv
  exact ((mem_specialStabilizer_iff J (line F) g.val).mp g.property v).mpr hv

theorem lineShears_isPGroup (J : HermitianForm 5 F) : IsPGroup 2 (lineShears J) :=
  shearSubgroup_isPGroup _ (lineStabilizerAction_injective J) _

theorem lineSwap_mem_stabilizer (J : HermitianForm 5 F) (hJ : J.form = 1) :
    lineSwap J hJ ∈ specialStabilizer J (line F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  change linearAction J (lineSwap J hJ) v ∈ line F ↔ v ∈ line F
  rw [lineSwap_apply]
  change (v 0 = v 1 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0) ↔
    (v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0)
  rw [eq_comm (a := v 0)]

def lineSwapStabilizer (J : HermitianForm 5 F) (hJ : J.form = 1) :
    specialStabilizer J (line F) := ⟨lineSwap J hJ, lineSwap_mem_stabilizer J hJ⟩

theorem lineSwap_mem_shears (J : HermitianForm 5 F) (hJ : J.form = 1) :
    lineSwapStabilizer J hJ ∈ lineShears J := by
  constructor
  · intro v hv
    change linearAction J (lineSwap J hJ) v = v
    rw [lineSwap_apply]
    change v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 at hv
    ext i
    fin_cases i <;> simp [hv.1]
  · intro v
    change linearAction J (lineSwap J hJ) v - v ∈ line F
    rw [lineSwap_apply]
    change v 0 - v 1 = v 1 - v 0 ∧ v 2 - v 2 = 0 ∧ v 3 - v 3 = 0 ∧ v 4 - v 4 = 0
    simp [CharTwo.sub_eq_add, add_comm]

theorem project_lineSwap_ne_one (J : HermitianForm 5 F) (hJ : J.form = 1) :
    project J (lineSwap J hJ) ≠ 1 := by
  intro h
  have hs : Matrix.ProjGenLinGroup.mk (lineSwap J hJ).val = 1 := congrArg Subtype.val h
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  have he := congrArg (fun A : GL (Fin 5) F => (A : Matrix (Fin 5) (Fin 5) F) 0 1) hu
  simp [lineSwap, lineSwapGL, lineSwapMatrix, Matrix.one_apply] at he

/-- A concrete normal elementary two-subgroup in the projective line parabolic. -/
def projectiveLineShears (J : HermitianForm 5 F) : Subgroup (lineParabolic J) :=
  (lineShears J).map ((project J).subgroupMap (specialStabilizer J (line F)))

instance projectiveLineShears_normal (J : HermitianForm 5 F) :
    (projectiveLineShears J).Normal :=
  (lineShears_normal J).map _ ((project J).subgroupMap_surjective _)

theorem projectiveLineShears_isPGroup (J : HermitianForm 5 F) :
    IsPGroup 2 (projectiveLineShears J) :=
  (lineShears_isPGroup J).of_surjective _
    (((project J).subgroupMap (specialStabilizer J (line F))).subgroupMap_surjective _)

theorem projectiveLineShears_ne_bot (J : HermitianForm 5 F) (hJ : J.form = 1) :
    projectiveLineShears J ≠ ⊥ := by
  intro h
  have hm : ((project J).subgroupMap (specialStabilizer J (line F))) (lineSwapStabilizer J hJ) ∈
      projectiveLineShears J :=
    ⟨lineSwapStabilizer J hJ, lineSwap_mem_shears J hJ, rfl⟩
  rw [h] at hm
  have he : ((project J).subgroupMap (specialStabilizer J (line F))) (lineSwapStabilizer J hJ) = 1 :=
    hm
  exact project_lineSwap_ne_one J hJ (congrArg Subtype.val he)

end Theory.SpecificGroups.UnitaryFive
