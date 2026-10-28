/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianProjectiveAxisRigidity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianFrameMonomial
public import Theory.AtlasPort.Janko2.Algebra.IcosianScalarCenter

/-!
# IcosianProjectiveAxisRigidity

An element fixing all coordinate axes is diagonal. Fixed projective lines compare its
coefficients and force commutation with their quaternionic ratios.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianProjectiveAxisRigidity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Pointwise

theorem icosian_fix_axes_mem_frame (f : icosianHermitianGroup)
    (hf : ∀ i,f • icosianAxisPoint i=icosianAxisPoint i) :
    f∈icosianCoordinateFrameStabilizer := by
  change f • icosianCoordinateFrame=icosianCoordinateFrame
  apply Set.Subset.antisymm
  · rintro x ⟨y,⟨i,rfl⟩,rfl⟩
    change f • icosianAxisPoint i∈icosianCoordinateFrame
    rw [hf]
    exact ⟨i,rfl⟩
  · rintro x ⟨i,rfl⟩
    exact ⟨icosianAxisPoint i,⟨i,rfl⟩,hf i⟩

theorem icosian_diagonal_of_fix_axes (f : icosianHermitianGroup)
    (hf : ∀ i,f • icosianAxisPoint i=icosianAxisPoint i) :
    ∃ q : Fin 3 → IcosianQuaternion,
      (∀ i,IsIcosian (q i) ∧ icosianNorm (q i)=1) ∧
      ∀ x i,f.val x i=q i*x i := by
  let g : icosianCoordinateFrameStabilizer := ⟨f,icosian_fix_axes_mem_frame f hf⟩
  have hp : icosianFramePermutation g=1 := by
    apply Equiv.ext
    intro i
    apply icosianAxisPoint_injective
    exact (icosianFramePermutation_spec g i).symm.trans (hf i)
  refine ⟨icosianFrameCoefficient g,fun i =>
    ⟨icosianFrameCoefficient_integral g i,icosianFrameCoefficient_norm g i⟩,?_⟩
  intro x i
  have h := icosianFrameMonomial_apply g x i
  rw [icosianFrameMonomial_representation g,hp] at h
  exact h

theorem icosian_projective_fixed_scalar (f : icosianHermitianGroup)
    (x : IcosianRationalCoordinates) (hx : x≠0)
    (hf : f • Projectivization.mk IcosianQuaternionᵐᵒᵖ x hx=
      Projectivization.mk IcosianQuaternionᵐᵒᵖ x hx) :
    ∃ a : IcosianQuaternion,∀ i,f.val x i=x i*a := by
  rw [Projectivization.smul_mk] at hf
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp hf
  exact ⟨MulOpposite.unop a,fun i => (congrFun ha i).symm⟩

/-- Fixing a line with two equal nonzero coordinates equates the corresponding
diagonal coefficients; no finite geometry or group order is assumed. -/
theorem icosian_diagonal_coeff_eq (f : icosianHermitianGroup)
    (q : Fin 3 → IcosianQuaternion) (hq : ∀ x i,f.val x i=q i*x i)
    (x : IcosianRationalCoordinates) (hx : x≠0) (i j : Fin 3)
    (hij : x i=x j) (hi : x i≠0)
    (hf : f • Projectivization.mk IcosianQuaternionᵐᵒᵖ x hx=
      Projectivization.mk IcosianQuaternionᵐᵒᵖ x hx) : q i=q j := by
  obtain ⟨a,ha⟩ := icosian_projective_fixed_scalar f x hx hf
  have h1 := ha i
  have h2 := ha j
  rw [hq] at h1 h2
  rw [← hij] at h2
  exact mul_right_cancel₀ hi (h1.trans h2.symm)

theorem icosian_common_scalar_commutes_ratio (f : icosianHermitianGroup)
    (q : IcosianQuaternion) (hq : ∀ x i,f.val x i=q*x i)
    (x : IcosianRationalCoordinates) (hx : x≠0) (i j : Fin 3) (hj : x j≠0)
    (hf : f • Projectivization.mk IcosianQuaternionᵐᵒᵖ x hx=
      Projectivization.mk IcosianQuaternionᵐᵒᵖ x hx) :
    q*(x i*(x j)⁻¹)=(x i*(x j)⁻¹)*q := by
  obtain ⟨a,ha⟩ := icosian_projective_fixed_scalar f x hx hf
  have h1 := ha i
  have h2 := ha j
  rw [hq] at h1 h2
  apply mul_right_cancel₀ hj
  calc
    _=q*x i := by simp [mul_assoc,hj]
    _=x i*a := h1
    _=(x i*(x j)⁻¹)*(q*x j) := by rw [h2]; simp [mul_assoc,hj]
    _=_ := by simp only [mul_assoc]

end Atlas.Conway
