/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianFrameCoordinates.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianQuaternionLines
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisIntersection
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialAction

/-!
# IcosianFrameCoordinates

A full coordinate-frame stabilizer element permutes axes and has integral norm-one
coefficients. Axis images and lattice intersections recover these coordinates.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianFrameCoordinates.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Pointwise BigOperators Quaternion QuadraticAlgebra

theorem icosianFrame_axis_image (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    ∃ j : Fin 3, f.val • icosianAxisPoint i=icosianAxisPoint j := by
  have hf := f.property
  change f.val • icosianCoordinateFrame=icosianCoordinateFrame at hf
  have hm : f.val • icosianAxisPoint i∈f.val • icosianCoordinateFrame :=
    ⟨icosianAxisPoint i,⟨i,rfl⟩,rfl⟩
  rw [hf] at hm
  obtain ⟨j,hj⟩ := hm
  exact ⟨j,hj.symm⟩

def icosianFramePermutation (f : icosianCoordinateFrameStabilizer) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (fun i => (icosianFrame_axis_image f i).choose) (by
    have hi : Function.Injective (fun i => (icosianFrame_axis_image f i).choose) := by
      intro i j h
      dsimp only at h
      apply icosianAxisPoint_injective
      apply (MulAction.injective f.val)
      change f.val • icosianAxisPoint i=f.val • icosianAxisPoint j
      rw [(icosianFrame_axis_image f i).choose_spec,
        (icosianFrame_axis_image f j).choose_spec,h]
    exact ⟨hi,Finite.surjective_of_injective hi⟩)

theorem icosianFramePermutation_spec (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    f.val • icosianAxisPoint i=icosianAxisPoint (icosianFramePermutation f i) :=
  (icosianFrame_axis_image f i).choose_spec

theorem icosianFrame_axis_coefficient (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    ∃ a : IcosianQuaternion,
      f.val.val (Pi.single i 1)=Pi.single (icosianFramePermutation f i) a := by
  have h := icosianFramePermutation_spec f i
  simp only [icosianAxisPoint,Projectivization.smul_mk] at h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h
  refine ⟨MulOpposite.unop a,?_⟩
  change a • Pi.single (icosianFramePermutation f i) 1=f.val.val (Pi.single i 1) at ha
  rw [← ha]
  funext j
  by_cases hj : j=icosianFramePermutation f i <;>
    simp [hj,MulOpposite.smul_eq_mul_unop]

def icosianFrameCoefficient (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    IcosianQuaternion := (icosianFrame_axis_coefficient f i).choose

theorem icosianFrameCoefficient_spec (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    f.val.val (Pi.single i 1)=
      Pi.single (icosianFramePermutation f i) (icosianFrameCoefficient f i) :=
  (icosianFrame_axis_coefficient f i).choose_spec

theorem icosianFrameCoefficient_integral (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    IsIcosian (icosianFrameCoefficient f i) := by
  have hL : Pi.single i (2 : IcosianQuaternion)∈rationalIcosianLattice := by
    rw [icosianAxisIntersection]
    exact ⟨1,by simp⟩
  have hmap := (f.val.property.2.2 _).mp hL
  have hs : Pi.single i (2 : IcosianQuaternion)=(2 : ℚ) • (Pi.single i (1 : IcosianQuaternion) : IcosianRationalCoordinates) := by
    funext j; by_cases hj : j=i <;> simp [hj]
  rw [hs,map_smul,icosianFrameCoefficient_spec] at hmap
  have ht : (2 : ℚ) • (Pi.single (icosianFramePermutation f i) (icosianFrameCoefficient f i) : IcosianRationalCoordinates)=
      Pi.single (icosianFramePermutation f i) (2*icosianFrameCoefficient f i) := by
    funext j; by_cases hj : j=icosianFramePermutation f i <;>
      simp [hj,two_smul,two_mul]
  rw [ht,icosianAxisIntersection] at hmap
  obtain ⟨u,hu⟩ := hmap
  have hval : icosianFrameCoefficient f i=u.val :=
    mul_left_cancel₀ (by intro h; have hh := congrArg (fun z : IcosianQuaternion => z.re.re) h; norm_num [QuaternionAlgebra.re_ofNat] at hh : (2 : IcosianQuaternion)≠0) hu
  rw [hval]
  exact u.property

theorem icosianFrameCoefficient_norm (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    icosianNorm (icosianFrameCoefficient f i)=1 := by
  have h := f.val.property.2.1 (Pi.single i 1) (Pi.single i 1)
  rw [icosianFrameCoefficient_spec] at h
  have hn (j : Fin 3) (a : IcosianQuaternion) :
      icosianHermitian (Pi.single j a) (Pi.single j a)=
        (1/2 : ℚ) • (icosianNorm a : IcosianQuaternion) := by
    fin_cases j <;> simp [icosianHermitian,Fin.sum_univ_succ,
      Quaternion.star_mul_self,icosianNorm]
  rw [hn,hn] at h
  have hh := congrArg (fun z : IcosianQuaternion => z.re) h
  change (1/2 : ℚ) • icosianNorm (icosianFrameCoefficient f i)=
    (1/2 : ℚ) • icosianNorm 1 at hh
  have he := (smul_right_injective _ (by norm_num : (1/2 : ℚ)≠0)) hh
  simpa [icosianNorm] using he

end Atlas.Conway
