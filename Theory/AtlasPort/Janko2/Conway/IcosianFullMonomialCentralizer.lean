/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianFullMonomialCentralizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialCentralizer
public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveModel

/-!
# IcosianFullMonomialCentralizer

Commutation with the full coordinate-frame stabilizer forces a golden-field scalar.
The exact projective kernel then identifies the center of the full Hermitian lattice group with its two signs.

Source: Gerald Höhn, `Atlas/Conway/IcosianFullMonomialCentralizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

theorem icosian_actual_monomial_mem_frame (m : IcosianUnitMonomial)
    (f : icosianHermitianGroup) (he : f.val=icosianMonomialRepresentation m) :
    f∈icosianCoordinateFrameStabilizer := by
  let g : icosianLiftedMonomial := ⟨m,icosianMonomial_mem_of_representation m f he⟩
  have hg : icosianMonomialToHermitian g=f := Subtype.ext he.symm
  rw [← hg]
  exact icosianMonomial_mem_frameStabilizer g

theorem icosianAxisReflection_mem_frame (i : Fin 3) :
    icosianAxisReflection i∈icosianCoordinateFrameStabilizer := by
  apply icosian_fix_axes_mem_frame
  intro j
  rw [icosianAxisPoint,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (if j=i then (-1 : IcosianQuaternion) else 1),?_⟩
  change MulOpposite.op (if j=i then (-1 : IcosianQuaternion) else 1) •
    (Pi.single j 1 : IcosianRationalCoordinates)=
      (icosianAxisReflection i).val (Pi.single j 1)
  funext k
  rw [icosianAxisReflection_apply]
  by_cases hki : k=i <;> by_cases hkj : k=j <;>
    simp_all

theorem icosianReflectionSwap_mem_frame (p : Fin 2) :
    icosianReflectionEdgeGenerator 0 p∈icosianCoordinateFrameStabilizer :=
  icosian_actual_monomial_mem_frame _ _ (icosianReflectionSwap_linear p)

theorem icosianReflectionEdgeWord_mem_frame (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeWord k p∈icosianCoordinateFrameStabilizer :=
  icosian_actual_monomial_mem_frame _ _ (icosianReflectionEdgeWord_linear k p)

/-- The centralizer of the full actual monomial group in right-D-linear
endomorphisms consists of scalars over the golden field. -/
theorem icosian_full_monomial_centralizer_scalar
    (f : IcosianRationalCoordinates →ₗ[ℚ] IcosianRationalCoordinates)
    (hf : ∀ a x, f (icosianRightMul x a)=icosianRightMul (f x) a)
    (hc : ∀ g : icosianCoordinateFrameStabilizer, ∀ x,
      f (g.val.val x)=g.val.val (f x)) :
    ∃ a : GoldenRational, ∀ x i, f x i=(a : IcosianQuaternion)*x i :=
  icosian_linear_scalar_of_bounded_monomials f hf
    (fun i => hc ⟨_,icosianAxisReflection_mem_frame i⟩)
    (fun p => hc ⟨_,icosianReflectionSwap_mem_frame p⟩)
    (fun k => hc ⟨_,icosianReflectionEdgeWord_mem_frame k 0⟩)

theorem icosian_full_monomial_centralizer_iff
    (f : IcosianRationalCoordinates →ₗ[ℚ] IcosianRationalCoordinates)
    (hf : ∀ a x, f (icosianRightMul x a)=icosianRightMul (f x) a) :
    (∀ g : icosianCoordinateFrameStabilizer, ∀ x,f (g.val.val x)=g.val.val (f x)) ↔
      ∃ a : GoldenRational, ∀ x i,f x i=(a : IcosianQuaternion)*x i := by
  constructor
  · exact icosian_full_monomial_centralizer_scalar f hf
  · rintro ⟨a,ha⟩ g x
    have he (y : IcosianRationalCoordinates) : f y=icosianRightMul y (a : IcosianQuaternion) := by
      funext i
      rw [ha]
      exact Quaternion.coe_commutes a (y i)
    rw [he,he,g.val.property.1]

/-- In particular, the center of the actual isometry group has no additional
quaternionic scalar units. No group-order or simplicity theorem is used. -/
theorem icosianHermitian_center_eq_sign (g : icosianHermitianGroup)
    (hg : g∈Subgroup.center icosianHermitianGroup) : g=1 ∨ g=icosianCentralSign := by
  have hc : ∀ h : icosianHermitianGroup, g*h=h*g :=
    fun h => ((Subgroup.mem_center_iff.mp hg) h).symm
  obtain ⟨a,ha⟩ := icosian_full_monomial_centralizer_scalar g.val.toLinearMap g.property.1
    (fun h x => congrArg (fun f : icosianHermitianGroup => f.val x) (hc h.val))
  change ∀ x i, g.val x i=(a : IcosianQuaternion)*x i at ha
  have hs : ∀ p : IcosianRootPoint,g • p=p := by
    intro p
    obtain ⟨r,hr⟩ := icosianRootToPoint_surjective p
    subst p
    apply Subtype.ext
    change g • icosianRootPoint r=icosianRootPoint r
    rw [icosianRootPoint,Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨MulOpposite.op (a : IcosianQuaternion),?_⟩
    change MulOpposite.op (a : IcosianQuaternion) • icosianCoordinateEmbedding r.val=
      g.val (icosianCoordinateEmbedding r.val)
    funext i
    rw [ha]
    exact (Quaternion.coe_commutes a _).symm
  exact icosian_fix_rootPoints_eq_sign g hs

theorem icosianHermitian_center :
    Subgroup.center icosianHermitianGroup=icosianCentralSigns := by
  ext g
  constructor
  · exact icosianHermitian_center_eq_sign g
  · rintro (rfl|rfl)
    · exact (Subgroup.center _).one_mem
    · apply Subgroup.mem_center_iff.mpr
      intro h
      exact (icosianCentralSign_comm h).symm

end Atlas.Conway
