/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianAxisIntersection.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRoots
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoKernel

/-!
# Icosian Axis Intersection

An axis meets the rational icosian lattice in exactly twice the integral
icosian order. The proof combines the single-coordinate congruences with
the kernel of reduction modulo two.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianAxisIntersection.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

theorem icosianCoordinateEmbedding_single (i : Fin 3) (z : icosianOrder) :
    icosianCoordinateEmbedding (icosianSingle i z)=Pi.single i z.val := by
  funext j
  by_cases h : j=i <;> simp [icosianCoordinateEmbedding,icosianSingle,h]

theorem icosianAxisIntersection (i : Fin 3) (a : IcosianQuaternion) :
    Pi.single i a∈rationalIcosianLattice ↔
      ∃ u : icosianOrder, a=2*u.val := by
  constructor
  · rintro ⟨x,hx,he⟩
    have hxi : (x i).val=a := by
      simpa [icosianCoordinateEmbedding] using congrFun he i
    have hsingle : x=icosianSingle i (x i) := by
      funext j
      apply Subtype.ext
      have hj := congrFun he j
      by_cases hji : j=i
      · subst j; simp [icosianSingle]
      · simpa [icosianCoordinateEmbedding,icosianSingle,Pi.single_apply,hji] using hj
    change x∈icosianLeechModule at hx
    rw [hsingle,icosianSingle_mem] at hx
    obtain ⟨u,hu⟩ := (icosianModuloTwo_eq_zero_iff_two_mul (x i)).mp hx
    refine ⟨u,?_⟩
    rw [← hxi,hu]
    rfl
  · rintro ⟨u,rfl⟩
    refine ⟨icosianSingle i (2*u),?_,?_⟩
    · change icosianSingle i (2*u)∈icosianLeechModule
      rw [icosianSingle_mem,icosianModuloTwo_eq_zero_iff_two_mul]
      exact ⟨u,rfl⟩
    · exact icosianCoordinateEmbedding_single i (2*u)

end Atlas.Lattices
