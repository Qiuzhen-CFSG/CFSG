module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The scalar-kernel strategy is adapted from
Atlas/LinearGroups/Orthogonal/SingularLineKernel.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: prove scalar equality directly on the native hyperbolic coordinate
basis, and use characteristic two and the given Clifford Spin natural action.
-/

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularLines
import Mathlib.Tactic

/-!
# Faithfulness on the singular lines of the Spin natural module

An isometry preserving every singular line scales each hyperbolic basis vector.
Singular sums identify all these scalars, and preservation of the form forces
their square to be one. In characteristic two the scalar is one, so the proved
injectivity of the Clifford natural action gives faithfulness on singular lines.
This is the coordinate version of the singular-line kernel argument underlying
the type-D simplicity proof (GLS3, Chapter 1, 1.10.1(b)).
-/

@[expose] public section
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup
variable (k : Type*) [Field k]

private def e (i : Fin 4) : QuadraticSpace k := (Pi.single i 1, 0)
private def f (i : Fin 4) : QuadraticSpace k := (0, Pi.single i 1)

private theorem vector_expansion (v : QuadraticSpace k) :
    v = (∑ i, v.1 i • e k i) + ∑ i, v.2 i • f k i := by
  ext j <;> simp [e, f, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem singular_isometry_scalar (z : quadraticIsometrySubgroup (quadraticForm k))
    (hz : ∀ v, quadraticForm k v = 0 → ∃ c : k, z.val v = c • v) :
    ∃ c : k, c ^ 2 = 1 ∧ ∀ v, z.val v = c • v := by
  classical
  have he (i : Fin 4) : quadraticForm k (e k i) = 0 := by
    simp [e, quadraticForm, hyperbolicForm_apply]
  have hf (i : Fin 4) : quadraticForm k (f k i) = 0 := by
    simp [f, quadraticForm, hyperbolicForm_apply]
  choose c hc using fun i => hz (e k i) (he i)
  choose d hd using fun i => hz (f k i) (hf i)
  have hcc (i j : Fin 4) : c i = c j := by
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨a, ha⟩ := hz (e k i + e k j) (by
      simp [e, quadraticForm, hyperbolicForm_apply])
    rw [map_add, hc, hc] at ha
    have hi := congrArg (fun v : QuadraticSpace k => v.1 i) ha
    have hj := congrArg (fun v : QuadraticSpace k => v.1 j) ha
    simp [e, hij, Ne.symm hij] at hi hj
    exact hi.trans hj.symm
  have hdc (i : Fin 4) : d i = c 0 := by
    obtain ⟨j, hij⟩ : ∃ j : Fin 4, j ≠ i := exists_ne i
    obtain ⟨a, ha⟩ := hz (f k i + e k j) (by
      simp [e, f, quadraticForm, hyperbolicForm_apply, Pi.single_apply, Ne.symm hij])
    rw [map_add, hd, hc] at ha
    have hi := congrArg (fun v : QuadraticSpace k => v.2 i) ha
    have hj := congrArg (fun v : QuadraticSpace k => v.1 j) ha
    simp [e, f] at hi hj
    exact hi.trans (hj.symm.trans (hcc j 0))
  have hscalar (v : QuadraticSpace k) : z.val v = c 0 • v := by
    conv_lhs => rw [vector_expansion k v]
    simp only [map_add, map_sum, map_smul, hc, hd, hdc, hcc _ 0]
    conv_rhs => rw [vector_expansion k v]
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply smul_comm
  refine ⟨c 0, ?_, hscalar⟩
  have h := (mem_quadraticIsometrySubgroup _ _).mp z.prop (e k 0 + f k 0)
  rw [hscalar, (quadraticForm k).map_smul] at h
  simpa [quadraticForm, hyperbolicForm_apply, e, f, Pi.single_apply, pow_two] using h

variable [IsAlgClosed k] [CharP k 2]

theorem singularLines_faithful : FaithfulSMul (Points k) (SingularLines k) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hscalar (v : QuadraticSpace k) (hq : quadraticForm k v = 0) :
      ∃ c : k, (naturalAction k g).val v = c • v := by
    by_cases hv : v = 0
    · exact ⟨0, by simp [hv]⟩
    have h := congrArg Subtype.val (hg (singularLineMk k v hv hq))
    change (naturalAction k g).val • Projectivization.mk k v hv =
      Projectivization.mk k v hv at h
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc.symm⟩
  obtain ⟨c, hc, hcv⟩ := singular_isometry_scalar k (naturalAction k g) hscalar
  have hc1 : c = 1 := by
    apply CharTwo.sq_injective
    simpa using hc
  apply naturalAction_injective k
  rw [map_one]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simpa [hc1] using hcv v

end Triality.SimplyConnected.NormalRootExtraction
