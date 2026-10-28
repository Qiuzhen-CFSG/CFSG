module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Coordinates
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.DefectTransfer
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.Normalized

/-!
# From finite lifted root relations to a cubic-defect section

A marked presentation identifies the entire positive subgroup once its
projection is bijective. In a cover, the six cubic generator lifts and the
fifteen descending relations modulo two central cubic elements then evaluate
that presentation in the central quotient. Pulling this homomorphism back
along the marked equivalence and choosing representatives gives the required
CubicDefectLift on the literal positive subgroup.

Two obligations remain explicit: bijectivity of the presentation projection,
and the fifteen lifted relations with two cubic defects. Neither individual
cubic lifts nor the order-27 hypothesis alone supplies those relations.
The source-theorem assembly must discharge both inputs. Source: the three-part
of Aschbacher--Smith I.1.4(5), printed p.408; GLS3 §6.1.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
open PerfectCentralCovering
open Subgroup
namespace RootLifts

variable {E : Type*} [Group E]

/-- A concrete starting point for the finite lifted-relation calculation.
The two displayed cubic kernel elements are not asserted to control all relations. -/
theorem exists_cubic_roots_and_pair_defects (f : Cover E S) :
    ∃ L : CubicRootLifts f.toMonoidHom,
      L.shortDefect ∈ f.toMonoidHom.ker ∧ L.mixedDefect ∈ f.toMonoidHom.ker ∧
      L.shortDefect ^ 3 = 1 ∧ L.mixedDefect ^ 3 = 1 := by
  let L := normalizedRoots f.toMonoidHom f.surjective f.ker_le_center
  exact ⟨L, L.shortDefect_mem, L.mixedDefect_mem,
    L.shortDefect_cube f.ker_le_center, L.mixedDefect_cube f.ker_le_center⟩

/-- Only the finite generator relations, with two actual cubic kernel elements.
There is no assertion about a lift on all of `positive` in this data. -/
structure FiniteDefectRelations (f : Cover E S) where
  roots : CubicRootLifts f.toMonoidHom
  z : E
  w : E
  z_mem : z ∈ f.toMonoidHom.ker
  w_mem : w ∈ f.toMonoidHom.ker
  z_cube : z ^ 3 = 1
  w_cube : w ^ 3 = 1
  swaps : ∀ i j : Fin 6, i < j →
    roots.gen j * roots.gen i *
      (roots.gen i * roots.gen j * swapTail roots.gen i j)⁻¹ ∈ zpowers z ⊔ zpowers w

namespace FiniteDefectRelations
variable {f : Cover E S} (D : FiniteDefectRelations f)

abbrev defect : Subgroup E := zpowers D.z ⊔ zpowers D.w

theorem defect_le_kernel : D.defect ≤ f.toMonoidHom.ker :=
  sup_le (zpowers_le.mpr D.z_mem) (zpowers_le.mpr D.w_mem)

theorem defect_normal : D.defect.Normal :=
  ⟨fun x hx g => by
    rw [mem_center_iff.mp (f.ker_le_center (D.defect_le_kernel hx)) g,
      mul_inv_cancel_right]
    exact hx⟩

/-- The finite relations evaluate the presentation in the central quotient. -/
def presentationLift : letI := D.defect_normal; Presentation →* E ⧸ D.defect := by
  let := D.defect_normal
  let q := QuotientGroup.mk' D.defect
  let x : Fin 6 → E ⧸ D.defect := fun r => q (D.roots.gen r)
  apply PresentedGroup.toGroup (relators_vanish x ?_ ?_)
  · intro r
    change q (D.roots.gen r) ^ 3 = 1
    rw [← map_pow, D.roots.cubes, map_one]
  · intro i j hij
    have h := (QuotientGroup.eq_one_iff _).mpr (D.swaps i j hij)
    change q (D.roots.gen j * D.roots.gen i *
      (D.roots.gen i * D.roots.gen j * swapTail D.roots.gen i j)⁻¹) = 1 at h
    simpa only [map_mul, map_inv, map_swapTail, mul_inv_eq_one] using h

theorem presentationLift_of (r : Fin 6) :
    let := D.defect_normal
    D.presentationLift (PresentedGroup.of r) = QuotientGroup.mk' D.defect (D.roots.gen r) := by
  let := D.defect_normal
  simp only [presentationLift, PresentedGroup.toGroup.of]

/-- The quotient lift retains the original projective marking on every generator. -/
theorem presentationLift_projects :
    let := D.defect_normal
    (f.quotientKernelSubgroup D.defect D.defect_le_kernel).toMonoidHom.comp
      D.presentationLift = positive.subtype.comp presentationProjection := by
  let := D.defect_normal
  apply PresentedGroup.ext
  intro r
  simp only [MonoidHom.comp_apply, D.presentationLift_of, presentationProjection_of]
  exact D.roots.projects r

include D in
/-- Generation and completeness of the presentation turn the finite local
relations into the all-elements multiplication condition used by transfer. -/
theorem nonempty_cubicDefectLift
    (hp : Function.Bijective presentationProjection) : Nonempty (CubicDefectLift f positive) := by
  let := D.defect_normal
  let q := QuotientGroup.mk' D.defect
  let g := f.quotientKernelSubgroup D.defect D.defect_le_kernel
  let e : Presentation ≃* positive := MulEquiv.ofBijective presentationProjection hp
  let s : positive →* E ⧸ D.defect := D.presentationLift.comp e.symm.toMonoidHom
  have hs (x : positive) : g.toMonoidHom (s x) = x := by
    change (g.toMonoidHom.comp D.presentationLift) (e.symm x) = x
    rw [D.presentationLift_projects]
    change ((e (e.symm x) : positive) : S) = x
    rw [e.apply_symm_apply]
  let lift : positive → E := fun x => (QuotientGroup.mk'_surjective D.defect (s x)).choose
  have hq (x : positive) : q (lift x) = s x :=
    (QuotientGroup.mk'_surjective D.defect (s x)).choose_spec
  refine ⟨{
    z := D.z, w := D.w, z_mem := D.z_mem, w_mem := D.w_mem,
    z_cube := D.z_cube, w_cube := D.w_cube,
    lift := lift, projects := ?_, multiplicative := ?_ }⟩
  · intro x
    change g.toMonoidHom (q (lift x)) = x
    rw [hq, hs]
  · intro x y
    apply (QuotientGroup.eq_one_iff _).mp
    change q (lift (x * y) * (lift x * lift y)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, hq, hq, hq, map_mul, mul_inv_cancel]

end FiniteDefectRelations
end RootLifts

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
