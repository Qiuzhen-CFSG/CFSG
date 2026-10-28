module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEight
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Basic

/-!
Adapted from `Atlas/Comparisons/Exceptional/DeletedEightSplit.lean`.
An explicit hyperbolic basis identifies the deleted module with the split
six-dimensional quadratic space. Finite identities are checked by the kernel.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.DeletedEight
open Atlas.Codes Atlas.Order20160A8.HalfWeight ClassicalOrthogonal
open scoped BigOperators
abbrev D := VectorD 3 Bit

def basisWord : Index 3 → V := Sum.elim
  ![![1,1,1,1,0,0,0,0], ![1,0,0,1,1,1,0,0], ![0,0,1,1,1,0,1,0]]
  ![![1,1,1,0,1,0,0,0], ![0,1,0,1,1,1,0,0], ![1,1,0,0,0,1,1,0]]

def raw : D →ₗ[Bit] V where
  toFun x := ∑ i, x i • basisWord i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

theorem raw_even (x : D) : raw x ∈ evenCode := by
  have h : ∀ x : D, (∑ i : Fin 8, raw x i) = 0 := by decide +kernel
  exact h x

def intoEven : D →ₗ[Bit] evenCode := raw.codRestrict evenCode raw_even

theorem raw_last (x : D) : raw x 7 = 0 := by
  have h : ∀ x : D, raw x 7 = 0 := by decide +kernel
  exact h x

theorem raw_kernel (x : D) (hx : raw x = 0) : x = 0 := by
  have h : ∀ x : D, raw x = 0 → x = 0 := by decide +kernel
  exact h x hx

def splitMap : D →ₗ[Bit] W := constants.mkQ.comp intoEven

theorem splitMap_injective : Function.Injective splitMap := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hm : intoEven x ∈ constants := by
    exact (Submodule.Quotient.mk_eq_zero constants).mp hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hl := congrArg (fun z : evenCode => z.val 7) ha
  have ha0 : a = 0 := by
    simpa only [Submodule.coe_smul, Pi.smul_apply, oneWord, smul_eq_mul, mul_one,
      intoEven, LinearMap.codRestrict_apply, raw_last] using hl
  apply raw_kernel
  have he := congrArg Subtype.val ha
  simpa [ha0, intoEven] using he.symm

def splitEquiv : D ≃ₗ[Bit] W := LinearEquiv.ofBijective splitMap ⟨splitMap_injective,
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [quotient_finrank]; simp [D, VectorD, Index])).mp splitMap_injective⟩

theorem raw_quadratic (x : D) : binaryHalfWeight (raw x) = formD 3 Bit x := by
  have h : ∀ x : D, binaryHalfWeight (raw x) = formD 3 Bit x := by decide +kernel
  exact h x

/-- Explicit comparison with the retained standard split six-dimensional form. -/
def splitIsometry : (formD 3 Bit).IsometryEquiv quotientQuadratic where
  __ := splitEquiv
  map_app' x := raw_quadratic x

end Atlas.Order20160A8.DeletedEight
