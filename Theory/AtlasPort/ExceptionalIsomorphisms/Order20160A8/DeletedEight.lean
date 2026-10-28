module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.HalfWeight
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic

/-!
Adapted from `Atlas/Comparisons/Exceptional/DeletedEight.lean`.
The even-coordinate space modulo the constant line carries the half-weight form.
Only namespaces and module boundaries are changed.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.DeletedEight
open Atlas.Codes Atlas.Order20160A8.HalfWeight
open scoped BigOperators
abbrev V := Fin 8 → Bit

def parity : V →ₗ[Bit] Bit where
  toFun x := ∑ i, x i
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' r x := by simp [Finset.mul_sum]

def evenCode : Submodule Bit V := parity.ker

def oneWord : evenCode := ⟨fun _ => 1, by change (∑ _ : Fin 8, (1 : Bit)) = 0; decide⟩
def constants : Submodule Bit evenCode := Submodule.span Bit {oneWord}
abbrev W := evenCode ⧸ constants

theorem oneWord_ne_zero : oneWord ≠ 0 := by
  intro h
  have he := congrArg (fun x : evenCode => x.val 0) h
  exact one_ne_zero he

theorem parity_surjective : Function.Surjective parity := by
  intro a
  refine ⟨Pi.single 0 a, ?_⟩
  simp [parity]

theorem evenCode_finrank : Module.finrank Bit evenCode = 7 := by
  have h := parity.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr parity_surjective, finrank_top] at h
  have hv : Module.finrank Bit V = 8 := by simp [V]
  rw [hv, Module.finrank_self] at h
  change Module.finrank Bit evenCode = 7
  change 1 + Module.finrank Bit evenCode = 8 at h
  omega

theorem quotient_finrank : Module.finrank Bit W = 6 := by
  have hc : Module.finrank Bit constants = 1 := finrank_span_singleton oneWord_ne_zero
  have h := constants.finrank_quotient_add_finrank
  rw [hc, evenCode_finrank] at h
  change Module.finrank Bit W + 1 = 7 at h
  omega

theorem even_weight (x : evenCode) : 2 ∣ hammingNorm x.val :=
  even_iff_two_dvd.mp ((even_weight_iff x.val).mpr x.property)

def quadratic : QuadraticMap Bit evenCode Bit := binaryHalfWeightQuadratic evenCode even_weight

theorem constants_radical : constants ≤ quadratic.radical := by
  apply Submodule.span_le.mpr
  intro x hx
  have he : x = oneWord := Set.mem_singleton_iff.mp hx
  subst x
  constructor
  · change binaryHalfWeight (fun _ : Fin 8 => (1 : Bit)) = 0
    simp [binaryHalfWeight, hammingNorm]
  · apply LinearMap.ext
    intro z
    rw [quadratic, binaryHalfWeightQuadratic_polar]
    change binaryDot (fun _ : Fin 8 => (1 : Bit)) z.val = 0
    have hz : (∑ i : Fin 8, z.val i) = 0 := z.property
    simpa only [binaryDot_apply, one_mul] using hz

/-- Half-weight descends through the actual constant line. -/
def quotientQuadratic : QuadraticMap Bit W Bit := quadratic.lift constants constants_radical

@[simp] theorem quotientQuadratic_mk (x : evenCode) :
    quotientQuadratic (Submodule.Quotient.mk x) = binaryHalfWeight x.val := rfl

end Atlas.Order20160A8.DeletedEight
