module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/RootGroups.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.RootLinearMaps
public import Theory.AtlasPort.LinearGroups.G2.Basic

/-! The root linear maps give actual octonion automorphisms, with additive parameters and an explicit noncommuting pair. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion
open Explicit
variable {K : Type*} [Field K]

/-- The explicit root family as actual multiplication-preserving automorphisms. -/
def rootA (a : K) : Model K := ⟨rootAEquiv a, rootA_mul a⟩

theorem rootA_add (a b : K) : rootA a * rootA b = rootA (a+b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Explicit.rootA_add a b x

theorem rootA_injective : Function.Injective (rootA (K := K)) := by
  intro a b h
  have hh := congrArg (fun g : Model K => g.val (basisVector 6) 0) h
  simpa [rootA,rootAEquiv,rootALinear,rootAApply,basisVector,Pi.single_apply] using hh

/-- The explicit root family as actual multiplication-preserving automorphisms. -/
def rootB (a : K) : Model K := ⟨rootBEquiv a, rootB_mul a⟩

theorem rootB_add (a b : K) : rootB a * rootB b = rootB (a+b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Explicit.rootB_add a b x

theorem rootB_injective : Function.Injective (rootB (K := K)) := by
  intro a b h
  have hh := congrArg (fun g : Model K => g.val (basisVector 5) 0) h
  simpa [rootB,rootBEquiv,rootBLinear,rootBApply,basisVector,Pi.single_apply] using hh

/-- The explicit root family as actual multiplication-preserving automorphisms. -/
def rootC (a : K) : Model K := ⟨rootCEquiv a, rootC_mul a⟩

theorem rootC_add (a b : K) : rootC a * rootC b = rootC (a+b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Explicit.rootC_add a b x

theorem rootC_injective : Function.Injective (rootC (K := K)) := by
  intro a b h
  have hh := congrArg (fun g : Model K => g.val (basisVector 3) 0) h
  simpa [rootC,rootCEquiv,rootCLinear,rootCApply,basisVector,Pi.single_apply] using hh

/-- The explicit root family as actual multiplication-preserving automorphisms. -/
def rootD (a : K) : Model K := ⟨rootDEquiv a, rootD_mul a⟩

theorem rootD_add (a b : K) : rootD a * rootD b = rootD (a+b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Explicit.rootD_add a b x

theorem rootD_injective : Function.Injective (rootD (K := K)) := by
  intro a b h
  have hh := congrArg (fun g : Model K => g.val (basisVector 2) 0) h
  simpa [rootD,rootDEquiv,rootDLinear,rootDApply,basisVector,Pi.single_apply] using hh

/-- The explicit root family as actual multiplication-preserving automorphisms. -/
def rootE (a : K) : Model K := ⟨rootEEquiv a, rootE_mul a⟩

theorem rootE_add (a b : K) : rootE a * rootE b = rootE (a+b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Explicit.rootE_add a b x

theorem rootE_injective : Function.Injective (rootE (K := K)) := by
  intro a b h
  have hh := congrArg (fun g : Model K => g.val (basisVector 2) 1) h
  simpa [rootE,rootEEquiv,rootELinear,rootEApply,basisVector,Pi.single_apply] using hh

/-- The explicit root family as actual multiplication-preserving automorphisms. -/
def rootF (a : K) : Model K := ⟨rootFEquiv a, rootF_mul a⟩

theorem rootF_add (a b : K) : rootF a * rootF b = rootF (a+b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Explicit.rootF_add a b x

theorem rootF_injective : Function.Injective (rootF (K := K)) := by
  intro a b h
  have hh := congrArg (fun g : Model K => g.val (basisVector 1) 0) h
  simpa [rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,Pi.single_apply] using hh

/-- A concrete noncommuting pair, including characteristics two and three. -/
theorem rootE_rootF_ne : rootE (1 : K) * rootF 1 ≠ rootF 1 * rootE 1 := by
  intro h
  have hh := congrArg (fun g : Model K => g.val (basisVector 2) 0) h
  simp [rootE,rootF,rootEEquiv,rootFEquiv,rootELinear,rootFLinear,
    rootEApply,rootFApply,basisVector] at hh

theorem exists_mul_ne_mul : ∃ g h : Model K, g*h ≠ h*g :=
  ⟨rootE 1,rootF 1,rootE_rootF_ne⟩
end Atlas.G2
