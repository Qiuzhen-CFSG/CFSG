module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual partial flags in binary five-space

A chosen basis and a subset of the four proper cuts define actual subspaces
and their common stabilizer in GL₅(2). Cut `i` means dimension `i + 1`.
The empty set gives the whole group. The first and last cuts are identified
with the span of a nonzero vector and the kernel of a nonzero functional.

This interface separates the exhaustion of Sylow overgroups by flags from
the calculation of their residuals. Neither assertion is assumed or proved
by the definition `IsFlagParabolic`.

Reference: Aschbacher–Smith, combined manuscript (1 March 2004), the
characteristic-two parabolic argument in A.3.12, printed p.48, and the
L₅(2) branch in the proof of 1.3.9, printed p.514.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic

/-- A basis of the actual natural binary five-space. -/
abbrev FiveBasis := Module.Basis (Fin 5) (ZMod 2) (Space 5)

/-- The span of the first `i + 1` basis vectors; the indices are the four proper cuts. -/
noncomputable def flagSpace (b : FiveBasis) (i : Fin 4) : Submodule (ZMod 2) (Space 5) :=
  Submodule.span (ZMod 2) (b '' {j : Fin 5 | j.val ≤ i.val})

/-- The actual subgroup preserving each subspace specified by the cuts. -/
noncomputable def flagStabilizer (b : FiveBasis) (cuts : Set (Fin 4)) :
    Subgroup (LinearGroup 5) := ⨅ i ∈ cuts, parabolic (flagSpace b i)

/-- Being an embedded stabilizer of a partial flag, including the empty flag. -/
def IsFlagParabolic (P : Subgroup (LinearGroup 5)) : Prop :=
  ∃ (b : FiveBasis) (cuts : Set (Fin 4)), P = flagStabilizer b cuts

theorem mem_flagStabilizer_iff (b : FiveBasis) (cuts : Set (Fin 4)) (g : LinearGroup 5) :
    g ∈ flagStabilizer b cuts ↔ ∀ i ∈ cuts, ∀ v, g v ∈ flagSpace b i ↔ v ∈ flagSpace b i := by
  simp only [flagStabilizer, mem_iInf]
  rfl

@[simp] theorem flagStabilizer_empty (b : FiveBasis) : flagStabilizer b ∅ = ⊤ := by
  simp [flagStabilizer]

@[simp] theorem flagStabilizer_singleton (b : FiveBasis) (i : Fin 4) :
    flagStabilizer b {i} = parabolic (flagSpace b i) := by
  simp [flagStabilizer]

theorem flagStabilizer_antitone (b : FiveBasis) : Antitone (flagStabilizer b) := by
  intro s t hst g hg
  rw [mem_flagStabilizer_iff] at hg ⊢
  exact fun i hi => hg i (hst hi)

theorem basis_mem_flagSpace_iff (b : FiveBasis) (i : Fin 4) (j : Fin 5) :
    b j ∈ flagSpace b i ↔ j.val ≤ i.val := b.self_mem_span_image

theorem flagSpace_ne_bot (b : FiveBasis) (i : Fin 4) : flagSpace b i ≠ ⊥ := by
  intro he
  have hm := (basis_mem_flagSpace_iff b i 0).mpr (Nat.zero_le _)
  rw [he, Submodule.mem_bot] at hm
  exact b.ne_zero 0 hm

theorem flagSpace_ne_top (b : FiveBasis) (i : Fin 4) : flagSpace b i ≠ ⊤ := by
  intro he
  have hm : b 4 ∈ flagSpace b i := he ▸ Submodule.mem_top
  have := (basis_mem_flagSpace_iff b i 4).mp hm
  change 4 ≤ i.val at this
  omega

/-- The first flag space is the line through the first basis vector. -/
theorem flagSpace_zero (b : FiveBasis) :
    flagSpace b 0 = Submodule.span (ZMod 2) {b 0} := by
  unfold flagSpace
  have he : {j : Fin 5 | j.val ≤ (0 : Fin 4).val} = {0} := by
    ext j
    simp only [Set.mem_ofPred_eq, Fin.val_zero, Nat.le_zero, Set.mem_singleton_iff]
    exact (Fin.ext_iff (a := j) (b := (0 : Fin 5))).symm
  rw [he, Set.image_singleton]

/-- The last proper flag space is the kernel of the last coordinate functional. -/
theorem flagSpace_last (b : FiveBasis) :
    flagSpace b 3 = LinearMap.ker (b.coord 4) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi4 : i ≠ 4 := by
      intro he
      subst i
      change 4 ≤ 3 at hi
      omega
    simp [LinearMap.mem_ker, Module.Basis.coord_apply, hi4.symm]
  · intro v hv
    have he := b.sum_repr v
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i = 4
    · subst i
      have hz : b.repr v 4 = 0 := hv
      simp [hz]
    · apply Submodule.smul_mem
      apply (basis_mem_flagSpace_iff b 3 i).mpr
      have : i.val ≠ 4 := fun h => hi (Fin.ext h)
      change i.val ≤ 3
      omega

end BinaryLinear.FiveFlagGeometry
