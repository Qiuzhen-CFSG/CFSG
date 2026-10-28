module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags

/-!
# Every full binary flag stabilizer is a two-group

The checked unitriangular Sylow construction supplies one full flag.
A basis change carries that flag to any prescribed basis, so its stabilizer
remains a two-group. This allows an exceptional comparison to certify a
permutation flag without enumerating the symmetric group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.25 and 15.3.28–32, printed pp.959–960 and 1131–1133.
-/

@[expose] public section
open Subgroup

namespace BinaryLinear.InvariantNodeActions
open OuterCyclic
/-- A full flag over the binary field has a two-group stabilizer. -/
theorem fullFlag_isPGroup {m : ℕ} (b : Basis m) : IsPGroup 2 (cutStabilizer b Set.univ) := by
  let _ : Finite (LinearGroup (m + 1)) :=
    Finite.of_injective (fun g : LinearGroup (m + 1) => (g : Space (m + 1) → Space (m + 1)))
      DFunLike.coe_injective
  obtain ⟨a, ha⟩ := sylow_eq_cutStabilizer (Sylow.nonempty.some : Sylow 2 (LinearGroup (m + 1)))
  have hp : IsPGroup 2 (cutStabilizer a Set.univ) := ha ▸ (Sylow.nonempty.some : Sylow 2 (LinearGroup (m + 1))).isPGroup'
  let g : LinearGroup (m + 1) := a.equiv b (Equiv.refl _)
  have hab : a.map g = b := by ext i; simp [g]
  have h := hp.map (MulAut.conj g).toMonoidHom
  rwa [cutStabilizer_map_conj, hab] at h
end BinaryLinear.InvariantNodeActions
