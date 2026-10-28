module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.ResidualMovedGeneration

/-!
# Augmentation-core generation by the even pair stabilizer

Seven explicit even permutations preserving {01,23,45,67} produce the
seven duads e_i+e_0 as displacements of even words. These duads span the
seven-dimensional augmentation core. Generation is preserved under conjugacy
and on restriction to the actual embedded two-residual.

This calculation retains the constant line in the augmentation module.
Its source application through the universal cover is 13.5.21(6),
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.924.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightCover

private def move : Fin 8 → Equiv.Perm (Fin 8) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2,
    Equiv.swap 0 4 * Equiv.swap 1 5, Equiv.swap 0 5 * Equiv.swap 1 4,
    Equiv.swap 0 6 * Equiv.swap 1 7, Equiv.swap 0 7 * Equiv.swap 1 6]

private theorem move_even (i : Fin 8) : move i ∈ alternatingGroup (Fin 8) := by
  fin_cases i <;> simp [move, Equiv.Perm.mem_alternatingGroup]

private theorem move_pairs : ∀ i, move i ∈ pairStabilizer := by decide +kernel

private def duad (i j : Fin 8) : core (Fin 8) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private theorem displacements : ∀ i : Fin 8,
    coreRepresentation (Fin 8) (move i) (duad 0 (if i.val < 4 then 4 else 2)) -
      duad 0 (if i.val < 4 then 4 else 2) = duad i 0 := by decide +kernel

/-- The even stabilizer of the four pairs generates the entire augmentation core. -/
theorem core_pairStabilizer_generated :
    subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤
      (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))) = ⊤ := by
  let C := subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤
    (pairStabilizer.subgroupOf (alternatingGroup (Fin 8)))
  have hd (i : Fin 8) : duad i 0 ∈ C := by
    rw [← displacements i]
    exact Submodule.subset_span ⟨⟨move i, move_even i⟩, move_pairs i,
      duad 0 (if i.val < 4 then 4 else 2), Submodule.mem_top, rfl⟩
  apply top_unique
  intro v _
  have heq : (∑ i, v.val i • duad i 0) = v := by
    apply Subtype.ext
    change (∑ i, v.val i • (Pi.single i 1 + Pi.single 0 1)) = v.val
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hsum : ∑ i, v.val i = 0 := v.property
    rw [hsum, zero_smul, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v.val
  rw [← heq]
  exact C.sum_mem fun i _ => C.smul_mem _ (hd i)

/-- The actual embedded two-residual still generates the full core. -/
theorem core_pairResidual_generated :
    subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤
      ((pResidual 2 (pairStabilizer.subgroupOf (alternatingGroup (Fin 8)))).map
        (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).subtype) = ⊤ :=
  commutator_pResidual_eq_top _ _ core_pairStabilizer_generated

/-- A conjugate of the same pair stabilizer also generates the full core. -/
theorem core_pairStabilizer_conjugate_generated (g : alternatingGroup (Fin 8)) :
    subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤
      ((pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map
        (MulAut.conj g).toMonoidHom) = ⊤ := by
  let ρ := alternatingCoreRepresentation (Fin 8)
  let P := pairStabilizer.subgroupOf (alternatingGroup (Fin 8))
  let C := subspaceCommutator ρ ⊤ (P.map (MulAut.conj g).toMonoidHom)
  have hc : subspaceCommutator ρ ⊤ P ≤ C.comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    change ρ g (ρ a v - v) ∈ C
    have he : ρ g (ρ a v - v) = ρ (g * a * g⁻¹) (ρ g v) - ρ g v := by
      rw [map_sub]
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
    rw [he]
    exact Submodule.subset_span ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, ρ g v, trivial, rfl⟩
  rw [core_pairStabilizer_generated] at hc
  apply top_unique
  intro v _
  have hh := hc (show ρ g⁻¹ v ∈ ⊤ from trivial)
  change ρ g (ρ g⁻¹ v) ∈ C at hh
  simpa only [ρ.self_inv_apply] using hh

end BinaryPermutation.EightCover
