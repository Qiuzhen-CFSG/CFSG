module

public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Theory.SpecificGroups.SymmetricEight.CentralPair

/-!
# Sylow-fixed vectors in the alternating eight-point augmentation core

The even binary-tree Sylow subgroup acts transitively on the eight coordinates.
Its fixed vectors in the augmentation core are therefore constant. Sylow
conjugacy gives the same conclusion for every Sylow two-subgroup of A₈.

This distinguishes the seven-dimensional augmentation core from the
six-dimensional deleted section. It checks the Sylow seed used in the last
paragraph of Aschbacher--Smith 12.2.16, printed p.800; compare the fixed-line
calculation in 12.6.1(2), printed p.823.
-/

public section
namespace BinaryPermutation
open Subgroup Theory.SpecificGroups.SymmetricEight
open A6ShadowTwoLocals CentralPair

private theorem even_tree_fixed_constant (v : core (Fin 8))
    (h : ∀ a ∈ (evenTreeSylow : Subgroup A8),
      alternatingCoreRepresentation (Fin 8) a v = v) :
    v.val ∈ constants (Fin 8) := by
  have hm (a : A8) (ha : a.val ∈ treeGroup) :
      alternatingCoreRepresentation (Fin 8) a v = v := by
    apply h a
    rwa [evenTreeSylow_coe]
  let a : A8 := ⟨treeGenerator 0 * treeGenerator 1, by
    change Equiv.Perm.sign (treeGenerator 0 * treeGenerator 1) = 1
    decide +kernel⟩
  let b : A8 := ⟨treeGenerator 4, by
    change Equiv.Perm.sign (treeGenerator 4) = 1
    decide +kernel⟩
  let d : A8 := ⟨treeGenerator 6, by
    change Equiv.Perm.sign (treeGenerator 6) = 1
    decide +kernel⟩
  have ha := hm a (treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 1))
  have hb := hm b (treeGenerator_mem 4)
  have hd := hm d (treeGenerator_mem 6)
  have h01 := congrArg (fun w : core (Fin 8) => w.val 0) ha
  have h23 := congrArg (fun w : core (Fin 8) => w.val 2) ha
  have h02 := congrArg (fun w : core (Fin 8) => w.val 0) hb
  have h04 := congrArg (fun w : core (Fin 8) => w.val 0) hd
  have h15 := congrArg (fun w : core (Fin 8) => w.val 1) hd
  have h26 := congrArg (fun w : core (Fin 8) => w.val 2) hd
  have h37 := congrArg (fun w : core (Fin 8) => w.val 3) hd
  change v.val 1 = v.val 0 at h01
  change v.val 3 = v.val 2 at h23
  change v.val 2 = v.val 0 at h02
  change v.val 4 = v.val 0 at h04
  change v.val 5 = v.val 1 at h15
  change v.val 6 = v.val 2 at h26
  change v.val 7 = v.val 3 at h37
  apply (mem_constants_iff v.val).mpr
  refine ⟨v.val 0, fun i => ?_⟩
  fin_cases i <;> simp_all

/-- Every Sylow two-subgroup of A₈ fixes only the constant line in its core. -/
theorem alternatingEight_core_sylow_fixed_constant
    (S : Sylow 2 (alternatingGroup (Fin 8))) (v : core (Fin 8))
    (h : ∀ a ∈ (S : Subgroup (alternatingGroup (Fin 8))),
      alternatingCoreRepresentation (Fin 8) a v = v) :
    v.val ∈ constants (Fin 8) := by
  let ρ := alternatingCoreRepresentation (Fin 8)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A8 evenTreeSylow S
  have he : (evenTreeSylow : Subgroup A8).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • evenTreeSylow : Sylow 2 A8) : Subgroup A8) = _
    rw [hg]
  have hf : ∀ a ∈ (evenTreeSylow : Subgroup A8),
      ρ a (ρ g⁻¹ v) = ρ g⁻¹ v := by
    intro a ha
    have hh := h (g * a * g⁻¹) (he ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
    have hmul : g⁻¹ * (g * a * g⁻¹) = a * g⁻¹ := by group
    have hh' := congrArg (ρ g⁻¹) hh
    change ρ g⁻¹ (ρ (g * a * g⁻¹) v) = ρ g⁻¹ v at hh'
    simpa only [← Module.End.mul_apply, ← map_mul, hmul] using hh'
  obtain ⟨k, hk⟩ := (mem_constants_iff _).mp
    (even_tree_fixed_constant (ρ g⁻¹ v) hf)
  apply (mem_constants_iff v.val).mpr
  refine ⟨k, fun i => ?_⟩
  have hi := hk (g.val.symm i)
  change v.val (g.val (g.val.symm i)) = k at hi
  simpa only [Equiv.apply_symm_apply] using hi

end BinaryPermutation
