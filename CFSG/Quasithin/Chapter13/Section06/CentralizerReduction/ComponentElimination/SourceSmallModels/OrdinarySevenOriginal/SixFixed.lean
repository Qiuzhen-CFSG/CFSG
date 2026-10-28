module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual.PermutationContract
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.SubspaceAction

open Subgroup Equiv BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

/-!
# Fixed vectors of the ordinary A₇ replacement

The two-residual of the even three-pair normalizer contains two explicit
cubic permutations. Their orbits together connect the first six letters,
so any vector fixed by that residual is constant on those letters. It is
therefore fixed by every permutation fixing the seventh letter, including
the literal six-point stabilizer used for the replacement subgroup.
The odd augmentation equivalence transports this to the natural module.

This supplies the fixed-space premise for the replacement endgame, without
assuming that the replacement is already an alternating block.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.22,
printed p.932, the ordinary A₇ replacement and subsequent A₆ argument.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixFixed
private def cubic : Perm (Fin 7) :=
  swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5)
private def otherCubic : Perm (Fin 7) :=
  swap 0 2 * swap 2 5 * (swap 1 3 * swap 3 4)
private theorem cubic_mem : cubic ∈ evenPairNormalizer := by
  refine ⟨?_, ?_⟩
  · change _ ∈ alternatingGroup (Fin 7)
    simp [cubic, Equiv.Perm.mem_alternatingGroup]
  apply normalizer_le_normalizer_closure
  apply mem_normalizer_fintype
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl | rfl <;> decide +kernel
private theorem otherCubic_mem : otherCubic ∈ evenPairNormalizer := by
  refine ⟨?_, ?_⟩
  · change _ ∈ alternatingGroup (Fin 7)
    simp [otherCubic, Equiv.Perm.mem_alternatingGroup]
  apply normalizer_le_normalizer_closure
  apply mem_normalizer_fintype
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl | rfl <;> decide +kernel

private theorem cubic_residual : cubic ∈
    (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype := by
  refine ⟨⟨cubic, cubic_mem⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have ho : orderOf (⟨cubic, cubic_mem⟩ : evenPairNormalizer) = 3 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  rw [ho]
  decide
private theorem otherCubic_residual : otherCubic ∈
    (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype := by
  refine ⟨⟨otherCubic, otherCubic_mem⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have ho : orderOf (⟨otherCubic, otherCubic_mem⟩ : evenPairNormalizer) = 3 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  rw [ho]
  decide

private theorem coordinates_fixed (w : Fin 7 → ZMod 2)
    (h : representation (Fin 7) cubic w = w)
    (h' : representation (Fin 7) otherCubic w = w) :
    ∀ i : Fin 7, i ≠ 6 → w i = w 0 := by
  have h2 := congrFun h 2
  have h4 := congrFun h 4
  have h3 := congrFun h 3
  have h5 := congrFun h 5
  have h4' := congrFun h' 4
  change w 0 = w 2 at h2
  change w 2 = w 4 at h4
  change w 1 = w 3 at h3
  change w 3 = w 5 at h5
  change w 3 = w 4 at h4'
  intro i hi
  fin_cases i <;> simp_all

/-- The actual normalizer residual and six-point stabilizer have the same
fixed vectors on the full seven-letter permutation module. -/
theorem full_fixed_of_fix_six (w : Fin 7 → ZMod 2)
    (hw : ∀ r ∈ (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype,
      representation (Fin 7) r w = w)
    (b : Perm (Fin 7)) (hb : b 6 = 6) :
    representation (Fin 7) b w = w := by
  have hf := hb
  have hc := coordinates_fixed w (hw _ cubic_residual) (hw _ otherCubic_residual)
  ext i
  change w (b.symm i) = w i
  by_cases hi : i = 6
  · subst i
    rw [b.symm_apply_eq.mpr hf.symm]
  · have hbi : b.symm i ≠ 6 := by
      intro he
      have hi' := congrArg b he
      simp only [b.apply_symm_apply, hf] at hi'
      exact hi hi'
    exact (hc _ hbi).trans (hc _ hi).symm

/-- Transport the fixed-space comparison to the literal odd natural module. -/
theorem natural_fixed_of_fix_six (w : natural (Fin 7))
    (hw : ∀ r ∈ (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype,
      naturalRepresentation (Fin 7) r w = w)
    (b : Perm (Fin 7)) (hb : b 6 = 6) :
    naturalRepresentation (Fin 7) b w = w := by
  let e := coreEquivNatural (Fin 7) (by decide : Odd (Fintype.card (Fin 7)))
  let u := e.symm w
  have hu (r : Perm (Fin 7)) (hr : r ∈
      (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype) :
      coreRepresentation (Fin 7) r u = u := by
    apply e.injective
    rw [coreEquivNatural_equivariant, LinearEquiv.apply_symm_apply, hw r hr]
  have hf := full_fixed_of_fix_six u.val (fun r hr => congrArg Subtype.val (hu r hr)) b hb
  have hc : coreRepresentation (Fin 7) b u = u := Subtype.ext hf
  have ht := congrArg e hc
  rw [coreEquivNatural_equivariant, LinearEquiv.apply_symm_apply] at ht
  exact ht

/-- Equality with the fixed space of the full six-letter stabilizer. -/
theorem natural_fixedSpace_eq :
    fixedSpace (naturalRepresentation (Fin 7))
      ((pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype) =
    fixedSpace (naturalRepresentation (Fin 7))
      (MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)) := by
  apply le_antisymm
  · intro w hw b
    exact natural_fixed_of_fix_six w (fun r hr => hw ⟨r, hr⟩) b.val b.property
  · intro w hw r
    exact hw ⟨r.val, normalizer_threeTranspositions_fix_six
      ((map_subtype_le (pResidual 2 evenPairNormalizer) r.property).2)⟩

/-- The literal A₆ replacement stabilizer fixes every vector fixed by the
source normalizer residual. -/
theorem natural_fixed (w : natural (Fin 7))
    (hw : ∀ r ∈ (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype,
      naturalRepresentation (Fin 7) r w = w)
    (b : alternatingGroup (Fin 7)) (hb : b ∈ sixStabilizer 6) :
    naturalRepresentation (Fin 7) b.val w = w :=
  natural_fixed_of_fix_six w hw b.val ((mem_sixStabilizer_iff 6 b).mp hb)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixFixed
