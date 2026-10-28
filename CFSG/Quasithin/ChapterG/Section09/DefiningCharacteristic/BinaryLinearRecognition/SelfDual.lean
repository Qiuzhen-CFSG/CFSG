module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition
public import Theory.Representation.BinaryLinearRecognition.SelfDual
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight.PermutationComparison

/-!
# Self-dual binary linear components in G.9

The PSL4(2) natural row is incompatible with self-duality, leaving its
literal A8 deleted permutation action. The sharp degree bound also excludes
PSL5(2): its degree-five natural action is not self-dual, and degree ten
exceeds the actual actor bound. The component action is retained throughout.

Source: Aschbacher–Smith G.9.3(11–13), G.11.6–8, printed pp.354,366–369.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition
open Representation.BinaryLinearRecognition
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {C : GroupClass} {ρ : Representation (ZMod 2) D V} {L A : Subgroup D} {m : ℕ}

/-- The self-dual PSL4(2) component has the actual natural A8 action. -/
theorem four_alternating_natural_of_selfDual
    (h : ComponentHypothesis C ρ A L L m)
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
    (e : L ≃* PSL(4, ZMod 2)) :
    Quasiequivalent (ρ.comp L.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) := by
  rcases four_alternatives h e with hnat | horth
  · exact (not_natural_degree_of_selfDual (ρ.comp L.subtype)
      (h.faithful.comp L.subtype_injective) hs (by decide) e hnat.2.1).elim
  · obtain ⟨E,f,hf⟩ := horth.1
    let c := naturalEightOrthogonalEquiv
    refine ⟨E,f.trans c.symm,?_⟩
    intro x w
    apply c.injective
    change c (c.symm (f (ρ x w))) =
      c (BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (E x) (c.symm (f w)))
    rw [c.apply_symm_apply,naturalEightOrthogonalEquiv_alternating,c.apply_symm_apply]
    exact hf x w

/-- The sharp actor-degree bound excludes self-dual PSL5(2) components. -/
theorem not_five_of_selfDual_sharp_degree
    (h : ComponentHypothesis C ρ A L L m)
    (hd : Module.finrank (ZMod 2) V ≤ m+2)
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
    (e : L ≃* PSL(5, ZMod 2)) : False := by
  have hb := five_degree_parameters h e
  rcases hb.2 with h5 | h10
  · exact not_natural_degree_of_selfDual (ρ.comp L.subtype)
      (h.faithful.comp L.subtype_injective) hs (by decide) e h5.1
  · omega
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition

