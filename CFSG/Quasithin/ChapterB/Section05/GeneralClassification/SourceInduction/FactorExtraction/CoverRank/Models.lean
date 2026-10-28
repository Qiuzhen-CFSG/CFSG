module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Symmetric-three subgroups in the five B.5.9 component cases

The binary prime field embeds in every specified binary field. The genuine
SL₂(2) isomorphism with S₃ therefore embeds S₃ in SL₂(F), and the
determinant-corrected block map embeds it in SL₃(F). Extending permutations
from three to five letters supplies the S₅ case. Transport along the actual
action equivalences covers all five component alternatives, including the
central quotient in the four-dimensional cover case.

This supplies the subgroup used with A.1.31(1) in the proof of B.5.11.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9–11,
printed pp.107–109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource
universe u v

private theorem binary_sl2_contains_symmetricThree (F : BinaryField) :
    ∃ f : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) F.Carrier,
      Function.Injective f := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap (ZMod 2) F.Carrier)
  have hf : Function.Injective f := by
    intro x y h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply (algebraMap (ZMod 2) F.Carrier).injective
    exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F.Carrier => g i j) h
  exact ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.injective⟩

private theorem binary_sl3_contains_symmetricThree (F : BinaryField) :
    ∃ f : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier,
      Function.Injective f := by
  obtain ⟨f, hf⟩ := binary_sl2_contains_symmetricThree F
  exact ⟨(Matrix.SL3.blockEmbedding F.Carrier).comp
      (Matrix.SpecialLinearGroup.toGL.comp f),
    (Matrix.SL3.blockEmbedding_injective F.Carrier).comp
      (Matrix.SpecialLinearGroup.toGL_injective.comp hf)⟩

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every first factor in B.5.9 contains an actual copy of S₃. -/
theorem ComponentActionCase.exists_symmetricThree_embedding {A L H : Subgroup G}
    {s : MovedSection ρ L} (hc : ComponentActionCase ρ A L s H) :
    ∃ f : Equiv.Perm (Fin 3) →* H, Function.Injective f := by
  cases hc with
  | linearTwo F natural _ _ =>
    obtain ⟨e⟩ := natural
    obtain ⟨f, hf⟩ := binary_sl2_contains_symmetricThree F
    exact ⟨e.groupEquiv.symm.toMonoidHom.comp f, e.groupEquiv.symm.injective.comp hf⟩
  | symmetricFive action _ _ =>
    let i : Fin 3 ↪ Fin 5 := ⟨Fin.castLE (by decide), Fin.castLE_injective _⟩
    exact ⟨action.action.groupEquiv.symm.toMonoidHom.comp (Equiv.Perm.viaEmbeddingHom i),
      action.action.groupEquiv.symm.injective.comp (Equiv.Perm.viaEmbeddingHom_injective i)⟩
  | doubleThree F _ natural _ _ =>
    obtain ⟨e⟩ := natural
    obtain ⟨f, hf⟩ := binary_sl3_contains_symmetricThree F
    exact ⟨e.groupEquiv.symm.toMonoidHom.comp f, e.groupEquiv.symm.injective.comp hf⟩
  | naturalThree F _ natural _ =>
    obtain ⟨e⟩ := natural
    obtain ⟨f, hf⟩ := binary_sl3_contains_symmetricThree F
    exact ⟨e.groupEquiv.symm.toMonoidHom.comp f, e.groupEquiv.symm.injective.comp hf⟩
  | fourCover cover _ _ _ =>
    obtain ⟨f, hf⟩ := binary_sl3_contains_symmetricThree BinaryField.two
    exact ⟨cover.natural.groupEquiv.symm.toMonoidHom.comp f,
      cover.natural.groupEquiv.symm.injective.comp hf⟩
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
