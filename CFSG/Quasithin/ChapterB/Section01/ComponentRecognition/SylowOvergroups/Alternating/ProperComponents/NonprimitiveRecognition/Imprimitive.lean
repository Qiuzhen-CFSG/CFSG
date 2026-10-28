module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.Imprimitive.GeometryContracts

/-!
# Assembly of the transitive imprimitive alternating induction step

The genuine block system gives smaller permutation degrees. Centralizer
control puts every relative component in the block kernel. The even part
of each block image contains a Sylow subgroup, so smaller-degree induction
classifies its components; the separating block restrictions then recover
actual component isomorphisms. The geometric inputs remain explicit here.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
-/

public section
open Subgroup MulAction Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The two geometric inputs discharge every remaining premise of the
imprimitive step. This is conditional assembly, not the unconditional step. -/
theorem alternating_imprimitive_component_step_of_block_geometry (m : ℕ)
    (hcentral : AlternatingBlockCentralizerControl m)
    (hsylow : AlternatingBlockSylowGeometry m) : AlternatingImprimitiveComponentStep m := by
  intro ih S X hSX _hX ht hp D hD
  let := ht
  obtain ⟨B, hB, hBs, hBu⟩ := alternating_exists_nontrivial_block X hp
  have hne : B.Nonempty := Set.not_subsingleton_iff.mp hBs |>.nonempty
  obtain ⟨hn7, hSblocks⟩ := hsylow S X hSX ht B hB hBs hBu
  have hdegrees := alternatingBlock_degrees X hB hBs hBu
  have hmodels : ∀ C : orbit X B, ∀ E : Subgroup (alternatingBlockImage X B C),
      IsComponent (alternatingBlockImage X B C) E → AlternatingSubgroupModels m E := by
    intro C E hE
    have hcard := alternatingBlock_card_eq X C
    have hlt : Nat.card C.val < m := by rw [hcard]; exact hdegrees.2.1
    have hC7 : Nat.card C.val ≠ 7 := by rwa [hcard]
    obtain ⟨T, hT⟩ := hSblocks C
    exact alternating_component_models_of_even_preimage (ih _ hlt) hlt.le hC7
      (alternatingBlockImage X B C) (Finite.equivFin C.val) T hT E hE
  exact alternating_component_models_of_block_kernel X hne hmodels D hD
    (alternating_component_le_blockKernel_of_centralizer X B
      (hcentral S X hSX ht B hB hBs hBu) D hD)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
