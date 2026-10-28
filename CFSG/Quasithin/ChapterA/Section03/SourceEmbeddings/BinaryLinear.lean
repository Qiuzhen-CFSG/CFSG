module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SylowOvergroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.HigherLinear
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.EightKernel

/-!
# Quasisimple local components in the binary linear four and five models

In degree four, the invariant-subspace calculation places every proper
full-Sylow overgroup in a subspace parabolic. Its binary radical is
self-centralizing, so the overgroup has characteristic two. The degree-five
flag calculation already supplies the same generalized Fitting bound.
A quasisimple local C-component in either model must therefore be the whole
containing component. The resulting A.3.12 conclusion keeps its uniqueness
assertion and the original subgroups.

Source: Aschbacher–Smith A.3.12(4–5), printed pp.47–48, and the binary
smaller-component application in C.5.13, printed p.163.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterB.ComponentRecognition.SylowOvergroups
variable {G : Type*} [Group G] [Finite G]

/-- Every proper full-Sylow overgroup in the literal PSL₄(2) carrier has
its generalized Fitting subgroup inside its two-core. -/
theorem binary_linear_four_properSylowFittingBound :
    ProperSylowFittingBound PSL(4, ZMod 2) := by
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 4) :=
    Finite.of_injective
      (fun g : BinaryLinear.OuterCyclic.LinearGroup 4 => (g : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2)))
      DFunLike.coe_injective
  apply properSylowFittingBound_of_equiv
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  intro S X hSX hX
  obtain ⟨W, hW, hWt, hXP⟩ := exists_invariant_subspace S X hSX hX
  rw [generalizedFitting_eq_pCore_of_sylow_le_normalizer S X
    (BinaryLinear.parabolic W) (BinaryLinear.radical W) hSX hXP
    (BinaryLinear.radical_le_parabolic W) (BinaryLinear.parabolic_le_normalizer W)
    (BinaryLinear.radical_two W) (BinaryLinear.centralizer_radical_le hW hWt)]
  exact le_sup_left

/-- The two binary higher-linear source rows cannot contain a proper
quasisimple smaller local C-component. This needs the full Sylow, with no
assumption that its entire Borel normalizer is present. -/
theorem eq_of_binary_linear_four_or_five
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hmodel : ClassicalGroup.IsPSL L d 2) : B = L := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  apply ChapterC.Section05.NormalizerControl.EmbeddingSelection.eq_of_proper_sylow_fitting_bound
    T hB hL hBL
  apply properSylowFittingBound_of_equiv (e.trans (Atlas.fieldEquivPSL d f))
  rcases hd with rfl | rfl
  · exact binary_linear_four_properSylowFittingBound
  · exact properSylowFittingBound_psl5_two

/-- The complete original A.3.12 conclusion for these containing-model rows
and a quasisimple smaller component, including uniqueness. -/
theorem conclusion_of_binary_linear_four_or_five
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hmodel : ClassicalGroup.IsPSL L d 2) : Chapter1.Section02.A312Conclusion B := by
  have he := eq_of_binary_linear_four_or_five T hB hL hBL hd hmodel
  refine ⟨L, hL, hBL, ?_, Chapter1.Section02.A312Embedding.one he⟩
  intro D hD hBD
  exact (hL.eq_of_le hD (he ▸ hBD)).symm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
