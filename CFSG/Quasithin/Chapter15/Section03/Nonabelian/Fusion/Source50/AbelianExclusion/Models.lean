module
public import CFSG.Quasithin.ChapterG.Section06.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.G64Source

/-!
# The central clause of source G.6.4 in action coordinates

The original classification supplies marked models on the full subgroup and
full subspace. Their canonical top equivalences give the action-model
interface used by 15.3.52 and the constituent actions in 15.3.58. This is a
transport of the proved source theorem; no classification callback is assumed.

Source: Aschbacher–Smith, G.6.4(4), printed pp.345–346.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
open ChapterG.Section06
open Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
universe u w z
variable {A : Type u} [Group A] {E : Type u} [AddCommGroup E] [Module (ZMod 2) E]

theorem actionModel_of_top_model
    (ρ : Representation (ZMod 2) A E)
    {B : Type w} [Group B] {F : Type z} [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) B F)
    (h : HasModelOn ρ ⊤ ⊤ σ) : HasActionModel ρ σ := by
  obtain ⟨eA, eE, stable, he⟩ := h
  let jA : A ≃* (⊤ : Subgroup A) := {
    toFun := fun a => ⟨a, mem_top a⟩
    invFun := Subtype.val
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let jE : E ≃ₗ[ZMod 2] (⊤ : Submodule (ZMod 2) E) := {
    toFun := fun v => ⟨v, Submodule.mem_top⟩
    invFun := Subtype.val
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  refine ⟨jA.trans eA, jE.trans eE, ?_⟩
  intro a v
  exact he ⟨a, mem_top a⟩ ⟨v, Submodule.mem_top⟩

theorem central_alternative_of_source_model
    (ρ : Representation (ZMod 2) A E) (h : CentralModel ρ) :
    G64CentralAlternative ρ := by
  rcases h with ⟨n, hn, hn', hm⟩ | hm | hm | hm
  · exact Or.inl ⟨n, hn, hn', actionModel_of_top_model ρ _ hm⟩
  · exact Or.inr (Or.inl (actionModel_of_top_model ρ _ hm))
  · exact Or.inr (Or.inr (Or.inl (actionModel_of_top_model ρ _ hm)))
  · exact Or.inr (Or.inr (Or.inr (actionModel_of_top_model ρ _ hm)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
