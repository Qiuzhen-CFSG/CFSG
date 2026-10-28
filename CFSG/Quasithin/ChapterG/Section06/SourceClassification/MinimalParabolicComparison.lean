module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.MinimalParabolicModels
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorModelComparison
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorMinimalParabolic

/-!
# Minimal parabolic models in the transvection catalogue

Apply unique maximality to the one-factor G.6.4 models and to the intrinsic
Sylow of a three-dimensional factor in the two-factor case. The survivors
are the marked natural actions of GL₂(2) and S₅, singly or in an exchanged
pair. Conjugation transports the first factor's marked action to the second;
in the binary-plane pair the full module has dimension four.

This supplies the group and module comparison in Aschbacher--Smith 10.2.1,
printed p.743. The original paired geometry separately excludes the single
GL₂(2) case, and the maximal-local argument separately excludes the S₅ cases.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-- The surviving G.6.4 actions, with the original factors and moved spaces. -/
def MinimalParabolicModelConclusion (ρ : Representation (ZMod 2) G V) (a : G) : Prop :=
  HasModelOn ρ ⊤ ⊤ (binaryLinearAction 2) ∨
  HasModelOn ρ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 5)) ∨
  ∃ d : TwoFactors ρ a,
    (HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2) ∧
      HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second) (binaryLinearAction 2) ∧
      Module.finrank (ZMod 2) V = 4) ∨
    (HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
        (BinaryPermutation.naturalRepresentation (Fin 5)) ∧
      HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
        (BinaryPermutation.naturalRepresentation (Fin 5)))

/-- Unique Sylow maximality removes precisely the higher-rank catalogue rows. -/
theorem conclusion_models_of_minimal_parabolic [Finite G] [Module.Finite (ZMod 2) V]
    (h : Conclusion ρ a) (hf : Function.Injective ρ) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) : MinimalParabolicModelConclusion ρ a := by
  have hmain : OneFactor ρ a ∨ Nonempty (TwoFactors ρ a) := h.1
  rcases hmain with h | hd
  · rcases one_factor_minimal_parabolic_models h T hP with h₂ | h₅
    · exact Or.inl h₂
    · exact Or.inr (Or.inl h₅)
  · obtain ⟨d⟩ := hd
    refine Or.inr (Or.inr ?_)
    refine ⟨d, ?_⟩
    obtain ⟨t, _, _, _, ht⟩ := d.extension
    rcases d.first_model with h₂ | h₃ | h₅
    · have h₂' := h₂.conjugate_moved t ht
      exact Or.inl ⟨h₂, h₂', d.toTwoFactorModules.binary_planes_finrank h₂ h₂'⟩
    · exact (d.not_binary_three_first hf T hP h₃).elim
    · exact Or.inr ⟨h₅, h₅.conjugate_moved t ht⟩

/-- The exact source hypotheses supply finiteness and faithfulness to the sieve. -/
theorem Hypotheses.minimal_parabolic_models {κ : GroupClass.{u}}
    {Cover : Type u} [Group Cover] {q : Cover →* G}
    (h : Hypotheses κ ρ a q) (hc : Conclusion ρ a) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) : MinimalParabolicModelConclusion ρ a := by
  let := h.finite_group
  let := h.finite_module
  exact conclusion_models_of_minimal_parabolic hc h.faithful T hP

end CFSG.Quasithin.ChapterG.Section06
