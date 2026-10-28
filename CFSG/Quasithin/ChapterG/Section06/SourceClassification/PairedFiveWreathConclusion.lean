module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.MinimalParabolicComparison
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.PairedFiveWreathAction

/-!
# The paired five-factor branch with its ambient wreath action

The minimal-parabolic sieve records the two-factor natural-five branch as a
model on each factor.  The literal paired-five construction upgrades that
branch to a faithful action of the whole group on the two-core wreath model.

Source: Aschbacher--Smith G.6.4(3)(ii), pp.345--346.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open BinaryPermutation BinaryPermutation.FivePair BinaryPermutation.FiveCentralExtension

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-- The paired-five branch of the minimal-parabolic conclusion carries a
faithful literal wreath action of the ambient group.  The other catalogue
rows are retained unchanged, so this theorem can be consumed directly by the
subsequent source sieve. -/
theorem minimal_parabolic_model_conclusion_with_paired_five_wreath
    [Finite G]
    (h : MinimalParabolicModelConclusion ρ a)
    (hf : Function.Injective ρ) :
    HasModelOn ρ ⊤ ⊤ (binaryLinearAction 2) ∨
    HasModelOn ρ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 5)) ∨
    (∃ d : TwoFactors ρ a,
      (HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
          (binaryLinearAction 2) ∧
        HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
          (binaryLinearAction 2) ∧
        Module.finrank (ZMod 2) V = 4) ∨
      (HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
          (BinaryPermutation.naturalRepresentation (Fin 5)) ∧
        HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
          (BinaryPermutation.naturalRepresentation (Fin 5)) ∧
        ∃ (c : V ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core))
          (q : G →* FivePair.Wreath) (e : G ≃* FivePair.Wreath),
          Function.Injective q ∧ Function.Surjective q ∧
          (∀ z : FiveCentralExtension.Sym × FiveCentralExtension.Sym,
            ∃ x : G, q x = FivePair.base z) ∧
          (∀ g v, c (ρ g v) = FivePair.wreathRepresentation (e g) (c v)))) := by
  rcases h with h₂ | h₅ | ⟨d, hd⟩
  · exact Or.inl h₂
  · exact Or.inr (Or.inl h₅)
  · rcases hd with h₂pair | h₅pair
    · exact Or.inr (Or.inr ⟨d, Or.inl h₂pair⟩)
    · obtain ⟨c, q, e, hqi, hqs, hbase, hact⟩ :=
        d.exists_paired_five_wreath_action h₅pair.1 h₅pair.2 hf
      exact Or.inr (Or.inr ⟨d, Or.inr ⟨h₅pair.1, h₅pair.2,
        c, q, e, hqi, hqs, hbase, hact⟩⟩)

end CFSG.Quasithin.ChapterG.Section06
