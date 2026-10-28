module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses

/-!
# The natural A₆ configuration before the abelian-closure theorem

This interface retains the original chosen module, natural action, quotient
and Sylow flag of Hypothesis 13.7.1. It contains no conclusion about the
conjugate spans of V or V₃. The actual 13.7.8 conclusion upgrades it to the
existing Section 13.8 local setup, with every subgroup and coordinate map
unchanged. Source: Aschbacher--Smith, Hypothesis 13.7.1 and 13.7.8,
printed pp.935--946.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source configuration preceding 13.7.8, with the literal Irr⁺ choice. -/
structure NaturalSetup (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G) where
  counterexample : Counterexample T L
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  local_quotient : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)
  module_in_reduced : V ≤ Chapter6.Source.reducedSubgroup (L ⊔ (T : Subgroup G))
  coordinate : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6))
  conjugation : ∀ (l : L) (v : V),
    (coordinate (V.normalizerMonoidHom
      ⟨l.val, normalizes_V (show l.val ∈ L ⊔ (T : Subgroup G) from mem_sup_left l.property)⟩ v)).toAdd =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (local_quotient (QuotientGroup.mk' (centralCore L) l)) (coordinate v).toAdd
  line_le_plane : V₁ ≤ V₂
  plane_le_seed : V₂ ≤ V₃
  seed_le : V₃ ≤ V
  line_card : Nat.card V₁ = 2
  plane_card : Nat.card V₂ = 4
  seed_card : Nat.card V₃ = 8
  line_stable : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  plane_stable : (T : Subgroup G) ≤ normalizer (V₂ : Set G)
  seed_stable : (T : Subgroup G) ≤ normalizer (V₃ : Set G)
  first_normalizer : G₁ = normalizer (V₁ : Set G)
  local_normalizer : M = normalizer (L : Set G)
  chosen : Chapter12.Section02.ChosenModule T L V

namespace NaturalSetup
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- Apply the original abelian-closure theorem to the unchanged setup. -/
def toLocalSetup (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : IsMulCommutative (conjugateSpanBy V G₁)) :
    LocalSetup T L V V₁ V₂ V₃ M G₁ where
  counterexample := d.counterexample
  normalizes_L := d.normalizes_L
  normalizes_V := d.normalizes_V
  local_quotient := d.local_quotient
  module_in_reduced := d.module_in_reduced
  coordinate := d.coordinate
  conjugation := d.conjugation
  line_le_plane := d.line_le_plane
  plane_le_seed := d.plane_le_seed
  seed_le := d.seed_le
  line_card := d.line_card
  plane_card := d.plane_card
  seed_card := d.seed_card
  line_stable := d.line_stable
  plane_stable := d.plane_stable
  seed_stable := d.seed_stable
  first_normalizer := d.first_normalizer
  local_normalizer := d.local_normalizer
  abelian_span := h

end NaturalSetup
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
