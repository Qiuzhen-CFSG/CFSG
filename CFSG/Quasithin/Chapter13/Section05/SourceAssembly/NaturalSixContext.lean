module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup

/-!
# Natural-six source data before recognition

This is the natural-action and flag data used in 13.5.12, with Hypothesis
13.3.1 and the stated Sp₆(2) exclusion. In particular it does not exclude
U₄(3). The adapter to the existing counterexample setup is used only inside
a proof by contradiction against that recognition conclusion. It preserves
the actual central quotient, conjugation action, Irr⁺ choice and flag.

The construction of this data from the preceding source hypotheses remains
with the 13.5 preparation argument. No closure or recognition is a field.
Source: Aschbacher–Smith, 13.5.3 and 13.5.12, printed pp.916 and918.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.SourceAssembly
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original natural-six configuration without the U₄(3) exclusion. -/
structure NaturalSixContext (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G) where
  hypothesis : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L
  no_symplectic_six : ¬ ClassicalGroup.IsPSp G 3 2
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

namespace NaturalSixContext
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- Retain all original data when negating the proposed U₄(3) conclusion. -/
def toNaturalSetup (d : NaturalSixContext T L V V₁ V₂ V₃ M G₁)
    (hnot : ¬ ClassicalGroup.IsPSU G 4 3) :
    NaturalSetup T L V V₁ V₂ V₃ M G₁ where
  counterexample := {
    qtke := d.hypothesis.qtke
    local_component := d.hypothesis.local_component
    no_larger_field := d.hypothesis.no_larger_field
    no_linear := d.hypothesis.no_linear
    no_alternating_nine := d.hypothesis.no_alternating_nine
    no_sporadic := d.hypothesis.no_sporadic
    five_minimal := d.hypothesis.five_minimal
    no_symplectic_six := d.no_symplectic_six
    no_unitary_four := hnot }
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
  chosen := d.chosen

/-- Recover the positive source data from an existing natural counterexample.
This lets the Section 13.7 consumer use recognition without changing its flag. -/
def ofNaturalSetup (d : NaturalSetup T L V V₁ V₂ V₃ M G₁) :
    NaturalSixContext T L V V₁ V₂ V₃ M G₁ where
  hypothesis := Chapter14.Section03.FaithfulSource.hypothesis1331 d.counterexample
  no_symplectic_six := d.counterexample.no_symplectic_six
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
  chosen := d.chosen

end NaturalSixContext
end CFSG.Quasithin.Chapter13.Section05.SourceAssembly
