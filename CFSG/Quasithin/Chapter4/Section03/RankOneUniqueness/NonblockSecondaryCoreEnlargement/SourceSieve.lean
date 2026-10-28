module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceConstruction

/-!
# Initial model exclusions without strict enlargement

The source data supply the three literal local-image premises. Movement
of Q and generation by Q and [R₂,K₂] exclude the binary rank-one,
unitary and odd nonexceptional rows. These reuse the subgroup-level
SourceImages proofs, with no stronger secondary record or universal
torus movement. The full automorphism catalogue and both exceptional
terminal rows remain separate obligations.
Source: Aschbacher–Smith, original 4.3.12–16, printed pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
namespace SecondaryActionData

/-- The three geometric premises of the source automorphism inspection. -/
structure LocalImageData (s : SecondaryActionData c n) : Prop where
  secondary_model : ClassicalGroup.IsPSL
    (secondaryImage s ⧸ pCore 2 (secondaryImage s)) 2 (2^n)
  normalizer_control : ambientImage s ⊓ normalizer (radicalImage s : Set _) ≤
    normalizer (secondaryImage s : Set _)
  proper_normalizer : ¬ componentImage s ≤ normalizer (radicalImage s : Set _)

/-- The literal source witness discharges every local-image geometry premise. -/
theorem localImageData (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) : LocalImageData s := by
  let := s.normal
  let := s.quasisimple
  obtain ⟨hm,hn,hp⟩ := SourceImages.local_image_geometry c s.component s.secondary_le
    s.isComponent.perfect D s.secondary_model s.torus s.enlarged_core_le
    s.radical_le s.radical_normalizer s.radical_action
  refine ⟨hm,?_,?_⟩
  · rw [ambientImage,componentImage_eq_inner]
    exact hn
  · rw [componentImage_eq_inner]
    exact hp

/-- The corrected source binary row uses core movement and explicit generation. -/
theorem not_binary_of_generation (s : SecondaryActionData c n)
    (hg : ActionGeneration s) {m : ℕ}
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2^m)) : False := by
  let := s.normal
  exact s.radical_action (SourceImages.binary_radical_eq_bot c s.component hm s.torus
    s.secondary_le s.radical_le s.torus_le s.radical_normalizer
    (SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model)
    s.torus_secondary s.core_moved hg)

/-- Both unitary forms retain the full quotient and faithful descent of the cover. -/
theorem not_unitary_of_generation (s : SecondaryActionData c n) (hn : 1 < n)
    (hg : ActionGeneration s)
    (hm : Chapter1.Section02.LocalModels.IsSU (s.component ⧸ pCore 2 s.component) 3 (2^n) ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2^n)) : False := by
  let := s.normal
  let := s.quasisimple
  exact s.radical_action (SourceImages.unitary_radical_eq_bot c s.component hn hm s.torus
    s.secondary_le s.radical_le s.torus_le s.radical_normalizer
    (SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model)
    s.core_moved hg)

/-- The odd rows kill the literal torus image, before any generation premise. -/
theorem odd_rows_torus_eq_bot (s : SecondaryActionData c 2)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5 ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Janko1.Model)) : torusImage s = ⊥ := by
  let := s.normal
  let := s.quasisimple
  exact SourceImages.odd_rows_torus_eq_bot c s.component s.secondary_le s.secondary_model hm
    s.torus s.torus_le s.torus_card s.torus_secondary

/-- Generation excludes all three nonexceptional rows on the corrected witness. -/
theorem not_nonexceptional_of_generation (s : SecondaryActionData c n) (hn : 1 < n)
    (hg : ActionGeneration s)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n) : False := by
  let := s.normal
  let := s.quasisimple
  exact s.radical_action (SourceImages.nonexceptional_radical_eq_bot c s.component
    s.secondary_le hn s.secondary_model hm s.torus s.radical_le s.torus_le
    s.radical_normalizer s.torus_card s.torus_secondary s.core_moved hg)

end SecondaryActionData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
