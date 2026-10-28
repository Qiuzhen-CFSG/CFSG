module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsOuter

/-!
# Source-record application of the corrected nonblock sieve

The corrected secondary witness supplies every local-image geometry clause
on its literal normalQuotientAction. The checked core-movement row arguments
exclude binary PSL₂, both unitary forms, J₁ and PSL₃(5), provided the same
whole-radical generation identity is supplied. The exceptional models then
force the original torus to act outerly by the prime-rank argument.

The final theorem is conditional on four-row model inspection and generation.
It discharges the earlier centrality, prime-centralizer and outer-action
premises, but is not the unconditional 4.3.16 classification. The sieve owner
retains model inspection; the nonblock source owner retains construction and
whole-radical generation. No conversion to legacy SecondaryData is used.
Source: Aschbacher--Smith, original 4.3.12--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}
namespace SecondarySourceData

/-- The three geometric premises of the source automorphism inspection. -/
structure LocalImageData (s : SecondarySourceData c n) : Prop where
  secondary_model : ClassicalGroup.IsPSL
    (secondaryImage s ⧸ pCore 2 (secondaryImage s)) 2 (2^n)
  normalizer_control : ambientImage s ⊓ normalizer (radicalImage s : Set _) ≤
    normalizer (secondaryImage s : Set _)
  proper_normalizer : ¬ componentImage s ≤ normalizer (radicalImage s : Set _)

/-- The four source model rows, retaining the exceptional outer-action clause. -/
def SourceAlternatives (s : SecondarySourceData c n) : Prop :=
  NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
    (ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥)

/-- The literal source witness discharges every local-image geometry premise. -/
theorem localImageData (s : SecondarySourceData c n)
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
theorem not_binary_of_generation (s : SecondarySourceData c n)
    (hg : ActionGeneration s) {m : ℕ}
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2^m)) : False := by
  let := s.normal
  exact s.radical_action (SourceImages.binary_radical_eq_bot c s.component hm s.torus
    s.secondary_le s.radical_le s.torus_le s.radical_normalizer
    (SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model)
    s.torus_secondary s.core_moved hg)

/-- Both unitary forms retain the full quotient and faithful descent of the cover. -/
theorem not_unitary_of_generation (s : SecondarySourceData c n) (hn : 1 < n)
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
theorem odd_rows_torus_eq_bot (s : SecondarySourceData c 2)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5 ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Janko1.Model)) : torusImage s = ⊥ := by
  let := s.normal
  let := s.quasisimple
  exact SourceImages.odd_rows_torus_eq_bot c s.component s.secondary_le s.secondary_model hm
    s.torus s.torus_le s.torus_card s.torus_secondary

/-- Generation excludes all three nonexceptional rows on the corrected witness. -/
theorem not_nonexceptional_of_generation (s : SecondarySourceData c n) (hn : 1 < n)
    (hg : ActionGeneration s)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n) : False := by
  let := s.normal
  let := s.quasisimple
  exact s.radical_action (SourceImages.nonexceptional_radical_eq_bot c s.component
    s.secondary_le hn s.secondary_model hm s.torus s.radical_le s.torus_le
    s.radical_normalizer s.torus_card s.torus_secondary s.core_moved hg)

/-- The actual model gives the exceptional outer clause; it need not be assumed. -/
theorem sourceAlternatives_of_model_alternatives (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      ExceptionalModel (s.component ⧸ pCore 2 s.component) n) : SourceAlternatives s := by
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr ⟨hm,exceptional_model_outer_torus s D h hm⟩

/-- Source-correct counterpart of the legacy conditional sieve. Model inspection
and whole-radical generation are the only remaining mathematical inputs. -/
theorem exceptional_of_source_inputs (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n) (hg : ActionGeneration s)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      ExceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    (n = 2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  rcases sourceAlternatives_of_model_alternatives s D h hm with hm | hm
  · exact (not_nonexceptional_of_generation s hn hg hm).elim
  · exact hm

end SecondarySourceData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
