module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Contracts
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Torus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocal

/-!
# Assembly of the local Cartan centralization and module arguments

The original component witness gives a member of the local component family.
If it fails to centralize omega, the FF reduction produces the maximal A₇
configuration, which the block and torus argument excludes. Centralization
then makes the outside subgroup H centralize omega. Source uniqueness
eliminates the fixed space of the original reduced module and its layer.

The final module recognition remains a separate source argument. The assembly
below keeps all three unproved source implications explicit and feeds its
result to the actual relocation consumer. It does not assert an unconditional
inhabitant of `LocalCartanCentralization`.

Source: Aschbacher--Smith, 5.1.13, printed pp.637--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Centralization of the witnessed component supplies both fixed-space
vanishings on the original W, without a further uniqueness premise. -/
theorem localCartanCentralization_fixed_spaces
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D) (hXC : X ≤ omegaCentralizer T) :
    W ⊓ centralizer (L : Set G) = ⊥ ∧
      layer L W ⊓ centralizer (L : Set G) = ⊥ := by
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp
    (d.residual_le.trans hXC)
  exact ⟨h.reduced_fixed_eq_bot_of_outside_centralizes hH hHC,
    h.layer_fixed_eq_bot_of_outside_centralizes hH hHC⟩

/-- The two independent noncentral arguments prove omega-centralization.
This implication imposes no module-recognition premise. -/
theorem localCartan_centralizes_of_ff_and_a7
    (hff : LocalCartanFFReduction G) (ha7 : LocalCartanA7Exclusion G)
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) : X ≤ omegaCentralizer T := by
  by_contra hn
  obtain ⟨K, hk⟩ := hff T L W n h H hH hgen A B c Y hY X D d hn
  exact ha7 T L W n h H hH hgen A B c Y hY X D d K hk

/-- The source cuts assemble the unchanged universal task contract. Each
cut still requires its producer; this is not the source theorem itself. -/
theorem localCartanCentralization_of_source_steps
    (hff : LocalCartanFFReduction G) (ha7 : LocalCartanA7Exclusion G)
    (hm : LocalCartanModuleRecognition G) :
    LocalCartanCentralization KnownSimple.IsKnownSimple G := by
  intro T L W n h H hH hgen A B c Y hY X D d
  have hc := localCartan_centralizes_of_ff_and_a7 hff ha7 h hH hgen c hY d
  exact ⟨hc, hm T L W n h H hH hgen A B c Y hY X D d hc⟩

/-- The literal source consumer reuses the independent sieve at the original
overgroup and again at the omega centralizer. No relocation catalogue is added. -/
theorem sourceLocalCartanEscape_of_local_source_steps
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (hff : LocalCartanFFReduction G) (ha7 : LocalCartanA7Exclusion G)
    (hm : LocalCartanModuleRecognition G) :
    SourceLocalCartanEscape KnownSimple.IsKnownSimple G :=
  sourceLocalCartanEscape_of_sieve_and_centralization hsieve
    (localCartanCentralization_of_source_steps hff ha7 hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
