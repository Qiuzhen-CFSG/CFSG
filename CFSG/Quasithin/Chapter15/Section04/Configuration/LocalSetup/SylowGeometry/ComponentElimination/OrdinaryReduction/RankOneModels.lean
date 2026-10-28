module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Comparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Sporadic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour

/-!
# Ordinary rank-one seeds and their inner actions

The actual rank-one quotient rules out the alternating actions, and the
odd-core hypothesis identifies the component center with its two-core.
This proves every source actor has an inner witness in the seed itself.
The central-cover and small odd-linear alternatives are excluded by their
orders. The full characteristic-two comparison restricts the odd parameter
to Fermat or Mersenne primes, and the concrete sporadic comparisons exclude
the remaining models. The final theorem assembles these comparisons to
identify the seed itself, retaining its given even exponent or odd prime.

Source: Aschbacher–Smith, full 1.1.5(3), printed pp.501–503, and the proof
of 15.4.20, printed p.1164. The parent OrdinaryReduction module owns the
construction of the component seed and the final pair assembly.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open OrdinaryReduction OrdinaryReduction.RankOneModels ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Assemble the model contract from the two independent comparisons.
The theorem below supplies both comparisons. -/
theorem rank_one_models_of_comparisons
    (hlie : ∀ {Q : Type u} [Group Q] [Finite Q] {p : ℕ}, p.Prime → Odd p → 5 ≤ p →
      ClassicalGroup.IsPSL Q 2 p → LieTypeTwoModel Q → IsFermatOrMersennePrime p)
    (hfour : ∀ (name : SporadicName),
      (name = .j2 ∨ name = .j4 ∨ name = .he ∨ name = .ru) → ∀ {q : ℕ},
      ((∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) →
      ¬ ClassicalGroup.IsPSL name.Carrier 2 q)
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) (earlier : Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (b : PairEmbedding H K U)
    (hodd : pPrimeCore 2 H = ⊥) (hcomponent : IsComponent H b.seed) :
    OrdinaryRankOneModel b.seed ∧ CentralInnerAction (b.seed.map H.subtype) d.Z := by
  let : IsQuasisimple b.seed := hcomponent.2
  let : Nontrivial d.Z := Finite.one_lt_card_iff_nontrivial.mp (by rw [s.four]; decide)
  obtain ⟨z,hz⟩ := exists_ne (1 : d.Z)
  obtain ⟨P,M,hlocal⟩ := s.local115 z z.property (fun he => hz (Subtype.ext he))
  obtain ⟨_,_,α,_,ha⟩ := earlier hG H P M z hlocal b.seed hcomponent
  refine ⟨ordinary_model_of_comparisons hlie (sporadic_separation_of_four hfour)
    b.model (Chapter15.Section03.component_center_eq_twoCore hcomponent hodd) ha, ?_⟩
  exact rank_one_seed_inner hG earlier s b hodd hcomponent

/-- The ordinary rank-one seed has an actual PSL₂ model, and every element
of the marked central four-group acts by an element of that same seed.
All six alternatives of 1.1.5(3) and every model comparison are discharged;
the parent supplies the odd-core and ordinary-component hypotheses. -/
theorem rank_one_models_of_ordinary
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) (earlier : Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (b : PairEmbedding H K U)
    (hodd : pPrimeCore 2 H = ⊥) (hcomponent : IsComponent H b.seed) :
    OrdinaryRankOneModel b.seed ∧ CentralInnerAction (b.seed.map H.subtype) d.Z := by
  exact rank_one_models_of_comparisons lie_odd_parameter sporadic_four_separation
    hG earlier s b hodd hcomponent

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
