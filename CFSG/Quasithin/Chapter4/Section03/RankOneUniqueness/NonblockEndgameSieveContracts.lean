module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveImages

/-!
# Outstanding source inputs for the nonblock automorphism sieve

These propositions separate the actual quotient-image geometry, the source
model inspection, and the odd-prime centralizer calculations. They are not
asserted theorems. `exceptional_of_source_inputs` assembles their conclusions
on the literal secondary action, and retains all three inputs explicitly.
The source assembly must construct them before it proves 4.3.16's surviving row.

All model predicates carry isomorphisms. The unitary row retains both SU₃ and
PSU₃, and the exceptional row retains the outer-action clause of the source.
Source: Aschbacher–Smith, original 4.3.12(2), 4.3.14–16 and the first paragraph
of the final proof of 4.3.2, printed pp.617–618; A.3.18, pp.51–52.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The first three rows of original 4.3.16, with actual matrix or J₁ models. -/
def NonexceptionalModel (J : Type*) [Group J] (n : ℕ) : Prop :=
  (∃ i : ℕ, 1 ≤ i ∧ ClassicalGroup.IsPSL J 2 (2 ^ (2 ^ i * n))) ∨
    (IsSU J 3 (2 ^ n) ∨ ClassicalGroup.IsPSU J 3 (2 ^ n)) ∨
    (n = 2 ∧ (ClassicalGroup.IsPSL J 3 5 ∨ Nonempty (J ≃* Janko1.Model)))

/-- The model conclusion requested by the parent endgame. -/
def ExceptionalModel (J : Type*) [Group J] (n : ℕ) : Prop :=
  n = 2 ∧ (ClassicalGroup.IsPSL J 3 4 ∨ ClassicalGroup.IsPSU J 3 5)

/-- The complete 4.3.16 alternatives, including the exceptional outer action. -/
def SecondaryData.SourceAlternatives (s : SecondaryData c n) : Prop :=
  NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
    (ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      (SecondaryData.torusImage s) ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥)

/-- The quotient geometry still needed by the source automorphism inspection.
All normalizers are taken in the automorphisms of the full component quotient. -/
structure SecondaryData.LocalImageData (s : SecondaryData c n) : Prop where
  secondary_model : ClassicalGroup.IsPSL
    ((SecondaryData.secondaryImage s) ⧸ pCore 2 (SecondaryData.secondaryImage s)) 2 (2 ^ n)
  normalizer_control :
    (SecondaryData.ambientImage s) ⊓ normalizer ((SecondaryData.radicalImage s) : Set _) ≤
      normalizer ((SecondaryData.secondaryImage s) : Set _)
  proper_normalizer : ¬ (SecondaryData.componentImage s) ≤ normalizer ((SecondaryData.radicalImage s) : Set _)

/-- Exactly the odd-prime automorphism exclusions consumed in rows 1–3.
They concern the actual embedded K₂-star, not an arbitrary abstract PSL₂. -/
def SecondaryData.ExcludedCentralizers (s : SecondaryData c n) : Prop :=
  NonexceptionalModel (s.component ⧸ pCore 2 s.component) n →
    ∀ p : ℕ, p.Prime → Odd p → p ∣ 2 ^ n - 1 →
      ∀ a ∈ (SecondaryData.torusImage s), a ∈ centralizer ((SecondaryData.secondaryImage s) : Set _) → orderOf a ≠ p

/-- Conditional assembly of the source sieve and its model-centralizer leaves.
This is not the unconditional source theorem: the model inputs remain explicit. -/
theorem SecondaryData.exceptional_of_source_inputs (s : SecondaryData c n)
    (hn : 1 < n) (hm : (SecondaryData.SourceAlternatives s))
    (hc : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n →
      (SecondaryData.CoreImageCentral s)) (he : (SecondaryData.ExcludedCentralizers s)) :
    n = 2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) := by
  rcases hm with hr | hr
  · exact (s.torus_action_ne_bot
      ((SecondaryData.torusImage_eq_bot_of_prime_centralizer s) (by omega) (hc hr)
        (he hr))).elim
  · exact hr.1

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
end
