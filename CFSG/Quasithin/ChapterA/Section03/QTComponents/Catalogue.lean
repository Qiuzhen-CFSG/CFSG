module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.RemainingRows
public import Theory.Quasithin.LocalRankEmbedding

/-!
# The five-row nonnormal-component shortlist at the local rank budget

A centerless nonnormal component has local plus ordinary rank at most two
at each odd prime. The complete Theorem C inspection uses independent
model-local inputs for odd signed degree three, binary degree three, and
positive local cubic rank in the remaining finite and binary rows. The
output preserves the actual binary PSL₂, Suzuki, odd PSL₂, J₁, or binary
PSU₃ model. The three input families remain explicit until source assembly.

Source: Aschbacher–Smith A.1.34(3), A.3.8(1–2), pp.29–30 and45–46.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.QTComponents
open Chapter1.Section02
universe u v

/-- The local and ordinary ranks supplied by two distinct centerless components. -/
def OddRankBudget (S : Type u) [Group S] : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → twoLocalPrimeRank p S + primeRank p S ≤ 2

/-- The five sufficient central-quotient rows for the Hall consumer. -/
inductive NonnormalModel (S : Type u) [Group S] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (model : ClassicalGroup.IsPSL S 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (model : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | linear_odd (q : ℕ) (ho : Odd q) (model : ClassicalGroup.IsPSL S 2 q)
  | janko (model : Nonempty (S ≃* Janko1.Model))
  | unitary (n : ℕ) (hn : 0 < n) (model : ClassicalGroup.IsPSU S 3 (2 ^ n))

/-- The independent odd signed-degree-three obstruction. -/
def OddThreeBudgetInput (S : Type u) [Group S] : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → ∀ unitary : Bool,
    LocalModels.IsPSLSign S unitary 3 p → ¬ OddRankBudget S

/-- The independent binary degree-three sieve retains the actual small alias. -/
def BinaryThreeBudgetInput (S : Type u) [Group S] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ClassicalGroup.IsPSL S 3 (2 ^ n) →
    OddRankBudget S → ClassicalGroup.IsPSL S 2 7

/-- Positive local cubic ranks for the other finite and binary source rows.
The rank-two linear row remains with its separate owner. -/
structure RemainingLocalInput (S : Type u) [Group S] : Prop where
  alternating : ∀ n : ℕ, 6 ≤ n ∧ n ≤ 8 → LocalModels.IsAlternating S n →
    1 ≤ twoLocalPrimeRank 3 S
  binary_linear : ∀ n : ℕ, n = 4 ∨ n = 5 → ClassicalGroup.IsPSL S n 2 →
    1 ≤ twoLocalPrimeRank 3 S
  sporadic : ∀ name : ClassificationModels.SporadicName, name ≠ .j3 →
    Nonempty (S ≃* name.Carrier) → 1 ≤ twoLocalPrimeRank 3 S
  rank_two : LocalModels.RankTwoTheoremC S →
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL S 3 (2 ^ n)) ∨
      1 ≤ twoLocalPrimeRank 3 S

variable {S : Type u} [Group S] {H : Type v} [Group H]

theorem NonnormalModel.of_mulEquiv (h : NonnormalModel S) (e : H ≃* S) :
    NonnormalModel H := by
  cases h with
  | linear_even n hn hm => exact .linear_even n hn (hm.of_mulEquiv e)
  | suzuki m hm he => exact .suzuki m hm (he.map (e.trans ·))
  | linear_odd q ho hm => exact .linear_odd q ho (hm.of_mulEquiv e)
  | janko he => exact .janko (he.map (e.trans ·))
  | unitary n hn hm => exact .unitary n hn (hm.of_mulEquiv e)

variable [Finite S] [Finite H]

theorem OddRankBudget.of_mulEquiv (h : OddRankBudget S) (e : H ≃* S) :
    OddRankBudget H := by
  intro p hp ho
  exact (Nat.add_le_add (twoLocalPrimeRank_le_of_injective p e.toMonoidHom e.injective)
    (primeRank_le_of_injective p e.toMonoidHom e.injective)).trans (h p hp ho)

/-- All rows of the full C-list, with only the three independent model-local
inputs left explicit. -/
theorem nonnormal_model_of_budget
    (hodd : OddThreeBudgetInput S) (hbinary : BinaryThreeBudgetInput S)
    (hlocal : RemainingLocalInput S) (hr : OddRankBudget S)
    (hm : LocalModels.TheoremCModel S) : NonnormalModel S := by
  have hthree := hr 3 (by decide) (by decide)
  cases hm with
  | alternating n hn he =>
    have hn5 : n = 5 := by
      by_contra hh
      have h6 : 6 ≤ n := by omega
      have hl := hlocal.alternating n ⟨h6,hn.2⟩ he
      have hb := alternatingGroup.TwoThreeCycles.two_le_primeRank h6
      rw [← primeRank_equiv 3 he.some] at hb
      omega
    subst n
    exact .linear_even 2 (by decide)
      ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),
        ⟨he.some.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  | linear_odd p n hp ho hn _ he => exact .linear_odd (p ^ n) ho.pow he
  | three_odd p hp ho unitary he => exact (hodd p hp ho unitary he hr).elim
  | rank_one he =>
    cases he with
    | linear n hn he => exact .linear_even n hn he
    | unitary n hn he => exact .unitary n (by omega) he
    | suzuki m hm he => exact .suzuki m hm he
  | rank_two he =>
    rcases hlocal.rank_two he with ⟨n,hn,he⟩ | hl
    · exact .linear_odd 7 (by decide) (hbinary n hn he hr)
    · rcases SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows he with ⟨n,hn,he⟩ | hb
      · exact .linear_odd 7 (by decide) (hbinary n hn he hr)
      · omega
  | binary_linear n hn he =>
    have hl := hlocal.binary_linear n hn he
    have hb := SQTKStructure.NonnormalOuterSource.FourModels.binary_linear_three_rank n hn he
    omega
  | sporadic name hn he =>
    have hl := hlocal.sporadic name hn he
    let : Finite name.Carrier := Finite.of_injective he.some.symm he.some.symm.injective
    have hb := SQTKStructure.NonnormalOuterSource.FourModels.sporadic_three_rank name hn
    rw [← primeRank_equiv 3 he.some] at hb
    omega
  | janko_one he => exact .janko he

end CFSG.Quasithin.ChapterA.QTComponents
