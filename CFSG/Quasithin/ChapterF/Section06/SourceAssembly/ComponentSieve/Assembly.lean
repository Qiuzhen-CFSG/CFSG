module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Odd
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Alternating
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenBender
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenLinear
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenExceptional
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Sporadic

/-!
# The complete small elementary Sylow sieve for Theorem C

The actual source catalogue, an elementary Sylow two-subgroup of order at
most eight, and nonsolvability leave precisely a prime-field odd PSL2,
PSL2(8), or J1. The linear odd parameters satisfy p = 3 or 5 modulo eight.
Each catalogue branch is discharged using its concrete carrier: orders
exclude the large two-parts, actual elements of order four exclude the
remaining non-elementary cases, and A5 identifies the binary rank-one
exception with PSL2(5).

Source: Aschbacher--Smith Theorem C and F.6.17, printed pp.33,309.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- All constructors of the literal Theorem C model list are discharged. -/
theorem theoremC_model_of_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 8)
    (hns : ¬ Group.IsSolvable G) (hm : ChapterA.Section02.IsTheoremCModel G) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      ClassicalGroup.IsPSL G 2 p) ∨
      ClassicalGroup.IsPSL G 2 8 ∨ Nonempty (G ≃* Janko1.Model) := by
  have hfive (h : ClassicalGroup.IsPSL G 2 5) :
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        ClassicalGroup.IsPSL G 2 p :=
    ⟨5, by decide, by decide, by decide, h⟩
  cases hm with
  | alternating n hn iso =>
    obtain ⟨e⟩ := iso
    exact .inl (hfive (alternating_model_of_small_elementary_sylow P hP hns hn e))
  | odd model => exact .inl (odd_model_of_small_elementary_sylow P hP model)
  | bender model =>
    rcases bender_small_sylow_cases P hP model with hm | hm
    · exact .inl (hfive hm)
    · exact .inr (.inl hm)
  | rank_two f model =>
    obtain ⟨_, hm⟩ := linear_of_theoremC_rankTwo_small_elementary_sylow P hP hns model
    exact (not_linear_three_binary_of_elementary_sylow P hm).elim
  | linear_binary n hn model =>
    exact (not_binary_four_or_five_of_small_sylow P hP hn model).elim
  | sporadic model =>
    exact .inr (.inr (jankoOne_of_theoremC_sporadic_small_sylow P hP model))

end CFSG.Quasithin.ChapterF.SourceAssembly
