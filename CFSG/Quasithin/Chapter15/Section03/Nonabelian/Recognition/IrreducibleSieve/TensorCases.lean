module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.Models
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.ParityAndCenter
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.RankOne
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.SplitFour

/-!
# Orthogonal and twisted tensor sieve for 15.3.58

The model interface retains the literal actions in G.9.3(7),(14)--(17),
with the corrected component-action formulation of (14). Parity excludes
(14), and the actual central kernel of the half-field tensor excludes (17).
For (7), (15), and (16), pointwise Sylow-fixer calculations and the faithful
irreducible binary centralizer argument place the marked involution in the
component join. The actual Hermitian, split orthogonal, and triple tensor
actions then force displacement greater than two. Combining these exclusions
gives the contradiction for all five alternatives, with no extra model premises.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3,
printed pp.353--357, and 15.3.58, printed p.1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- Parity and the central kernel reduce the alternatives to the three
marked-involution model calculations. -/
theorem remaining_alternatives (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (ha : Alternative ρ K (s + 1)) :
    MinusCase ρ K (s + 1) ∨ PlusCase ρ K (s + 1) ∨ TripleCase ρ K (s + 1) := by
  cases ha with
  | minus hm => exact Or.inl hm
  | product hp => exact (not_productCase h hp).elim
  | plus hp => exact Or.inr (Or.inl hp)
  | triple ht => exact Or.inr (Or.inr ht)
  | twistedThree ht => exact (not_twistedThreeCase h hK ht).elim

/-- None of G.9.3(7),(14)--(17) satisfies the source hypotheses of the
irreducible branch of 15.3.58. All five model exclusions are discharged. -/
theorem exclude (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (ha : Alternative ρ K (s + 1)) : False := by
  rcases remaining_alternatives h hK ha with hm | hp | ht
  · exact not_minusCase h hK hm
  · exact not_plusCase h hK hp
  · exact not_tripleCase h hK ht

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases
