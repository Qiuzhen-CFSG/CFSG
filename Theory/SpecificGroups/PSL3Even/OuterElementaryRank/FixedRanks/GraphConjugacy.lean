module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.ModelBounds
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy.Gram
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# Graph involutions of PSL₃ over finite fields of characteristic two

The square-one equation for the actual projective graph actor forces its
conjugating matrix to be symmetric. The ternary Gram factorization writes
this matrix as hᵀh. Conjugation by the linear actor of h⁻ᵀ then gives the
standard inverse-transpose automorphism on the literal quotient SL₃/Z(SL₃).
Transporting its whole fixed subgroup gives the bound by the binary field
degree. This includes the field with two elements.

This discharges the graph-conjugacy premise of
`FixedRanks.fixed_estimates_of_model_identifications`; the field and
mixed graph-field branches remain with their respective owners.
Source: GLS3, Theorem 2.5.12 and §2.7; Aschbacher–Smith E.1.14(1),
printed p.214, and the graph type in 16.1.4(6), printed p.1171.
The fixed subgroup here is the whole fixed group, not its two-residual.
-/

public section
open scoped MatrixGroups
open Theory.GroupTheory
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F]

/-- A Gram factor gives the explicit conjugator on the actual projective group. -/
theorem graph_congr_of_gram (g h : GL (Fin 3) F)
    (hh : g.val = h.val.transpose * h.val) :
    MulAut.congr (linearConj F (inverseTransposeGL F h))
      (linearConj F g * graph F) = graph F := by
  let n := inverseTransposeGL F h
  have hfactor : g = n⁻¹ * h := Units.ext hh
  have hn : inverseTransposeGL F n = h := Units.ext rfl
  have hnorm : n * g * inverseTransposeGL F n⁻¹ = 1 := by
    rw [hfactor, map_inv, hn]
    group
  change linearConj F n * (linearConj F g * graph F) * (linearConj F n)⁻¹ = graph F
  rw [← map_inv, mul_assoc, mul_assoc, graph_linearConj, ← mul_assoc,
    ← map_mul, ← mul_assoc, ← map_mul, hnorm, map_one, one_mul]

/-- The conjugacy intertwines the actors on every element of PSL₃ itself. -/
theorem graph_gram_intertwines (g h : GL (Fin 3) F)
    (hh : g.val = h.val.transpose * h.val) (x : PSL(3,F)) :
    linearConj F (inverseTransposeGL F h) ((linearConj F g * graph F) x) =
      graph F (linearConj F (inverseTransposeGL F h) x) := by
  have hc := graph_congr_of_gram g h hh
  have he := DFunLike.congr_fun hc (linearConj F (inverseTransposeGL F h) x)
  simpa using he

/-- Every involution in the linear–graph coset has an actual linear conjugator. -/
theorem graph_involution_linear_conjugate [Finite F] [CharP F 2]
    (g : GL (Fin 3) F) (hg : (linearConj F g * graph F) ^ 2 = 1) :
    ∃ n : GL (Fin 3) F,
      MulAut.congr (linearConj F n) (linearConj F g * graph F) = graph F := by
  obtain ⟨h, hh⟩ := GraphConjugacy.symmetric_gram g
    (Matrix.PSL3.OddInvolutionFixed.graph_involution_symmetric g hg)
  exact ⟨inverseTransposeGL F h, graph_congr_of_gram g h hh⟩

/-- The exact graph-model premise consumed by the outer fixed-rank assembly. -/
theorem graph_involution_conjugate [Finite F] {f : ℕ}
    (_hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (g : GL (Fin 3) F) (hg : (linearConj F g * graph F) ^ 2 = 1) :
    ∃ c : MulAut PSL(3,F), MulAut.congr c (linearConj F g * graph F) = graph F := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨n, hn⟩ := graph_involution_linear_conjugate g hg
  exact ⟨linearConj F n, hn⟩

/-- The whole fixed group of a graph involution has two-rank at most f. -/
theorem graph_involution_fixed_rank [Finite F] {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (g : GL (Fin 3) F) (hg : (linearConj F g * graph F) ^ 2 = 1) :
    primeRank 2 (linearConj F g * graph F).fixedSubgroup ≤ f := by
  obtain ⟨c, hc⟩ := graph_involution_conjugate hf hF g hg
  exact graph_fixed_rank_of_congr hF _ c hc

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks
