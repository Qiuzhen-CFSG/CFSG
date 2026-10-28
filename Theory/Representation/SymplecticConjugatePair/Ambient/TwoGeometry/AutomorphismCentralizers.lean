module

public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.Binary
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.NonbinaryNormalForms

/-!
# Sharp two-ranks of outer involution centralizers in Aut(Sp₄(F))

For |F| = 2ⁿ, a diagram-moving involution has centralizer two-rank at most
n+1, including n=1. A noninner diagram-preserving involution requires even n
and has centralizer two-rank at most 3(n/2)+1. The kernel of the centralizer's
map to the cyclic outer quotient is its actual inner intersection and embeds
in the involution's fixed subgroup. The latter is the full symplectic group
over the half-size field, or the full Suzuki fixed group, respectively.

Semilinear coverage and the Suzuki matrix identification are proved inputs.
For n>1 the only remaining premises are the displayed field and graph
cocycle descents. The binary bound is unconditional. Discharging the two
nonbinary descents and transferring through the scalar kernel remain with
the source and ambient assembly owners.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, H.7,
printed p.389, and 16.1.4, printed pp.1170–1173 of `refs/quasithin.pdf`.
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
namespace SymplecticConjugatePair.Ambient.AutomorphismCentralizers

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The sharp graph centralizer bound in every positive field degree. The
cocycle premise is required only in the nonbinary case; at n=1 the separate
unconditional binary theorem applies. -/
theorem moving_centralizer_rank_le_of_descent {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n)
    (hgraph : 1 < n → Odd n → ∀ g : Sp F,
      g * (ExceptionalGraph.graphAut ^ n) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ n) h)⁻¹)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : ¬ PreservesDiagram a) :
    primeRank 2 (centralizer ({a} : Set (MulAut (Sp F)))) ≤ n + 1 := by
  by_cases hbinary : n = 1
  · subst n
    exact binary_moving_centralizer_rank_le (by simpa only [pow_one] using hF) a hao ha
  · have hn' : 2 ≤ n := by omega
    let := ExceptionalGraph.outer_isCyclic_of_card hF (by omega)
      SemilinearClassification.inner_field_of_preservesDiagram
    obtain ⟨hodd, hc⟩ := moving_normal_form hF hn' (hgraph (by omega)) a hao ha
    have hfixed : primeRank 2 a.fixedSubgroup ≤ n := by
      rw [fixed_rank_eq_of_isConj hc]
      exact graph_fixed_rank_le hF hodd
    exact (centralizer_rank_le_fixed_add_one inner_injective a).trans
      (Nat.add_le_add_right hfixed 1)

/-- A noninner diagram-preserving involution forces even degree and has the
sharp field centralizer bound. Only the even-degree field cocycle descent
remains explicit. -/
theorem preserving_outer_centralizer_rank_le_of_descent {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : PreservesDiagram a)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    Even n ∧ primeRank 2 (centralizer ({a} : Set (MulAut (Sp F)))) ≤ 3 * (n / 2) + 1 := by
  let := ExceptionalGraph.outer_isCyclic_of_card hF (by omega)
    SemilinearClassification.inner_field_of_preservesDiagram
  obtain ⟨heven, hc⟩ := preserving_outer_normal_form hF hn hfield a hao ha hi
  refine ⟨heven, ?_⟩
  have hfixed : primeRank 2 a.fixedSubgroup = 3 * (n / 2) := by
    rw [fixed_rank_eq_of_isConj hc]
    exact field_fixed_rank hF hn heven
  exact hfixed ▸ centralizer_rank_le_fixed_add_one inner_injective a

end SymplecticConjugatePair.Ambient.AutomorphismCentralizers
