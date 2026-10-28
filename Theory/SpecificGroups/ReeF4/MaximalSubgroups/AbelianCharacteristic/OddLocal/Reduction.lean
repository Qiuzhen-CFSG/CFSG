module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Separating the odd-local Ree geometry from the normalizer argument

There are two geometric obligations. `CyclicReduction` says that a nontrivial
elementary abelian odd characteristic subgroup of a nonsolvable maximal
subgroup has order three. `ThreeCentralizers` identifies the actual centralizer
of an order-three subgroup with SU₃ over the quadratic field, proves its
normalizer proper, and supplies nontrivial action of that normalizer.
These are unproved inputs, not source theorems.

The remaining finite-group argument is independent of Ree geometry. Relative
normality places a maximal subgroup inside the ambient normalizer, so a proper
normalizer equals it. Conjugation embeds the normalizer modulo centralizer in
Aut(C₃), which has order two. Nontrivial action therefore gives index two,
without choosing a complement or quotienting the SU₃ center.

Sources: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E; the list in the proof of Theorem 5,
arXiv:0910.4758, pp.2–3. For the order-three centralizer and its universal
version, see GLS3, Table 4.7.3A, printed p.227
(`refs/KGroup/GLS3/chapter4.tex`), and the A₂ × A₂ subsystem construction in
Example 2.6.3 (`refs/KGroup/GLS3/chapter2.tex`). GLS3's half-integer Ree
parameter has square equal to our field size `2^(2*m+1)`.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal

open Subgroup BenderSuzuki.MatrixGroups

/-- The remaining semisimple normalizer reduction. Maximality and relative
characteristicity are retained: nonsolvability of an arbitrary odd-subgroup
normalizer alone is not the asserted hypothesis. -/
def CyclicReduction : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup M,
      E.Characteristic → IsElementaryAbelian p E → E ≠ ⊥ → Nat.card E = 3

/-- The remaining intrinsic order-three calculation. The carrier equivalence
describes the full centralizer as SU₃, retaining its central kernel. The
normalizer is proper and acts nontrivially on the order-three subgroup; its
index over the centralizer will then follow from the generic argument below. -/
def ThreeCentralizers : Prop :=
  ∀ m, 1 ≤ m → ∀ A : Subgroup (Model m), Nat.card A = 3 →
    normalizer (A : Set (Model m)) ≠ ⊤ ∧
    centralizer (A : Set (Model m)) ≠ normalizer (A : Set (Model m)) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
      Nat.card F = (2 ^ (2 * m + 1)) ^ 2 ∧
      (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) ∧
      Nonempty (centralizer (A : Set (Model m)) ≃* J.specialSubgroup)

/-- A proper ambient normalizer of a subgroup normal in a maximal subgroup
equals that maximal subgroup. No ambient normality or simplicity is used. -/
theorem normalizer_eq_of_isCoatom {G : Type*} [Group G]
    (M : Subgroup G) (hM : IsCoatom M) (E : Subgroup M) [E.Normal]
    (hN : normalizer (E.map M.subtype : Set G) ≠ ⊤) :
    normalizer (E.map M.subtype : Set G) = M := by
  have hMN : M ≤ normalizer (E.map M.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using E.le_normalizer_map M.subtype
  exact le_antisymm ((isCoatom_iff_ge_of_le.mp hM).2 _ hN hMN) hMN

/-- Nontrivial normalizer action on a group of order three has centralizer
index exactly two. This does not assert that the extension splits. -/
theorem centralizer_index_of_card_three {G : Type*} [Group G]
    (A : Subgroup G) [Finite A] (hA : Nat.card A = 3)
    (hC : centralizer (A : Set G) ≠ normalizer (A : Set G)) :
    ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).index = 2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hdiv := card_dvd_of_injective _
    (QuotientGroup.kerLift_injective A.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut,
    hA, Nat.totient_prime (by decide : Nat.Prime 3)] at hdiv
  have hne : ((centralizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))).index ≠ 1 := by
    intro h
    exact hC (le_antisymm (centralizer_le_normalizer _)
      (subgroupOf_eq_top.mp (index_eq_one.mp h)))
  exact ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv).resolve_left hne

end ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal
