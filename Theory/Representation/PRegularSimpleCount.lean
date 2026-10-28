module
public import Theory.Representation.IrreducibleTraceIndependence
public import Theory.Representation.PRegularTrace
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Bounding modular simple families by p-regular conjugacy classes

For a finite group over an algebraically closed field of prime characteristic
p, any finite family of pairwise inequivalent irreducible finite-dimensional
representations has cardinality at most the number of p-regular conjugacy
classes. The spaces may vary with the family index, and irreducibility and
equivalence are the actual representation predicates. This is the modular
counting bound needed to exhaust the concrete highest-weight candidates for
SL2 over a finite field; it assumes no classification of simple modules.

The trace characters are linearly independent by simultaneous simple-module
density. Every group element has the same trace values as a common p-regular
element in all representations, and trace is conjugacy-invariant. Thus
restriction to one representative of each p-regular conjugacy class retains
linear independence. The dimension of the function space on those classes
is their number, giving the bound. No ordinary-character orthogonality or
invertibility of the group order is used, and the class set is the existing
`ConjClasses.mk` image, not a separate conjugacy relation.
-/

open scoped BigOperators

namespace Representation

variable {F G ι : Type*} [Field F] [Group G] [Finite G] [Fintype ι]
  (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
  [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))

public theorem irreducible_family_card_le_pRegularConjClasses [IsAlgClosed F]
    [∀ i, IsIrreducible (ρ i)] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hne : Pairwise fun i j => IsEmpty (Equiv (ρ i) (ρ j))) :
    Nat.card ι ≤ Nat.card (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) := by
  classical
  have hli := linearIndependent_characters_of_pairwise_inequivalent V ρ hne
  have htrace (g : G) : ∃ h : G, ¬ p ∣ orderOf h ∧
      ∀ i, (ρ i).character g = (ρ i).character h := by
    obtain ⟨h, hh, heq⟩ := exists_pRegular_same_character (F := F) p g
    exact ⟨h, hh, fun i => heq (V i) (ρ i)⟩
  let S : Set (ConjClasses G) := ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}
  let : Fintype S := Fintype.ofFinite S
  let rep (c : S) : G := Classical.choose c.property
  have hrep (c : S) : ConjClasses.mk (rep c) = c.val :=
    (Classical.choose_spec c.property).2
  let ψ (i : ι) (c : S) : F := (ρ i).character (rep c)
  have hchar {g h : G} (hc : ConjClasses.mk g = ConjClasses.mk h) (i : ι) :
      (ρ i).character g = (ρ i).character h := by
    obtain ⟨a, ha⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hc)
    rw [← ha, (ρ i).char_conj]
  have hψ : LinearIndependent F ψ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply (Fintype.linearIndependent_iff.mp hli) c
    funext g
    obtain ⟨h, hh, hgh⟩ := htrace g
    let k : S := ⟨ConjClasses.mk h, ⟨h, hh, rfl⟩⟩
    have hk (i : ι) : (ρ i).character g = ψ i k :=
      (hgh i).trans (hchar (hrep k).symm i)
    have hx := congrFun hc k
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, hk] using hx
  have : Fintype.card ι ≤ Module.finrank F (S → F) := hψ.fintype_card_le_finrank
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using this

end Representation
