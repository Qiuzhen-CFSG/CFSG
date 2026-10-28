module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Hyperplane orbits under a subgroup normalizer

The normalizer acts on the subgroups of `P` by its actual conjugation
homomorphism. We use the range of that action to describe each orbit,
retaining the ambient normalizer rather than replacing it by all automorphisms.
For an elementary abelian `p`-group, hyperplanes are exactly its subgroups
of index `p`.

A minimum orbit length is both a lower bound and the length of an actual
hyperplane orbit. A nontrivial finite elementary abelian group has a maximal
subgroup of index `p`, so the family is nonempty and its minimum exists.
Every orbit contains its starting subgroup, hence the minimum is positive.

This is the orbit and nontriviality setup for Aschbacher--Smith, *The
Classification of Quasithin Groups*, G.7.1(3), printed p.347. It asserts no
representation-degree inequality by itself.
-/

@[expose] public section

namespace Representation.BinaryCoprimeDegree

variable {G : Type*} [Group G]

/-- The actual conjugation orbit of a subgroup of `P` under `N_G(P)`. -/
def normalizerHyperplaneOrbit (P : Subgroup G) (H : Subgroup P) : Set (Subgroup P) :=
  Set.range fun g : Subgroup.normalizer (P : Set G) => H.map (P.normalizerMonoidHom g).toMonoidHom

theorem mem_normalizerHyperplaneOrbit (P : Subgroup G) (H : Subgroup P) :
    H ∈ normalizerHyperplaneOrbit P H := by
  refine ⟨1, ?_⟩
  simp only [map_one]
  exact H.map_id

theorem index_eq_of_mem_normalizerHyperplaneOrbit (P : Subgroup G)
    (H K : Subgroup P) (hK : K ∈ normalizerHyperplaneOrbit P H) : K.index = H.index := by
  obtain ⟨g, rfl⟩ := hK
  exact H.index_map_equiv (P.normalizerMonoidHom g)

/-- A minimum is required to be attained on a subgroup of index `p`. This does
not assign a fictitious minimum when there are no hyperplanes. -/
def IsMinimumHyperplaneOrbit (p : ℕ) (P : Subgroup G) (n : ℕ) : Prop :=
  (∃ H : Subgroup P, H.index = p ∧ Nat.card (normalizerHyperplaneOrbit P H) = n) ∧
    ∀ H : Subgroup P, H.index = p → n ≤ Nat.card (normalizerHyperplaneOrbit P H)

variable [Finite G]

theorem normalizerHyperplaneOrbit_card_pos (P : Subgroup G) (H : Subgroup P) :
    0 < Nat.card (normalizerHyperplaneOrbit P H) := by
  let : Nonempty (normalizerHyperplaneOrbit P H) :=
    ⟨⟨H, mem_normalizerHyperplaneOrbit P H⟩⟩
  exact Nat.card_pos

theorem IsMinimumHyperplaneOrbit.pos {p n : ℕ} {P : Subgroup G}
    (hn : IsMinimumHyperplaneOrbit p P n) : 0 < n := by
  obtain ⟨H, _, hH⟩ := hn.1
  rw [← hH]
  exact normalizerHyperplaneOrbit_card_pos P H

omit [Finite G] in
theorem IsMinimumHyperplaneOrbit.unique {p n m : ℕ} {P : Subgroup G}
    (hn : IsMinimumHyperplaneOrbit p P n) (hm : IsMinimumHyperplaneOrbit p P m) : n = m := by
  obtain ⟨H, hpH, hH⟩ := hn.1
  obtain ⟨K, hpK, hK⟩ := hm.1
  exact le_antisymm (hK ▸ hn.2 K hpK) (hH ▸ hm.2 H hpH)

/-- A nontrivial finite elementary abelian group has hyperplanes and hence a
well-defined attained minimum normalizer-orbit length. -/
theorem exists_minimumHyperplaneOrbit {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : P ≠ ⊥) :
    ∃ n, IsMinimumHyperplaneOrbit p P n := by
  classical
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨H, hH⟩ := IsCoatomic.exists_coatom (α := Subgroup P)
  have hidx : H.index = p := (IsElementaryAbelian.isPGroup p P).index_of_isCoatom H hH
  obtain ⟨K, hK, hmin⟩ := Set.exists_min_image
    {K : Subgroup P | K.index = p}
    (fun K => Nat.card (normalizerHyperplaneOrbit P K)) (Set.toFinite _) ⟨H, hidx⟩
  exact ⟨Nat.card (normalizerHyperplaneOrbit P K), ⟨K, hK, rfl⟩, hmin⟩

end Representation.BinaryCoprimeDegree
