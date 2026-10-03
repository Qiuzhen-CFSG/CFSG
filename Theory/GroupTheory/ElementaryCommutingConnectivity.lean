module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Logic.Relation

/-!
# Connectivity by commuting elementary subgroups

The vertices are actual elementary abelian `p`-subgroups with cardinality
at least `p ^ 2`. Two vertices are adjacent when they commute elementwise.
Connectivity is the reflexive transitive closure of adjacency, together
with validity of the starting vertex. The latter condition also keeps
zero-length paths at valid vertices; every endpoint is therefore valid.

This is the rank-two commuting graph of Gorenstein–Lyons–Solomon, volume 2,
Definition 10.18 (`refs/KGroup/GLS2/ChapterC.tex`). At prime `p` in a finite
ambient group the vertex condition is the source's elementary rank at
least two. The definitions and transport theorem only need the literal
cardinality condition, so no primality or ambient finiteness is assumed.
Allowing the commuting self-edge does not change connectivity.

Symmetry follows from symmetry of elementwise commutation. An ambient
group isomorphism preserves the elementary property, cardinalities and
commutation, and hence maps each step of a chain. Its inverse reflects
connectivity. This supplies the actual subgroup relation for component
normalizer arguments, without assuming that the whole graph is connected.
-/

namespace Subgroup

@[expose] public def ElementaryCommutingAdjacent (p : ℕ)
    {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  IsElementaryAbelian p A ∧ p ^ 2 ≤ Nat.card A ∧
    IsElementaryAbelian p B ∧ p ^ 2 ≤ Nat.card B ∧
    A ≤ centralizer (B : Set G)

@[expose] public def ElementaryCommutingConnected (p : ℕ)
    {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  IsElementaryAbelian p A ∧ p ^ 2 ≤ Nat.card A ∧
    Relation.ReflTransGen (ElementaryCommutingAdjacent p) A B

variable {p : ℕ} {G H : Type*} [Group G] [Group H]
variable {A B C : Subgroup G}

public theorem ElementaryCommutingAdjacent.symm
    (h : ElementaryCommutingAdjacent p A B) : ElementaryCommutingAdjacent p B A :=
  ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, le_centralizer_iff.mp h.2.2.2.2⟩

public theorem ElementaryCommutingConnected.left
    (h : ElementaryCommutingConnected p A B) :
    IsElementaryAbelian p A ∧ p ^ 2 ≤ Nat.card A :=
  ⟨h.1, h.2.1⟩

public theorem ElementaryCommutingConnected.right
    (h : ElementaryCommutingConnected p A B) :
    IsElementaryAbelian p B ∧ p ^ 2 ≤ Nat.card B := by
  obtain ⟨hA, hcard, hpath⟩ := h
  induction hpath with
  | refl => exact ⟨hA, hcard⟩
  | tail _ hstep _ => exact ⟨hstep.2.2.1, hstep.2.2.2.1⟩

public theorem ElementaryCommutingConnected.refl
    (hA : IsElementaryAbelian p A) (hcard : p ^ 2 ≤ Nat.card A) :
    ElementaryCommutingConnected p A A :=
  ⟨hA, hcard, .refl⟩

public theorem ElementaryCommutingAdjacent.connected
    (h : ElementaryCommutingAdjacent p A B) : ElementaryCommutingConnected p A B :=
  ⟨h.1, h.2.1, .single h⟩

public theorem ElementaryCommutingConnected.trans
    (hAB : ElementaryCommutingConnected p A B)
    (hBC : ElementaryCommutingConnected p B C) : ElementaryCommutingConnected p A C :=
  ⟨hAB.1, hAB.2.1, hAB.2.2.trans hBC.2.2⟩

public theorem ElementaryCommutingConnected.symm
    (h : ElementaryCommutingConnected p A B) : ElementaryCommutingConnected p B A := by
  refine ⟨h.right.1, h.right.2, ?_⟩
  have hpath := h.2.2
  clear h
  induction hpath with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.head hstep.symm

private theorem elementary_map_equiv (e : G ≃* H)
    (hA : IsElementaryAbelian p A) : IsElementaryAbelian p (A.map e.toMonoidHom) := by
  let _ := hA
  refine {
    toIsMulCommutative := Subgroup.map_isMulCommutative A e.toMonoidHom
    exponent_dvd_p := ?_
  }
  rw [← Monoid.exponent_eq_of_mulEquiv (A.equivMapOfInjective e.toMonoidHom e.injective)]
  exact IsElementaryAbelian.exponent_dvd_p p A

public theorem ElementaryCommutingAdjacent.map
    (h : ElementaryCommutingAdjacent p A B) (e : G ≃* H) :
    ElementaryCommutingAdjacent p (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  refine ⟨elementary_map_equiv e h.1, ?_, elementary_map_equiv e h.2.2.1, ?_, ?_⟩
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using h.2.1
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      using h.2.2.2.1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.2.2.2.2 ha b hb]

public theorem ElementaryCommutingConnected.map
    (h : ElementaryCommutingConnected p A B) (e : G ≃* H) :
    ElementaryCommutingConnected p (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  refine ⟨elementary_map_equiv e h.1, ?_, ?_⟩
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using h.2.1
  · exact h.2.2.lift (fun K => K.map e.toMonoidHom) (fun _ _ hstep => hstep.map e)

/-- An injective homomorphism transports commuting edges, including their
elementary and cardinality conditions. -/
public theorem ElementaryCommutingAdjacent.map_injective
    (h : ElementaryCommutingAdjacent p A B) (f : G →* H) (hf : Function.Injective f) :
    ElementaryCommutingAdjacent p (A.map f) (B.map f) := by
  have helem (K : Subgroup G) (hK : IsElementaryAbelian p K) :
      IsElementaryAbelian p (K.map f) := by
    let _ := hK
    refine {
      toIsMulCommutative := Subgroup.map_isMulCommutative K f
      exponent_dvd_p := ?_
    }
    rw [← Monoid.exponent_eq_of_mulEquiv (K.equivMapOfInjective f hf)]
    exact IsElementaryAbelian.exponent_dvd_p p K
  refine ⟨helem A h.1, ?_, helem B h.2.2.1, ?_, ?_⟩
  · simpa only [card_map_of_injective hf] using h.2.1
  · simpa only [card_map_of_injective hf] using h.2.2.2.1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.2.2.2.2 ha b hb]

/-- In particular, a commuting path in a subgroup is a commuting path in
the ambient group, after mapping each vertex by the subtype homomorphism. -/
public theorem ElementaryCommutingConnected.map_injective
    (h : ElementaryCommutingConnected p A B) (f : G →* H) (hf : Function.Injective f) :
    ElementaryCommutingConnected p (A.map f) (B.map f) := by
  have hAA : ElementaryCommutingAdjacent p A A := by
    let _ := h.1
    refine ⟨h.1, h.2.1, h.1, h.2.1, ?_⟩
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hm := hAA.map_injective f hf
  exact ⟨hm.1, hm.2.1,
    h.2.2.lift (fun K => K.map f) (fun _ _ hstep => hstep.map_injective f hf)⟩

/-- An actual ambient group isomorphism preserves and reflects elementary
rank-two commuting connectivity. -/
public theorem elementaryCommutingConnected_map_iff (p : ℕ) (e : G ≃* H)
    (A B : Subgroup G) :
    ElementaryCommutingConnected p (A.map e.toMonoidHom) (B.map e.toMonoidHom) ↔
      ElementaryCommutingConnected p A B := by
  constructor
  · intro h
    have hmap (K : Subgroup G) :
        (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
      have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
        apply MonoidHom.ext
        intro x
        exact e.symm_apply_apply x
      rw [Subgroup.map_map, hid, Subgroup.map_id]
    simpa only [hmap] using h.map e.symm
  · exact fun h => h.map e

end Subgroup
