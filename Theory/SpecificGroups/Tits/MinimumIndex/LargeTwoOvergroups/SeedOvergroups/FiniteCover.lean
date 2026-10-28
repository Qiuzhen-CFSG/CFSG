module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Places

/-!
# Finite subgroup covers with tree intersections

A family obtained by successively attaching a leaf has the Helly property for
common subgroup membership: pairwise common places give a single place for
the entire subgroup. At a leaf P with parent Q, choose an element outside P.
Every element in P must then also lie in Q; this removes the leaf and lets
induction apply. A product certificate turns union membership into the
required pairwise common membership.

This is the abstract part of the concrete Tits seed-overgroup argument.
`SeedOvergroups.lean` applies it to the literal conjugate parabolics in `Places`.
The intersection and product certificates themselves remain independent inputs.
Source application: the Parrott (1972), section 5, p.683 parabolic generators.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups

/-- A leaf elimination certificate for a finite family of subgroups. -/
inductive LeafIntersections {G : Type*} [Group G] : List (Subgroup G) → Prop
  | singleton (P : Subgroup G) : LeafIntersections [P]
  | cons (P Q : Subgroup G) (L : List (Subgroup G))
      (parent : Q ∈ L) (intersections : ∀ R ∈ L, P ⊓ R ≤ Q)
      (tail : LeafIntersections L) : LeafIntersections (P :: L)

private theorem helly {G : Type*} [Group G] {L : List (Subgroup G)}
    (htree : LeafIntersections L) (K : Subgroup G)
    (hpair : ∀ x ∈ K, ∀ y ∈ K, ∃ P ∈ L, x ∈ P ∧ y ∈ P) :
    ∃ P ∈ L, K ≤ P := by
  classical
  induction htree with
  | singleton P =>
      refine ⟨P, by simp, ?_⟩
      intro x hx
      obtain ⟨R, hR, hxR, _⟩ := hpair x hx x hx
      exact (List.mem_singleton.mp hR) ▸ hxR
  | cons P Q L hQ hmeet _ ih =>
      by_cases hKP : K ≤ P
      · exact ⟨P, List.mem_cons_self, hKP⟩
      obtain ⟨x, hx, hxP⟩ := SetLike.not_le_iff_exists.mp hKP
      have hparent (z : G) (hz : z ∈ K) (hzP : z ∈ P) : z ∈ Q := by
        obtain ⟨R, hR, hxR, hzR⟩ := hpair x hx z hz
        rcases List.mem_cons.mp hR with rfl | hR
        · exact (hxP hxR).elim
        · exact hmeet R hR ⟨hzP, hzR⟩
      have hp : ∀ a ∈ K, ∀ b ∈ K, ∃ R ∈ L, a ∈ R ∧ b ∈ R := by
        intro a ha b hb
        obtain ⟨R, hR, haR, hbR⟩ := hpair a ha b hb
        rcases List.mem_cons.mp hR with rfl | hR
        · exact ⟨Q, hQ, hparent a ha haR, hparent b hb hbR⟩
        · exact ⟨R, hR, haR, hbR⟩
      obtain ⟨R, hR, hKR⟩ := ih hp
      exact ⟨R, List.mem_cons_of_mem _ hR, hKR⟩

/-- Membership of x, y and their product in the union has a common place for x and y. -/
def ProductCompatible {G : Type*} [Group G] (L : List (Subgroup G)) : Prop :=
  ∀ x y : G, (∃ P ∈ L, x ∈ P) → (∃ P ∈ L, y ∈ P) →
    (∃ P ∈ L, x * y ∈ P) → ∃ P ∈ L, x ∈ P ∧ y ∈ P

/-- Local intersection and product certificates make union membership sufficient. -/
theorem le_of_union {G : Type*} [Group G] {L : List (Subgroup G)}
    (htree : LeafIntersections L) (hproduct : ProductCompatible L)
    (K : Subgroup G) (hcover : ∀ x ∈ K, ∃ P ∈ L, x ∈ P) :
    ∃ P ∈ L, K ≤ P :=
  helly htree K (fun x hx y hy => hproduct x y
    (hcover x hx) (hcover y hy) (hcover (x * y) (K.mul_mem hx hy)))

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
