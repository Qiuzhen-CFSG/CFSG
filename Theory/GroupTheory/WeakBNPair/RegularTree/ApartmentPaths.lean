module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentRelation

/-!
# Extending paths within a genuine apartment

A path in a tree can be extended inside a vertex subset whenever every vertex
of that subset has two internal neighbors. Choose a neighbor other than the
previous vertex; acyclicity prevents it from occurring earlier in the path.
Iterating preserves the entire initial segment's endpoint at its original
position. Applying this inside the translate containing an `s`-path gives the
`2(s-1)`-path needed for the finite quotient construction.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (3.5)(a) and the first paragraph of (3.6), printed pp.75--78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
universe u v
variable {X : Type u} {V : Type v} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {T : Set V}

/-- The minimum-valence property of a genuine apartment, as a vertex set in
the original graph. DGS (3.5)(a) gives exactly two neighbors. -/
def TwoNeighborsIn (Γ : SimpleGraph V) (T : Set V) : Prop :=
  ∀ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, Γ.Adj a b ∧ Γ.Adj a c ∧ b ≠ c

/-- A path in a subset of a tree with at least two internal neighbors at each
vertex extends to any larger length inside that same subset. -/
theorem path_extension_in_set (hacyclic : Γ.IsAcyclic) (hdeg : TwoNeighborsIn Γ T)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (hT : ∀ z ∈ p.support, z ∈ T) {N : ℕ} (hle : p.length ≤ N) :
    ∃ y, ∃ q : Γ.Walk a y, q.IsPath ∧ q.length = N ∧
      (∀ z ∈ q.support, z ∈ T) ∧ q.getVert p.length = b := by
  induction N, hle using Nat.le_induction with
  | base => exact ⟨b, p, hp, rfl, hT, p.getVert_length⟩
  | succ N hN ih =>
    obtain ⟨y, q, hq, hqlen, hqT, hprefix⟩ := ih
    obtain ⟨b', hb', c', hc', hyb, hyc, hbc⟩ := hdeg y (hqT y q.end_mem_support)
    have hex : ∃ z ∈ T, Γ.Adj y z ∧ z ≠ q.penultimate := by
      by_cases hb : b' = q.penultimate
      · exact ⟨c', hc', hyc, fun hc => hbc (hb.trans hc.symm)⟩
      · exact ⟨b', hb', hyb, hb⟩
    obtain ⟨z, hzT, hyz, hz⟩ := hex
    have hnew : z ∉ q.support := fun hmem =>
      hz (hacyclic.eq_penultimate_of_adj_end hq hyz hmem)
    refine ⟨z, q.concat hyz, hq.concat hnew hyz, ?_, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.length_concat, hqlen]
    · intro w hw
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hqT w hw
      · exact hzT
    · rw [SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.getVert_append',
        if_pos (hqlen ▸ hN), hprefix]

/-- The existence part of the source uniqueness condition. -/
def ApartmentsCover (Γ : SimpleGraph V) (T : Set V) (k : ℕ) : Prop :=
  ∀ {a b : V} (p : Γ.Walk a b), p.IsPath → p.length = k →
    InApartment (X := X) Γ T p

/-- Translates of the actual apartment have the same internal valence property. -/
theorem twoNeighborsIn_translate
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hdeg : TwoNeighborsIn Γ T) (g : X) :
    TwoNeighborsIn Γ {z | ∃ t ∈ T, g • t = z} := by
  rintro a ⟨t, ht, rfl⟩
  obtain ⟨b, hb, c, hc, hab, hac, hbc⟩ := hdeg t ht
  exact ⟨g • b, ⟨b, hb, rfl⟩, g • c, ⟨c, hc, rfl⟩, hact g hab,
    hact g hac, fun he => hbc ((MulAction.toPerm g).injective he)⟩

/-- A genuine apartment of valence at least two and coverage of the `s`-paths
supply the extension input used in the finite quotient proof, for `n = s-1`. -/
theorem apartmentExtension_of_cover (hacyclic : Γ.IsAcyclic)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hdeg : TwoNeighborsIn Γ T) {n : ℕ} (hn : 0 < n)
    (hcover : ApartmentsCover (X := X) Γ T (n + 1)) :
    ApartmentExtension (X := X) Γ T n := by
  intro a b p hp hlen
  obtain ⟨g, hg⟩ := hcover p hp hlen
  obtain ⟨y, q, hq, hqlen, hqT, he⟩ :=
    path_extension_in_set hacyclic (twoNeighborsIn_translate hact hdeg g) p hp hg
      (show p.length ≤ 2 * n by omega)
  exact ⟨y, q, hq, hqlen, ⟨g, hqT⟩, hlen ▸ he⟩

end Theory.GroupTheory.WeakBNPair.RegularTree
