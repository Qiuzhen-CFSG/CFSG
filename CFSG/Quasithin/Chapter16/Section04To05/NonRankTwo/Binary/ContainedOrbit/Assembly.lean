module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.ContainedOrbit.Geometry

/-!
# Orbit assembly from the marked local action

An M-orbit meeting either six-element stabilizer orbit contains that whole
orbit. The Δ₀ exclusion leaves only z and these two orbits. A moving element
therefore forces size seven or thirteen, and either six-element orbit together
with z generates A. The actual stabilizer has order 72 by the orthogonal
calculation, so the previously proved faithful-action obstruction applies.

The local-action witness and the moving normalizer element are still explicit
premises. Constructing them from the source contained-A hypothesis remains
necessary before this conditional assembly proves that source branch.

Source: Aschbacher–Smith, combined manuscript, printed pp.1200–1201.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary.ContainedOrbit

open Subgroup MulAction OrthogonalFourBinary

variable {G : Type*} [Group G] {L A : Subgroup G} {z : A}

private theorem slice_subset_orbit (d : LocalAction L A z) {ε : F} {a : A}
    (ha : a ∈ orbit (normalizerImage A) z) (hs : a ∈ d.slice ε) :
    d.slice ε ⊆ orbit (normalizerImage A) z := by
  rw [← d.orbit_eq_slice hs]
  have he : orbit (normalizerImage A) a = orbit (normalizerImage A) z :=
    orbit_eq_iff.mpr ha
  exact (orbit_subgroup_subset (stabilizer (normalizerImage A) z) a).trans
    he.subset

/-- The orbit is z together with one or both of the actual six-element slices. -/
theorem LocalAction.orbit_shape (d : LocalAction L A z)
    (hcover : ∀ x ∈ orbit (normalizerImage A) z, x ≠ z →
      x ∈ d.slice 0 ∪ d.slice 1)
    (hmove : ∃ x ∈ orbit (normalizerImage A) z, x ≠ z) :
    orbit (normalizerImage A) z = insert z (d.slice 0) ∨
    orbit (normalizerImage A) z = insert z (d.slice 1) ∨
    orbit (normalizerImage A) z = insert z (d.slice 0 ∪ d.slice 1) := by
  classical
  have hbound : orbit (normalizerImage A) z ⊆ insert z (d.slice 0 ∪ d.slice 1) := by
    intro x hx
    by_cases he : x = z
    · exact Or.inl he
    · exact Or.inr (hcover x hx he)
  have hz : z ∈ orbit (normalizerImage A) z := mem_orbit_self z
  by_cases h0 : ∃ x ∈ orbit (normalizerImage A) z, x ∈ d.slice 0
  · obtain ⟨a, ha, ha0⟩ := h0
    have hs0 := slice_subset_orbit d ha ha0
    by_cases h1 : ∃ x ∈ orbit (normalizerImage A) z, x ∈ d.slice 1
    · obtain ⟨b, hb, hb1⟩ := h1
      have hs1 := slice_subset_orbit d hb hb1
      exact Or.inr (Or.inr (hbound.antisymm
        (Set.insert_subset hz (Set.union_subset hs0 hs1))))
    · left
      apply Set.Subset.antisymm _ (Set.insert_subset hz hs0)
      intro x hx
      rcases hbound hx with he | he | he
      · exact Or.inl he
      · exact Or.inr he
      · exact (h1 ⟨x, hx, he⟩).elim
  · right
    left
    obtain ⟨a, ha, haz⟩ := hmove
    have ha1 : a ∈ d.slice 1 :=
      (hcover a ha haz).resolve_left (fun hh => h0 ⟨a, ha, hh⟩)
    have hs1 := slice_subset_orbit d ha ha1
    apply Set.Subset.antisymm _ (Set.insert_subset hz hs1)
    intro x hx
    rcases hbound hx with he | he | he
    · exact Or.inl he
    · exact (h0 ⟨x, hx, he⟩).elim
    · exact Or.inr he

/-- The two six-element local orbits force the source lengths seven or thirteen. -/
theorem LocalAction.orbit_card [Finite G] (d : LocalAction L A z)
    (hcover : ∀ x ∈ orbit (normalizerImage A) z, x ≠ z →
      x ∈ d.slice 0 ∪ d.slice 1)
    (hmove : ∃ x ∈ orbit (normalizerImage A) z, x ≠ z) :
    Nat.card (orbit (normalizerImage A) z) = 7 ∨
    Nat.card (orbit (normalizerImage A) z) = 13 := by
  have hc (ε : F) : (d.slice ε).ncard = 6 := d.slice_card ε
  rcases d.orbit_shape hcover hmove with he | he | he
  · left
    rw [he, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem
      (d.central_not_mem_slice 0), hc]
  · left
    rw [he, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem
      (d.central_not_mem_slice 1), hc]
  · right
    have hz : z ∉ d.slice 0 ∪ d.slice 1 :=
      fun hh => hh.elim (d.central_not_mem_slice 0) (d.central_not_mem_slice 1)
    rw [he, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hz,
      Set.ncard_union_eq d.slices_disjoint, hc, hc]

/-- The normalizer orbit generates A, since it contains z and at least one whole slice. -/
theorem LocalAction.orbit_generates (d : LocalAction L A z)
    (hcover : ∀ x ∈ orbit (normalizerImage A) z, x ≠ z →
      x ∈ d.slice 0 ∪ d.slice 1)
    (hmove : ∃ x ∈ orbit (normalizerImage A) z, x ≠ z) :
    closure (orbit (normalizerImage A) z) = ⊤ := by
  obtain ⟨a, ha, haz⟩ := hmove
  have hgen (ε : F) (hs : a ∈ d.slice ε) :
      closure (orbit (normalizerImage A) z) = ⊤ := by
    apply top_unique
    rw [← d.slice_generates ε]
    exact closure_mono (Set.insert_subset (mem_orbit_self z) (slice_subset_orbit d ha hs))
  exact (hcover a ha haz).elim (hgen 0) (hgen 1)

/-- The source detector discharges the orbit-cover premise of the assembly. -/
theorem orbit_covered_by_slices [Finite G]
    {T : Sylow 2 G} {z₀ u g : G} {R X : Subgroup G}
    (h : EarlierInputs T z₀ L g R X u)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hz : z₀ ∈ A) (d : LocalAction L A ⟨z₀, hz⟩) :
    ∀ x ∈ orbit (normalizerImage A) (⟨z₀, hz⟩ : A), x ≠ ⟨z₀, hz⟩ →
      x ∈ d.slice 0 ∪ d.slice 1 := by
  intro x hx hxz
  obtain ⟨y, _, he⟩ := (normalizerImage_orbit_iff A ⟨z₀, hz⟩ x).mp hx
  have hx2 : orderOf (x : G) = 2 := by
    rw [← he]
    exact ((MulAut.conj y).orderOf_eq z₀).trans h.involution
  have hx1 : x ≠ 1 := by
    intro hh
    simp [hh] at hx2
  apply d.mem_slices_of_not_twoCentralProjection hx1 hxz
  rw [← he]
  exact conjugate_not_twoCentralProjection h hdis y

/-- Conditional assembly: marked local coordinates and a moving element of N_G(A)
are sufficient. Their construction from A ≤ L'K' remains required. -/
theorem contradiction_of_localAction_of_moving [Finite G]
    {T : Sylow 2 G} {z₀ u g : G} {R X : Subgroup G}
    (h : EarlierInputs T z₀ L g R X u)
    (c : ElementaryConfiguration T z₀ u g L R)
    (d : LocalAction L (elementaryGroup T L u) ⟨z₀, c.central_mem_elementary⟩)
    (hmove : ∃ m ∈ normalizer (elementaryGroup T L u : Set G),
      MulAut.conj m z₀ ≠ z₀) : False := by
  let B := elementaryGroup T L u
  let zB : B := ⟨z₀, c.central_mem_elementary⟩
  have hcover := orbit_covered_by_slices h c.centerless c.central_mem_elementary d
  have hmoves : ∃ x ∈ orbit (normalizerImage B) zB, x ≠ zB := by
    obtain ⟨m, hm, hne⟩ := hmove
    let x : B := ⟨MulAut.conj m z₀,
      (mem_normalizer_iff.mp hm z₀).mp c.central_mem_elementary⟩
    refine ⟨x, (normalizerImage_orbit_iff B zB x).mpr ⟨m, hm, rfl⟩, ?_⟩
    exact fun he => hne (congrArg Subtype.val he)
  let : IsElementaryAbelian 2 B := c.elementary
  exact normalizer_orbit_obstruction B c.elementary_card zB
    (d.orbit_generates hcover hmoves) (d.orbit_card hcover hmoves) d.stabilizer_card

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary.ContainedOrbit
