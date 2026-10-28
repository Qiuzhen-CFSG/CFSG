module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction.Binary
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationChain
/-!
# The AS91 ternary relation-chain reduction

Hypothesis B retains the chosen common-neighbor components in Dₖ and both
distance-two restrictions in B3. Passing to binary relations explicitly adds
equality and adjacency, as required by Hypothesis A's level-zero convention.
B2 first connects common neighbors of level-one pairs. Induction on the
ternary level then contracts all squares; B3 supplies the common neighbor
needed for the source's pentagon decomposition. The binary-chain theorem
finally contracts every closed walk in nonabelian triangle closure.

These are conditional graph theorems, not fields of `SourceCycleBase.Input`.
Their ambient section 7 verification remains a separate mathematical step.

Source: Aschbacher–Segev (1991), Hypothesis B, (1.3)–(1.4), pp.591–592.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction
open SimpleGraph SimpleGraph.WalkClosure
variable {V : Type*} {Γ : SimpleGraph V}

/-- Reflexive adjacency is retained when passing from ternary to binary
relations. In particular, isolated vertices cause no exception at level zero. -/
def induced (T : ℕ → V → V → V → Prop) (i : ℕ) (x y : V) : Prop :=
  Near Γ x y ∨ ∃ u, T i x u y

def extension (T : ℕ → V → V → V → Prop) (i : ℕ) (x u y : V) : Set V :=
  commonComponent Γ x u y ∪
    {w | Γ.Adj x w ∧ ∃ c ∈ commonComponent Γ x u y, T i y c w}

structure HypothesisB (Γ : SimpleGraph V) (N : ℕ) where
  ternary : ℕ → V → V → V → Prop
  symm : ∀ i x u y, ternary i x u y → ternary i y u x
  mono : ∀ i j, i ≤ j → ∀ x u y, ternary i x u y → ternary j x u y
  zero : ∀ x u y, ternary 0 x u y ↔ Γ.Adj x u ∧ Γ.Adj u y ∧ Γ.Adj x y
  bounded : ∀ i x u y, ternary i x u y → Γ.Adj x u ∧ Γ.Adj u y
  full : ∀ x u y, Γ.Adj x u → Γ.Adj u y → ternary N x u y
  /-- B2, stated with the actual component witnesses and distance at most one. -/
  bridge : ∀ k, k < N → ∀ x u y v z,
    ternary (k + 1) x u y → ¬ Near Γ x y →
    Γ.Adj x v → Γ.Adj v z → ¬ Near Γ x z →
    ∃ w q, w ∈ extension (Γ := Γ) ternary k x u y ∧
      q ∈ commonComponent Γ x v z ∧ induced (Γ := Γ) ternary (min k 1) w q
  /-- B3, with both distance-two restrictions, as in the source. -/
  triple : ∀ x y w, induced (Γ := Γ) ternary 1 x y → ProperTwo Γ x y →
    Γ.Adj y w → ProperTwo Γ x w →
    ∃ c, Γ.Adj x c ∧ Γ.Adj y c ∧ Near Γ c w

namespace HypothesisB
variable {N : ℕ} (B : HypothesisB Γ N)

abbrev rel := induced (Γ := Γ) B.ternary
abbrev ext := extension (Γ := Γ) B.ternary

theorem rel_zero (x y : V) : B.rel 0 x y ↔ Near Γ x y := by
  constructor
  · rintro (h | ⟨u, hu⟩)
    · exact h
    · exact Or.inr ((B.zero x u y).mp hu).2.2
  · exact Or.inl

theorem extension_zero (x u y : V) : B.ext 0 x u y = commonComponent Γ x u y := by
  apply Set.ext
  intro w
  constructor
  · rintro (hw | ⟨hxw, c, hc, ht⟩)
    · exact hw
    · have ht' := (B.zero y c w).mp ht
      exact commonComponent_step Γ hc ⟨hxw, ht'.2.2⟩ ht'.2.1
  · exact Or.inl

/-- AS91 (1.3), including the reflexive-neighborhood convention. -/
def toA : HypothesisA Γ N where
  rel := B.rel
  symm := by
    intro i x y h
    rcases h with (he | ha) | ⟨u, hu⟩
    · exact Or.inl (Or.inl he.symm)
    · exact Or.inl (Or.inr ha.symm)
    · exact Or.inr ⟨u, B.symm i x u y hu⟩
  mono := by
    intro i j hij x y h
    rcases h with h | ⟨u, hu⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, B.mono i j hij x u y hu⟩
  zero := B.rel_zero
  bounded := by
    intro i x y h
    rcases h with h | ⟨u, hu⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, B.bounded i x u y hu⟩
  full := by
    intro x y h
    rcases h with h | ⟨u, hxu, huy⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, B.full x u y hxu huy⟩
  reduce := by
    intro k hk x y z hxy hxy' hxz
    obtain hnear | ⟨u, hu⟩ := hxy
    · exact (hxy'.1 hnear).elim
    obtain ⟨v, hxv, hvz⟩ := hxz.2
    obtain ⟨w, q, hw, hq, hwq⟩ := B.bridge k hk x u y v z hu hxy'.1 hxv hvz hxz.1
    have hq' := commonComponent_subset Γ x v z hq
    refine ⟨w, q, ?_, ?_, hq'.1, hq'.2, hwq⟩
    · rcases hw with hw | hw
      · exact (commonComponent_subset Γ x u y hw).1
      · exact hw.1
    · rcases hw with hw | ⟨_, c, hc, ht⟩
      · exact Or.inl (Or.inr (commonComponent_subset Γ x u y hw).2)
      · exact Or.inr ⟨c, ht⟩

end HypothesisB

/-- Join two components through an edge (or their intersection). -/
theorem commonComponent_join {x u y v w q : V}
    (hw : w ∈ commonComponent Γ x u y) (hq : q ∈ commonComponent Γ x v y)
    (h : Near Γ w q) : v ∈ commonComponent Γ x u y := by
  obtain ⟨hu, hw', hw⟩ := hw
  obtain ⟨hv, hq', hq⟩ := hq
  have hwq : (Γ.commonNeighborGraph x y).Reachable ⟨w, hw'⟩ ⟨q, hq'⟩ := by
    rcases h with rfl | h
    · exact .refl _
    · exact ⟨(show (Γ.commonNeighborGraph x y).Adj ⟨w, hw'⟩ ⟨q, hq'⟩ from h).toWalk⟩
  exact ⟨hu, hv, (hw.trans hwq).trans hq.symm⟩

theorem commonComponent_reverse {x u y v : V} (hv : v ∈ commonComponent Γ x u y) :
    u ∈ commonComponent Γ x v y := by
  obtain ⟨hu, hv, hp⟩ := hv
  exact ⟨hv, hu, hp.symm⟩

theorem commonComponent_trans {x u y v w : V}
    (hv : v ∈ commonComponent Γ x u y) (hw : w ∈ commonComponent Γ x v y) :
    w ∈ commonComponent Γ x u y := by
  obtain ⟨hu, hv, hp⟩ := hv
  obtain ⟨_, hw, hq⟩ := hw
  exact ⟨hu, hw, hp.trans hq⟩

namespace HypothesisB
variable {N : ℕ} (B : HypothesisB Γ N)

/-- The first paragraph of (1.4): only level-one distance-two pairs have
connected common-neighbor graphs at this point of the argument. -/
theorem common_component_one (hN : 0 < N) {x y u v : V}
    (hxy : B.rel 1 x y) (hn : ¬ Near Γ x y)
    (hxu : Γ.Adj x u) (huy : Γ.Adj u y) (hxv : Γ.Adj x v) (hvy : Γ.Adj v y) :
    v ∈ commonComponent Γ x u y := by
  obtain hnear | ⟨c, hc⟩ := hxy
  · exact (hn hnear).elim
  have connect (w : V) (hxw : Γ.Adj x w) (hwy : Γ.Adj w y) :
      w ∈ commonComponent Γ x c y := by
    obtain ⟨a, b, ha, hb, hab⟩ := B.bridge 0 hN x c y w y hc hn hxw hwy hn
    change a ∈ B.ext 0 x c y at ha
    rw [B.extension_zero] at ha
    exact commonComponent_join ha hb ((B.rel_zero a b).mp hab)
  exact commonComponent_trans (commonComponent_reverse (connect u hxu huy)) (connect v hxv hvy)

/-- Shorten a square with a degenerate diagonal. -/
theorem two_step_near {x y u v : V} (hxy : Near Γ x y)
    (hxu : Γ.Adj x u) (huy : Γ.Adj u y) (hxv : Γ.Adj x v) (hvy : Γ.Adj v y) :
    Rel (triangles Γ) (.cons hxu huy.toWalk) (.cons hxv hvy.toWalk) := by
  rcases hxy with rfl | hxy
  · exact (spur hxu .nil).trans (spur hxv .nil).symm
  · exact (triangle_replace hxu huy hxy).trans (triangle_replace hxv hvy hxy).symm

/-- Level-one binary pairs contract squares, including degenerate cases. -/
theorem two_step_one (hN : 0 < N) {x y u v : V} (hxy : B.rel 1 x y)
    (hxu : Γ.Adj x u) (huy : Γ.Adj u y) (hxv : Γ.Adj x v) (hvy : Γ.Adj v y) :
    Rel (triangles Γ) (.cons hxu huy.toWalk) (.cons hxv hvy.toWalk) := by
  classical
  by_cases hn : Near Γ x y
  · exact two_step_near hn hxu huy hxv hvy
  · exact two_step_related_of_commonComponent Γ hxu huy hxv hvy
      (B.common_component_one hN hxy hn hxu huy hxv hvy)

end HypothesisB

/-- Rotate a square relation while retaining all four literal vertices. -/
theorem rotate_square {S : Cycles Γ} {a b c d : V}
    (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (had : Γ.Adj a d) (hdc : Γ.Adj d c)
    (h : Rel S (.cons hab hbc.toWalk) (.cons had hdc.toWalk)) :
    Rel S (.cons hbc hdc.symm.toWalk) (.cons hab.symm had.toWalk) := by
  have h' := Rel.append (rel_cons hab.symm h) (.refl hdc.symm.toWalk)
  have hleft := spur (S := S) hab.symm (Walk.cons hbc hdc.symm.toWalk)
  have hright := rel_cons (S := S) hab.symm (rel_cons had (spur hdc .nil))
  exact hleft.symm.trans (h'.trans hright)

namespace HypothesisB
variable {N : ℕ} (B : HypothesisB Γ N)

/-- A level-one diagonal also contracts the square after exchanging its
opposite vertex pairs. -/
theorem two_step_opposite (hN : 0 < N) {a b c d : V} (hbd : B.rel 1 b d)
    (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (had : Γ.Adj a d) (hdc : Γ.Adj d c) :
    Rel (triangles Γ) (.cons hab hbc.toWalk) (.cons had hdc.toWalk) :=
  (rotate_square hab.symm had hbc hdc.symm
    (B.two_step_one hN hbd hab.symm had hbc hdc.symm)).symm

/-- The minimal-type square argument of AS91 (1.4). The induction keeps
both common-neighbor components, and B3 is used only with its two genuine
distance-two hypotheses. -/
theorem two_step_of_ternary (k : ℕ) (hk : k ≤ N) {a b c d : V}
    (ht : B.ternary k a b c) (had : Γ.Adj a d) (hdc : Γ.Adj d c) :
    Rel (triangles Γ)
      (.cons (B.bounded k a b c ht).1 (B.bounded k a b c ht).2.toWalk)
      (.cons had hdc.toWalk) := by
  classical
  have hab := (B.bounded k a b c ht).1
  have hbc := (B.bounded k a b c ht).2
  induction k generalizing a b c d with
  | zero =>
    exact two_step_near (Or.inr ((B.zero a b c).mp ht).2.2) hab hbc had hdc
  | succ k ih =>
    have hN : 0 < N := by omega
    by_cases hn : Near Γ a c
    · exact two_step_near hn hab hbc had hdc
    by_cases hk0 : k = 0
    · subst k
      exact B.two_step_one hN (Or.inr ⟨b, ht⟩) hab hbc had hdc
    obtain ⟨w, q, hw, hq, hwq⟩ := B.bridge k (by omega) a b c d c ht hn had hdc hn
    have hwq' : B.rel 1 w q := B.toA.mono _ _ (min_le_right _ _) w q hwq
    have haq := (commonComponent_subset Γ a d c hq).1
    have hqc := (commonComponent_subset Γ a d c hq).2.symm
    have right := two_step_related_of_commonComponent Γ had hdc haq hqc hq
    apply Rel.trans (q := .cons haq hqc.toWalk) ?_ right.symm
    rcases hw with hw | ⟨haw, b', hb', hcbw⟩
    · have haw := (commonComponent_subset Γ a b c hw).1
      have hwc := (commonComponent_subset Γ a b c hw).2.symm
      exact (two_step_related_of_commonComponent Γ hab hbc haw hwc hw).trans
        (B.two_step_opposite hN hwq' haw hwc haq hqc)
    · have hab' := (commonComponent_subset Γ a b c hb').1
      have hb'c := (commonComponent_subset Γ a b c hb').2.symm
      have hb'w := (B.bounded k c b' w hcbw).2
      have left := two_step_related_of_commonComponent Γ hab hbc hab' hb'c hb'
      apply left.trans
      have insert : Rel (triangles Γ) (.cons hab' hb'c.toWalk)
          (.cons haw (.cons hb'w.symm hb'c.toWalk)) :=
        Rel.append (triangle_replace haw hb'w.symm hab').symm (.refl hb'c.toWalk)
      by_cases hwc : Near Γ w c
      · obtain he | hwc := hwc
        · exact (hn (Or.inr (he ▸ haw))).elim
        · exact insert.trans ((rel_cons haw (triangle_replace hb'w.symm hb'c hwc)).trans
            (B.two_step_opposite hN hwq' haw hwc haq hqc))
      have htw := B.symm k c b' w hcbw
      by_cases hwq : Near Γ w q
      · obtain he | hwq := hwq
        · exact (hwc (Or.inr (he ▸ hqc))).elim
        · have low := ih (by omega) htw hwq hqc hb'w.symm hb'c
          exact insert.trans ((rel_cons haw low).trans
            (Rel.append (triangle_replace haw hwq haq) (.refl hqc.toWalk)))
      obtain ⟨x, hwx, hqx, hxc⟩ := B.triple w q c hwq'
        ⟨hwq, a, haw.symm, haq⟩ hqc ⟨hwc, b', hb'w.symm, hb'c⟩
      have hxc' : Γ.Adj x c := by
        obtain he | hxc := hxc
        · exact (hwc (Or.inr (he ▸ hwx))).elim
        · exact hxc
      have low := ih (by omega) htw hwx hxc' hb'w.symm hb'c
      have opposite := B.two_step_opposite hN hwq' haw hwx haq hqx
      exact insert.trans ((rel_cons haw low).trans
        ((Rel.append opposite (.refl hxc'.toWalk)).trans
          (rel_cons haq (triangle_replace hqx hxc' hqc))))

/-- AS91 (1.4), in the actual nonabelian triangle closure. -/
theorem triangulable (B : HypothesisB Γ N) : Triangulable Γ := by
  intro a p
  apply (B.toA.four_generated a p).of_generators
  intro x q hq
  change q.length ≤ 4 at hq
  cases q with
  | nil => exact .refl _
  | @cons x a x hxa q =>
    cases q with
    | nil => exact (hxa.ne rfl).elim
    | @cons a b x hab q =>
      cases q with
      | nil => exact spur hxa .nil
      | @cons b c x hbc q =>
        cases q with
        | nil => exact .cycle _ rfl
        | @cons c d x hcd q =>
          have hz : q.length = 0 := by simp only [Walk.length_cons] at hq; omega
          cases q with
          | nil =>
            have he := B.two_step_of_ternary N le_rfl (B.full x a b hxa hab) hcd.symm hbc.symm
            have he' := Rel.append he (.refl (Walk.cons hbc hcd.toWalk))
            exact he'.trans ((rel_cons hcd.symm (spur hbc.symm _)).trans (spur hcd.symm .nil))
          | cons _ _ => simp at hz

end HypothesisB
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction
