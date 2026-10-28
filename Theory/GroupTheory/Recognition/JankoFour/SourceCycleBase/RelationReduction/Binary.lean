module
public import Theory.Combinatorics.WalkClosure.RankContraction
/-!
# The AS91 binary relation-chain reduction

Hypothesis A uses the reflexive graph neighborhood at level zero and pairs at
distance at most two at its top. Its local reduction shortens four-edge paths.
An outer induction on cycle length and an inner induction on the first
relation level implement the source's minimal-cycle, minimal-type proof.
The conclusion is generation by triangles and squares in the existing
nonabelian normal walk closure. No diameter bound is used.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄* (1991),
Hypothesis A and (1.2), printed pp.590–591.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction
open SimpleGraph SimpleGraph.WalkClosure
variable {V : Type*} (Γ : SimpleGraph V)

def Near (x y : V) : Prop := x = y ∨ Γ.Adj x y

def Two (x y : V) : Prop := Near Γ x y ∨ ∃ u, Γ.Adj x u ∧ Γ.Adj u y

def ProperTwo (x y : V) : Prop := ¬ Near Γ x y ∧ ∃ u, Γ.Adj x u ∧ Γ.Adj u y

structure HypothesisA (N : ℕ) where
  rel : ℕ → V → V → Prop
  symm : ∀ i x y, rel i x y → rel i y x
  mono : ∀ i j, i ≤ j → ∀ x y, rel i x y → rel j x y
  zero : ∀ x y, rel 0 x y ↔ Near Γ x y
  bounded : ∀ i x y, rel i x y → Two Γ x y
  full : ∀ x y, Two Γ x y → rel N x y
  reduce : ∀ k, k < N → ∀ x y z,
    rel (k + 1) x y → ProperTwo Γ x y → ProperTwo Γ x z →
    ∃ u v, Γ.Adj x u ∧ rel k y u ∧ Γ.Adj x v ∧ Γ.Adj z v ∧ rel (min k 1) u v

variable {Γ}
theorem near_path {x y : V} (h : Near Γ x y) : ∃ p : Γ.Walk x y, p.length ≤ 1 := by
  rcases h with rfl | h
  · exact ⟨.nil, by simp⟩
  · exact ⟨h.toWalk, by simp⟩

theorem two_path {x y : V} (h : Two Γ x y) : ∃ p : Γ.Walk x y, p.length ≤ 2 := by
  rcases h with h | ⟨u, hxu, huy⟩
  · obtain ⟨p, hp⟩ := near_path h
    exact ⟨p, by omega⟩
  · exact ⟨.cons hxu huy.toWalk, by simp⟩

namespace HypothesisA
variable {N : ℕ} (A : HypothesisA Γ N)

/-- The four-edge shortening (*) in the proof of AS91 (1.2). -/
theorem shorten_four (hN : 0 < N) {a b c d e : V}
    (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hcd : Γ.Adj c d) (hde : Γ.Adj d e)
    (hac : A.rel 1 a c) :
    ∃ q : Γ.Walk a e, q.length ≤ 3 ∧
      Rel (shortCycles Γ) (.cons hab (.cons hbc (.cons hcd hde.toWalk))) q := by
  classical
  by_cases hn : Near Γ a c
  · obtain ⟨p, hp⟩ := near_path hn
    refine ⟨p.append (.cons hcd hde.toWalk), by simp; omega, ?_⟩
    exact Rel.append (short_paths (.cons hab hbc.toWalk) p (by simp; omega)) (.refl _)
  by_cases hn' : Near Γ c e
  · obtain ⟨p, hp⟩ := near_path hn'
    refine ⟨(Walk.cons hab hbc.toWalk).append p, by simp; omega, ?_⟩
    exact Rel.append (.refl (Walk.cons hab hbc.toWalk)) (short_paths (.cons hcd hde.toWalk) p (by simp; omega))
  have hca : ProperTwo Γ c a := ⟨by
    rintro (he | ha)
    · exact hn (Or.inl he.symm)
    · exact hn (Or.inr ha.symm), b, hbc.symm, hab.symm⟩
  obtain ⟨u, v, hcu, hau, hcv, hev, huv⟩ :=
    A.reduce 0 hN c a e (A.symm 1 a c hac) hca ⟨hn', d, hcd, hde⟩
  obtain ⟨p, hp⟩ := near_path ((A.zero a u).mp hau)
  obtain ⟨q, hq⟩ := near_path ((A.zero u v).mp huv)
  refine ⟨(p.append q).append hev.symm.toWalk, by simp; omega, ?_⟩
  have hleft := short_paths (.cons hab hbc.toWalk) (p.append hcu.symm.toWalk) (by simp; omega)
  have hright := short_paths (.cons hcd hde.toWalk) (.cons hcv hev.symm.toWalk) (by simp)
  have hmiddle := short_paths (.cons hcu.symm hcv.toWalk) q (by simp; omega)
  exact (Rel.append hleft hright).trans (by
    simpa only [← Walk.append_assoc, Walk.cons_append, Walk.nil_append] using
      Rel.append (Rel.append (.refl p) hmiddle) (.refl hev.symm.toWalk))

/-- Length induction outside, relation-level induction inside: the minimal
cycle and minimal-type argument of AS91 (1.2), without choosing a cycle. -/
theorem closed_of_pair (n : ℕ)
    (small : ∀ a (p : Γ.Walk a a), p.length < n → Rel (shortCycles Γ) p .nil)
    (k : ℕ) (hk : k ≤ N) {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (p : Γ.Walk c a) (hp : (Walk.cons hab (.cons hbc p)).length ≤ n)
    (hac : A.rel k a c) :
    Rel (shortCycles Γ) (.cons hab (.cons hbc p)) .nil := by
  classical
  have close_near {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
      (p : Γ.Walk c a) (hp : (Walk.cons hab (.cons hbc p)).length ≤ n)
      (hac : Near Γ a c) : Rel (shortCycles Γ) (.cons hab (.cons hbc p)) .nil := by
    obtain ⟨q, hq⟩ := near_path hac
    have hrel := Rel.append (short_paths (.cons hab hbc.toWalk) q (by simp; omega)) (.refl p)
    exact hrel.trans (small a (q.append p) (by
      simp only [Walk.length_append]
      simp only [Walk.length_cons] at hp
      omega))
  induction k generalizing a b c with
  | zero => exact close_near hab hbc p hp ((A.zero a c).mp hac)
  | succ k ih =>
    by_cases hs : (Walk.cons hab (.cons hbc p)).length ≤ 4
    · exact .cycle _ hs
    by_cases hn : Near Γ a c
    · exact close_near hab hbc p hp hn
    cases p with
    | nil => simp at hs
    | @cons c d a hcd p =>
      cases p with
      | nil => simp at hs
      | @cons d e a hde p =>
        cases p with
        | nil => simp at hs
        | @cons e f a hef p =>
          have hpn : p.length + 5 ≤ n := by simpa [Walk.length_cons, Nat.add_assoc] using hp
          by_cases hce : Near Γ c e
          · obtain ⟨q, hq⟩ := near_path hce
            have heq := Rel.append
              (Rel.append (.refl (Walk.cons hab hbc.toWalk))
                (short_paths (.cons hcd hde.toWalk) q (by simp; omega)))
              (.refl (Walk.cons hef p))
            apply heq.trans
            apply small
            simp only [Walk.length_append, Walk.length_cons, Walk.length_nil]
            omega
          have hca : ProperTwo Γ c a := ⟨by
            rintro (he | ha)
            · exact hn (Or.inl he.symm)
            · exact hn (Or.inr ha.symm), b, hbc.symm, hab.symm⟩
          obtain ⟨u, v, hcu, hau, hcv, hev, huv⟩ :=
            A.reduce k (by omega) c a e (A.symm _ a c hac) hca ⟨hce, d, hcd, hde⟩
          obtain ⟨q, hq⟩ := two_path (A.bounded k a u hau)
          /- A lower-type prefix closes both the auxiliary pentagon and the
          replacement cycle. If its length is less than two, length induction
          alone suffices. -/
          have lower (r : Γ.Walk u a) (hlen : (q.append r).length ≤ n)
              (hshort : q.length < 2 → (q.append r).length < n) :
              Rel (shortCycles Γ) (q.append r) .nil := by
            by_cases hq' : q.length < 2
            · exact small _ _ (hshort hq')
            cases q with
            | nil => simp at hq'
            | @cons a w u haw q =>
              cases q with
              | nil => simp at hq'
              | @cons w u' u hwu q =>
                have hz : q.length = 0 := by simp only [Walk.length_cons] at hq; omega
                cases q with
                | nil => exact ih (by omega) haw hwu r hlen hau
                | cons _ _ => simp at hz
          have hleft : Rel (shortCycles Γ) (.cons hab hbc.toWalk)
              (q.append hcu.symm.toWalk) := by
            apply Rel.symm
            apply rel_of_closed
            rw [← Walk.append_assoc]
            apply lower (hcu.symm.toWalk.append (Walk.cons hab hbc.toWalk).reverse)
            · simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons, Walk.length_nil]
              omega
            · intro hq'
              simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons, Walk.length_nil]
              omega
          have huv' : A.rel 1 u v := A.mono _ _ (min_le_right _ _) _ _ huv
          obtain ⟨r, hr, hrel⟩ := A.shorten_four (by omega) hcu.symm hcv hev.symm hef huv'
          have hright := short_paths (.cons hcd hde.toWalk) (.cons hcv hev.symm.toWalk) (by simp)
          have hrepl : Rel (shortCycles Γ)
              (.cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef p)))))
              ((q.append r).append p) := by
            have h₁ := Rel.append (Rel.append hleft hright) (.refl (Walk.cons hef p))
            have h₂ := Rel.append (Rel.append (.refl q) hrel) (.refl p)
            exact h₁.trans (by
              simpa only [← Walk.append_assoc, Walk.cons_append, Walk.nil_append] using h₂)
          apply hrepl.trans
          rw [← Walk.append_assoc]
          apply lower (r.append p)
          · simp only [Walk.length_append]; omega
          · intro hq'
            simp only [Walk.length_append]; omega

/-- AS91 (1.2): the binary relation filtration generates every cycle from
triangles and squares, in normal nonabelian walk closure. -/
theorem four_generated (A : HypothesisA Γ N) : IsCycleBase (shortCycles Γ) := by
  have all : ∀ n a (p : Γ.Walk a a), p.length ≤ n → Rel (shortCycles Γ) p .nil := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a p hp
      cases p with
      | nil => exact .refl _
      | @cons a b a hab p =>
        cases p with
        | nil => exact (hab.ne rfl).elim
        | @cons b c a hbc p =>
          exact A.closed_of_pair n
            (fun a q hq => ih q.length hq a q le_rfl) N le_rfl hab hbc p hp
            (A.full a c (Or.inr ⟨b, hab, hbc⟩))
  exact fun a p => all p.length a p le_rfl

end HypothesisA
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction
