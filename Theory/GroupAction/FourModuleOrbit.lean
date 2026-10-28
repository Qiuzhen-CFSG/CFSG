module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Tactic.FinCases

/-!
# Four modules and a noncommuting pair

Let a group permute four objects. An index-two subgroup preserves the first
pair, and a chosen actor sends that pair to the other pair. If an invariant
symmetric relation joins the first object to its image but does not join that
image to the second object, the image of the action is a regular Klein four
group. The proof first excludes the four-cycle for the chosen actor, then
restricts the index-two subgroup to two permutations. No permutation table is
assumed and no classification of two-subgroups of the symmetric group is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
C.5.6(7), printed p.158. In that application the relation is noncommutation of
subgroups and the objects are the two modules and their conjugates.
-/

@[expose] public section

namespace FourModuleOrbit
abbrev Point := Fin 4
abbrev Perm := Equiv.Perm Point

def Table (p : Perm) : Prop :=
  (p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 2 ∧ p 3 = 3) ∨
  (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 3 ∧ p 3 = 2) ∨
  (p 0 = 2 ∧ p 1 = 3 ∧ p 2 = 0 ∧ p 3 = 1) ∨
  (p 0 = 3 ∧ p 1 = 2 ∧ p 2 = 1 ∧ p 3 = 0)

private theorem point_cases (i : Point) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp

private theorem pair_image (p : Perm) (h0 : p 0 = 2) (h1 : p 1 = 3)
    (R : Point → Point → Prop) (hR : ∀ i j, R i j → R (p i) (p j))
    (hr : R 0 2) (hn : ¬ R 2 1) :
    p 2 = 0 ∧ p 3 = 1 := by
  have hi02 : p 0 ≠ p 2 := p.injective.ne (by decide)
  have hi12 : p 1 ≠ p 2 := p.injective.ne (by decide)
  have hi03 : p 0 ≠ p 3 := p.injective.ne (by decide)
  have hi13 : p 1 ≠ p 3 := p.injective.ne (by decide)
  have hi23 : p 2 ≠ p 3 := p.injective.ne (by decide)
  have h2 : p 2 = 0 := by
    rcases point_cases (p 2) with h | h | h | h
    · exact h
    · exact False.elim (hn (by simpa [h0, h] using hR 0 2 hr))
    · exact False.elim (hi02 (h0.trans h.symm))
    · exact False.elim (hi12 (h1.trans h.symm))
  refine ⟨h2, ?_⟩
  rcases point_cases (p 3) with h | h | h | h
  · exact False.elim (hi23 (h2.trans h.symm))
  · exact h
  · exact False.elim (hi03 (h0.trans h.symm))
  · exact False.elim (hi13 (h1.trans h.symm))

private theorem pair_preserving (p : Perm) (h0 : p 0 = 0 ∨ p 0 = 1)
    (h1 : p 1 = 0 ∨ p 1 = 1)
    (R : Point → Point → Prop) (hR : ∀ i j, R i j → R (p i) (p j))
    (hr : R 0 2) (hn12 : ¬ R 1 2) (hn03 : ¬ R 0 3) :
    Table p := by
  have hi01 : p 0 ≠ p 1 := p.injective.ne (by decide)
  have hi02 : p 0 ≠ p 2 := p.injective.ne (by decide)
  have hi12 : p 1 ≠ p 2 := p.injective.ne (by decide)
  have hi03 : p 0 ≠ p 3 := p.injective.ne (by decide)
  have hi13 : p 1 ≠ p 3 := p.injective.ne (by decide)
  have hi23 : p 2 ≠ p 3 := p.injective.ne (by decide)
  have h2 := point_cases (p 2)
  have h3 := point_cases (p 3)
  rcases h0 with h0 | h0
  · have h1 : p 1 = 1 := h1.resolve_left (fun h => hi01 (h0.trans h.symm))
    have h2 : p 2 = 2 := by
      rcases h2 with h | h | h | h
      · exact False.elim (hi02 (h0.trans h.symm))
      · exact False.elim (hi12 (h1.trans h.symm))
      · exact h
      · exact False.elim (hn03 (by simpa [h0, h] using hR 0 2 hr))
    have h3 : p 3 = 3 := by
      rcases h3 with h | h | h | h
      · exact False.elim (hi03 (h0.trans h.symm))
      · exact False.elim (hi13 (h1.trans h.symm))
      · exact False.elim (hi23 (h2.trans h.symm))
      · exact h
    exact Or.inl ⟨h0, h1, h2, h3⟩
  · have h1 : p 1 = 0 := h1.resolve_right (fun h => hi01 (h0.trans h.symm))
    have h2 : p 2 = 3 := by
      rcases h2 with h | h | h | h
      · exact False.elim (hi12 (h1.trans h.symm))
      · exact False.elim (hi02 (h0.trans h.symm))
      · exact False.elim (hn12 (by simpa [h0, h] using hR 0 2 hr))
      · exact h
    have h3 : p 3 = 2 := by
      rcases h3 with h | h | h | h
      · exact False.elim (hi13 (h1.trans h.symm))
      · exact False.elim (hi03 (h0.trans h.symm))
      · exact h
      · exact False.elim (hi23 (h2.trans h.symm))
    exact Or.inr (Or.inl ⟨h0, h1, h2, h3⟩)

private theorem Table.square {p : Perm} (hp : Table p) : p ^ 2 = 1 := by
  ext i
  rcases hp with h | h | h | h <;> rcases h with ⟨h0,h1,h2,h3⟩ <;>
    fin_cases i <;> simp [pow_two, Equiv.Perm.mul_apply, h0,h1,h2,h3]

private theorem Table.ext {p q : Perm} (hp : Table p) (hq : Table q)
    (h : p 0 = q 0) : p = q := by
  rcases hp with hp | hp | hp | hp <;> rcases hp with ⟨p0,p1,p2,p3⟩ <;>
    rcases hq with hq | hq | hq | hq <;> rcases hq with ⟨q0,q1,q2,q3⟩ <;>
    simp only [p0,q0] at h
  all_goals try contradiction
  all_goals ext i; fin_cases i <;> simp [p0,p1,p2,p3,q0,q1,q2,q3]

private theorem Table.mul {p q : Perm} (hp : Table p) (hq : Table q) : Table (p*q) := by
  rcases hp with hp | hp | hp | hp <;> rcases hp with ⟨p0,p1,p2,p3⟩ <;>
    rcases hq with hq | hq | hq | hq <;> rcases hq with ⟨q0,q1,q2,q3⟩ <;>
    simp [Table, Equiv.Perm.mul_apply, p0,p1,p2,p3,q0,q1,q2,q3]

/-- An index-two orbit pair, its translating element, and the original
noncommutation facts. The permutation table is a conclusion, not an input. -/
structure Setup {Γ : Type*} [Group Γ] (ρ : Γ →* Perm)
    (H : Subgroup Γ) (x t : Γ) (R : Point → Point → Prop) : Prop where
  index_two : H.index = 2
  pair_zero : ∀ g ∈ H, ρ g 0 = 0 ∨ ρ g 0 = 1
  pair_one : ∀ g ∈ H, ρ g 1 = 0 ∨ ρ g 1 = 1
  x_zero : ρ x 0 = 2
  x_one : ρ x 1 = 3
  t_mem : t ∈ H
  t_zero : ρ t 0 = 1
  symmetric : ∀ i j, R i j → R j i
  invariant : ∀ g i j, R i j → R (ρ g i) (ρ g j)
  noncommuting : R 0 2
  cross_commuting : ¬ R 2 1

variable {Γ : Type*} [Group Γ] {ρ : Γ →* Perm}
  {H : Subgroup Γ} {x t : Γ} {R : Point → Point → Prop}

theorem Setup.x_table (h : Setup ρ H x t R) :
    ρ x 0 = 2 ∧ ρ x 1 = 3 ∧ ρ x 2 = 0 ∧ ρ x 3 = 1 :=
  ⟨h.x_zero, h.x_one, pair_image (ρ x) h.x_zero h.x_one R
    (h.invariant x) h.noncommuting h.cross_commuting⟩

theorem Setup.other_cross_commuting (h : Setup ρ H x t R) : ¬ R 0 3 := by
  intro hr
  have hp := h.x_table
  exact h.cross_commuting (by simpa only [hp.1, hp.2.2.2] using h.invariant x 0 3 hr)

theorem Setup.table (h : Setup ρ H x t R) (g : Γ) : Table (ρ g) := by
  have hxT : Table (ρ x) := Or.inr (Or.inr (Or.inl h.x_table))
  have hHT (k : Γ) (hk : k ∈ H) : Table (ρ k) :=
    pair_preserving (ρ k) (h.pair_zero k hk) (h.pair_one k hk) R
      (h.invariant k) h.noncommuting
      (fun hr => h.cross_commuting (h.symmetric 1 2 hr)) h.other_cross_commuting
  by_cases hg : g ∈ H
  · exact hHT g hg
  have hx : x ∉ H := by
    intro hx
    rcases h.pair_zero x hx with hz | hz <;> rw [h.x_zero] at hz <;> contradiction
  have hxg : x * g ∈ H := (H.mul_mem_iff_of_index_two h.index_two).mpr (by simp [hx,hg])
  have ht := hxT.mul (hHT (x*g) hxg)
  rw [map_mul, ← mul_assoc, ← pow_two, hxT.square, one_mul] at ht
  exact ht

theorem Setup.square (h : Setup ρ H x t R) (g : Γ) : ρ g ^ 2 = 1 :=
  (h.table g).square

theorem Setup.regular (h : Setup ρ H x t R) :
    Function.Bijective (fun p : ρ.range => (p : Perm) 0) := by
  constructor
  · rintro ⟨p,g,rfl⟩ ⟨q,k,rfl⟩ he
    exact Subtype.ext (Table.ext (h.table g) (h.table k) he)
  · intro i
    rcases point_cases i with rfl | rfl | rfl | rfl
    · exact ⟨⟨1, ⟨1, ρ.map_one⟩⟩, rfl⟩
    · exact ⟨⟨ρ t, ⟨t,rfl⟩⟩, h.t_zero⟩
    · exact ⟨⟨ρ x, ⟨x,rfl⟩⟩, h.x_zero⟩
    · refine ⟨⟨ρ (x*t), ⟨x*t,rfl⟩⟩, ?_⟩
      simp only [map_mul, Equiv.Perm.mul_apply, h.t_zero, h.x_one]

theorem Setup.card_range (h : Setup ρ H x t R) : Nat.card ρ.range = 4 := by
  rw [Nat.card_congr (Equiv.ofBijective _ h.regular)]
  exact Nat.card_fin 4

theorem Setup.isKleinFour (h : Setup ρ H x t R) : IsKleinFour ρ.range := by
  have : Nontrivial ρ.range := by
    refine ⟨⟨⟨ρ x, ⟨x,rfl⟩⟩, 1, ?_⟩⟩
    intro he
    have hz := congrArg (fun p : ρ.range => (p : Perm) 0) he
    change ρ x 0 = 0 at hz
    rw [h.x_zero] at hz
    contradiction
  refine ⟨h.card_range, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  rintro ⟨p,g,rfl⟩ hne
  exact orderOf_eq_prime (Subtype.ext (h.square g)) hne

theorem Setup.card_pair_range (h : Setup ρ H x t R) : Nat.card (H.map ρ) = 2 := by
  let a : H.map ρ := ⟨ρ t, ⟨t, h.t_mem, rfl⟩⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, a, ?_, ?_⟩
  · intro he
    have he0 := congrArg (fun p : H.map ρ => (p : Perm) 0) he
    change 0 = ρ t 0 at he0
    rw [h.t_zero] at he0
    contradiction
  · apply Set.eq_univ_of_forall
    rintro ⟨p,g,hg,rfl⟩
    rcases h.pair_zero g hg with he | he
    · apply Set.mem_insert_iff.mpr
      left
      apply Subtype.ext
      exact Table.ext (h.table g) (by simp [Table]) he
    · apply Set.mem_insert_iff.mpr
      right
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact Table.ext (h.table g) (h.table t) (he.trans h.t_zero.symm)

end FourModuleOrbit

end
