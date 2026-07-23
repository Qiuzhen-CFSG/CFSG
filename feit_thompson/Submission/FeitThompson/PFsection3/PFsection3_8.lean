module

public import Submission.FeitThompson.PFsection3.PFsection3_7

/-!
# Peterfalvi, Section 3, Proposition (3.8)

This file begins the coefficient-counting analysis following Proposition (3.7).
The first lemmas are the book-facing algebraic normal forms used in the three
cases of PF (3.8).
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section3

universe v
universe u

/-! ## (3.8) -/

/--
Peterfalvi (3.8): under Hypothesis (3.6), if `|W₁| < |W₂|` and fewer than
`2 |W₁|` coefficients are nonzero, then either `ψ = β`, or
`NC(ψ) = |W₁|` and exactly one full column of coefficients occurs, or
`NC(ψ) = |W₂|` and exactly one full row of coefficients occurs.
-/
@[expose] public def proposition_3_8_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (_h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω) :
    Prop :=
  Nat.card W1 < Nat.card W2 →
    coefficientNonzeroCount a < 2 * Nat.card W1 →
      ψ = β ∨
        (coefficientNonzeroCount a = Nat.card W1 ∧
          ∃ c : ℂ, ∃ j : J,
            ψ = c • (∑ i : I, σ (ω i j)) + β) ∨
        (coefficientNonzeroCount a = Nat.card W2 ∧
          ∃ c : ℂ, ∃ i : I,
            ψ = c • (∑ j : J, σ (ω i j)) + β)


public theorem coefficientNonzeroCount_eq_zero_iff
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) :
    coefficientNonzeroCount a = 0 ↔ ∀ i j, a i j = 0 := by
  classical
  simp [coefficientNonzeroCount, Fintype.card_subtype]

public theorem hypothesis_3_6_eq_beta_of_all_coeff_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (ha : ∀ i j, a i j = 0) :
    ψ = β := by
  have hψ := h36.2.2.1
  rw [hψ]
  simp [ha]

public theorem hypothesis_3_6_all_coeff_zero_of_eq_beta
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (hψeq : ψ = β) :
    ∀ i j, a i j = 0 := by
  classical
  rcases h36 with ⟨h32, hβorth, hψ, _hβclass, _hψclass, _hvanish⟩
  intro i j
  have hcoeff :
      Section1.scalarProduct G
        (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2))
        (σ (ω i j)) = a i j := by
    have hsumfun :
        (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) =
          (fun g : G => ∑ p : I × J, (a p.1 p.2 • σ (ω p.1 p.2)) g) := by
      ext g
      simp
    rw [hsumfun]
    rw [Section1.scalarProduct_fintype_sum_left]
    rw [Finset.sum_eq_single (i, j)]
    · rw [Section1.scalarProduct_smul_left]
      have hself :
          Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
        exact h32.1 (ω i j) (ω i j) (hω.is_class i j) (hω.is_class i j)
          |>.trans (by simpa using hω.orthonormal (i, j) (i, j))
      simp [hself]
    · intro p _hp hpne
      rw [Section1.scalarProduct_smul_left]
      have horth :
          Section1.scalarProduct G (σ (ω p.1 p.2)) (σ (ω i j)) = 0 := by
        have hsp :=
          h32.1 (ω p.1 p.2) (ω i j) (hω.is_class p.1 p.2) (hω.is_class i j)
        have hpne' : p ≠ (i, j) := hpne
        simpa [hpne'] using hsp.trans (by simpa [hpne'] using hω.orthonormal p (i, j))
      simp [horth]
    · intro hnot
      exact False.elim (hnot (by simp))
  have hmain :
      Section1.scalarProduct G
          ((∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) + β)
          (σ (ω i j)) =
        Section1.scalarProduct G β (σ (ω i j)) := by
    rw [← hψ, hψeq]
  rw [Section1.scalarProduct_add_left, hcoeff,
    hβorth (ω i j) (hω.is_class i j)] at hmain
  simpa using hmain

public theorem coefficientNonzeroCount_swap
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) :
    coefficientNonzeroCount (fun j i => a i j) = coefficientNonzeroCount a := by
  classical
  unfold coefficientNonzeroCount
  refine Fintype.card_congr ?_
  refine
    { toFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
      invFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p with
    | mk p hp =>
      cases p
      rfl
  · intro p
    cases p with
    | mk p hp =>
      cases p
      rfl

public theorem sum_sigma_single_column
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (c : ℂ) (j : J) :
    (∑ p : I × J,
        (if p.2 = j then c else 0) • σ (ω p.1 p.2)) =
      c • (∑ i : I, σ (ω i j)) := by
  classical
  rw [Fintype.sum_prod_type]
  simp [Finset.smul_sum]

public theorem sum_sigma_single_row
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (c : ℂ) (i : I) :
    (∑ p : I × J,
        (if p.1 = i then c else 0) • σ (ω p.1 p.2)) =
      c • (∑ j : J, σ (ω i j)) := by
  classical
  rw [Fintype.sum_prod_type]
  simp [Finset.smul_sum]

public theorem hypothesis_3_6_eq_single_column_of_coefficients
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (c : ℂ) (j : J)
    (ha : ∀ i q, a i q = if q = j then c else 0) :
    ψ = c • (∑ i : I, σ (ω i j)) + β := by
  have hψ := h36.2.2.1
  rw [hψ]
  convert congrArg (fun x => x + β) (sum_sigma_single_column ω σ c j) using 1
  simp [ha]

public theorem hypothesis_3_6_eq_single_row_of_coefficients
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (c : ℂ) (i : I)
    (ha : ∀ p j, a p j = if p = i then c else 0) :
    ψ = c • (∑ j : J, σ (ω i j)) + β := by
  have hψ := h36.2.2.1
  rw [hψ]
  convert congrArg (fun x => x + β) (sum_sigma_single_row ω σ c i) using 1
  simp [ha]

public theorem proposition_3_8_of_zero_count
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (hcount : coefficientNonzeroCount a = 0) :
    ψ = β := by
  exact hypothesis_3_6_eq_beta_of_all_coeff_zero h36
    ((coefficientNonzeroCount_eq_zero_iff a).mp hcount)

public theorem proposition_3_8_column_exit
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (hcount : coefficientNonzeroCount a = Nat.card W1)
    (c : ℂ) (j : J)
    (ha : ∀ i q, a i q = if q = j then c else 0) :
    coefficientNonzeroCount a = Nat.card W1 ∧
      ∃ c : ℂ, ∃ j : J,
        ψ = c • (∑ i : I, σ (ω i j)) + β := by
  refine ⟨hcount, c, j, ?_⟩
  exact hypothesis_3_6_eq_single_column_of_coefficients h36 c j ha

public theorem proposition_3_8_row_exit
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (hcount : coefficientNonzeroCount a = Nat.card W2)
    (c : ℂ) (i : I)
    (ha : ∀ p j, a p j = if p = i then c else 0) :
    coefficientNonzeroCount a = Nat.card W2 ∧
      ∃ c : ℂ, ∃ i : I,
        ψ = c • (∑ j : J, σ (ω i j)) + β := by
  refine ⟨hcount, c, i, ?_⟩
  exact hypothesis_3_6_eq_single_row_of_coefficients h36 c i ha

public theorem finset_card_le_coefficientNonzeroCount
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) (s : Finset (I × J))
    (hs : ∀ p ∈ s, a p.1 p.2 ≠ 0) :
    s.card ≤ coefficientNonzeroCount a := by
  classical
  have hsub :
      s ⊆ Finset.univ.filter (fun p : I × J => a p.1 p.2 ≠ 0) := by
    intro p hp
    simp [hs p hp]
  rw [coefficientNonzeroCount, Fintype.card_subtype]
  exact Finset.card_le_card hsub

public theorem two_le_coefficientNonzeroCount_of_two_nonzero_cells
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (i0 i1 : I) (j0 j1 : J)
    (h00 : a i0 j0 ≠ 0) (h11 : a i1 j1 ≠ 0)
    (hi : i1 ≠ i0) :
    2 ≤ coefficientNonzeroCount a := by
  classical
  let s : Finset (I × J) := {(i0, j0), (i1, j1)}
  have hs : ∀ p ∈ s, a p.1 p.2 ≠ 0 := by
    intro p hp
    simp [s] at hp
    rcases hp with hp | hp
    · simpa [hp] using h00
    · simpa [hp] using h11
  have hpneq : (i0, j0) ≠ (i1, j1) := by
    intro hpair
    exact hi (congrArg Prod.fst hpair).symm
  have hcard : s.card = 2 := by
    dsimp [s]
    rw [Finset.card_pair]
    simp [hpneq]
  rw [← hcard]
  exact finset_card_le_coefficientNonzeroCount a s hs

public theorem coefficientNonzeroCount_ge_card_left_of_nonzero_column
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (j : J)
    (h : ∀ i : I, a i j ≠ 0) :
    Fintype.card I ≤ coefficientNonzeroCount a := by
  classical
  let s : Finset (I × J) := Finset.univ.image (fun i : I => (i, j))
  have hs : ∀ p ∈ s, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, _hi, rfl⟩
    exact h i
  have hcard : s.card = Fintype.card I := by
    dsimp [s]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.fst hxy
  rw [← hcard]
  exact finset_card_le_coefficientNonzeroCount a s hs

public theorem coefficientNonzeroCount_ge_card_right_of_nonzero_row
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (i : I)
    (h : ∀ j : J, a i j ≠ 0) :
    Fintype.card J ≤ coefficientNonzeroCount a := by
  classical
  let s : Finset (I × J) := Finset.univ.image (fun j : J => (i, j))
  have hs : ∀ p ∈ s, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, _hj, rfl⟩
    exact h j
  have hcard : s.card = Fintype.card J := by
    dsimp [s]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.snd hxy
  rw [← hcard]
  exact finset_card_le_coefficientNonzeroCount a s hs

public theorem coefficient_cell_ne_zero_of_two_axes_zero
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) (i0 i : I) (j0 j : J)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (h00 : a i0 j0 ≠ 0)
    (hi0 : a i j0 = 0) (h0j : a i0 j = 0) :
    a i j ≠ 0 := by
  intro hij
  have h := hrect i i0 j j0
  rw [hi0, h0j, hij] at h
  simp at h
  exact h00 h

public theorem coefficient_cell_eq_neg_base_of_two_axes_zero
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) (i0 i : I) (j0 j : J)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hi0 : a i j0 = 0) (h0j : a i0 j = 0) :
    a i j = -a i0 j0 := by
  have h := hrect i i0 j j0
  rw [hi0, h0j] at h
  linear_combination h

public theorem coefficient_rectangle_solve
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) (r i : I) (s j : J)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j) :
    a i j = a i s + a r j - a r s := by
  have h := hrect i r j s
  linear_combination h

public theorem coefficients_eq_single_column_indicator
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r : I) (s : J)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (_hbase : a r s ≠ 0)
    (j' : J) (hj's : j' ≠ s)
    (hcolzero : ∀ j, j ≠ s → a r j = 0)
    (hintzero : ∀ i j, i ≠ r → j ≠ s → a i j = 0) :
    ∀ i j, a i j = if j = s then a r s else 0 := by
  intro i j
  by_cases hjs : j = s
  · subst j
    by_cases hir : i = r
    · subst i
      simp
    · have hrect' := hrect i r s j'
      rw [hintzero i j' hir hj's, hcolzero j' hj's] at hrect'
      simpa using hrect'
  · by_cases hir : i = r
    · subst i
      simp [hcolzero, hjs]
    · simp [hintzero i j hir hjs, hjs]

public theorem coefficients_eq_single_row_indicator
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r : I) (s : J)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (_hbase : a r s ≠ 0)
    (i' : I) (hi'r : i' ≠ r)
    (hrowzero : ∀ i, i ≠ r → a i s = 0)
    (hintzero : ∀ i j, i ≠ r → j ≠ s → a i j = 0) :
    ∀ i j, a i j = if i = r then a r s else 0 := by
  intro i j
  by_cases hir : i = r
  · subst i
    by_cases hjs : j = s
    · subst j
      simp
    · have hrect' := hrect i' r j s
      rw [hintzero i' j hi'r hjs, hrowzero i' hi'r] at hrect'
      simpa using hrect'.symm
  · by_cases hjs : j = s
    · subst j
      simp [hrowzero, hir]
    · simp [hintzero i j hir hjs, hir]

public theorem coefficientNonzeroCount_eq_card_left_of_single_column
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (c : ℂ) (j : J)
    (hc : c ≠ 0)
    (ha : ∀ i q, a i q = if q = j then c else 0) :
    coefficientNonzeroCount a = Fintype.card I := by
  classical
  have hsupport : {p : I × J // a p.1 p.2 ≠ 0} ≃ I :=
    { toFun := fun p => p.1.1
      invFun := fun i => ⟨(i, j), by simp [ha, hc]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        have hpj : p.1.2 = j := by
          by_contra hpj
          have hpzero : a p.1.1 p.1.2 = 0 := by simp [ha, hpj]
          exact p.2 hpzero
        exact Prod.ext rfl hpj.symm
      right_inv := by intro i; rfl }
  exact Fintype.card_congr hsupport

public theorem coefficientNonzeroCount_eq_card_right_of_single_row
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (c : ℂ) (i : I)
    (hc : c ≠ 0)
    (ha : ∀ p j, a p j = if p = i then c else 0) :
    coefficientNonzeroCount a = Fintype.card J := by
  classical
  have hsupport : {p : I × J // a p.1 p.2 ≠ 0} ≃ J :=
    { toFun := fun p => p.1.2
      invFun := fun j => ⟨(i, j), by simp [ha, hc]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        have hpi : p.1.1 = i := by
          by_contra hpi
          have hpzero : a p.1.1 p.1.2 = 0 := by simp [ha, hpi]
          exact p.2 hpzero
        exact Prod.ext hpi.symm rfl
      right_inv := by intro j; rfl }
  exact Fintype.card_congr hsupport

public theorem card_univ_erase_erase
    {I : Type*} [Fintype I] [DecidableEq I] {r i : I} (hri : i ≠ r) :
    ((Finset.univ.erase r).erase i).card = Fintype.card I - 2 := by
  classical
  have hi_mem : i ∈ Finset.univ.erase r := by simp [hri]
  rw [Finset.card_erase_of_mem hi_mem]
  rw [Finset.card_erase_of_mem (by simp : r ∈ (Finset.univ : Finset I))]
  exact Nat.sub_sub _ _ _

public theorem card_subtype_ne_and_ne
    {I : Type*} [Fintype I] [DecidableEq I] {r i : I} (hri : i ≠ r) :
    Fintype.card {x : I // x ≠ r ∧ x ≠ i} = Fintype.card I - 2 := by
  classical
  have hcard := card_univ_erase_erase (I := I) hri
  rw [Fintype.card_subtype]
  let s : Finset I := (Finset.univ.erase r).erase i
  have hfilter : Finset.univ.filter (fun x : I => x ≠ r ∧ x ≠ i) = s := by
    ext x
    by_cases hxr : x = r <;> by_cases hxi : x = i <;> simp [s, hxr, hxi]
  simpa [s, hfilter] using hcard

private theorem two_cells_disjoint_erase_left_column
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 i1 : I) (j0 j1 : J) :
    let s0 : Finset (I × J) := {(i0, j0), (i1, j1)}
    let sI : Finset (I × J) :=
      ((Finset.univ.erase i0).erase i1).image (fun i => (i, j0))
    Disjoint s0 sI := by
  classical
  intro s0 sI
  rw [Finset.disjoint_left]
  intro p hp0 hpI
  have hp0_cases : p = (i0, j0) ∨ p = (i1, j1) := by
    simpa [s0] using hp0
  rcases Finset.mem_image.mp hpI with ⟨k, hk, hpk⟩
  have hk_ne_i1 : k ≠ i1 := (Finset.mem_erase.mp hk).1
  have hk_ne_i0 : k ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  rcases hp0_cases with hp | hp
  · have hk_eq : k = i0 := by
      have hfst := congrArg Prod.fst hpk
      simpa [hp] using hfst
    exact hk_ne_i0 hk_eq
  · have hk_eq : k = i1 := by
      have hfst := congrArg Prod.fst hpk
      simpa [hp] using hfst
    exact hk_ne_i1 hk_eq

private theorem two_cells_disjoint_erase_base_row
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 i1 : I) (j0 j1 : J) :
    let s0 : Finset (I × J) := {(i0, j0), (i1, j1)}
    let sJ : Finset (I × J) :=
      ((Finset.univ.erase j0).erase j1).image (fun j => (i0, j))
    Disjoint s0 sJ := by
  classical
  intro s0 sJ
  rw [Finset.disjoint_left]
  intro p hp0 hpJ
  have hp0_cases : p = (i0, j0) ∨ p = (i1, j1) := by
    simpa [s0] using hp0
  rcases Finset.mem_image.mp hpJ with ⟨k, hk, hpk⟩
  have hk_ne_j1 : k ≠ j1 := (Finset.mem_erase.mp hk).1
  have hk_ne_j0 : k ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  rcases hp0_cases with hp | hp
  · have hk_eq : k = j0 := by
      have hsnd := congrArg Prod.snd hpk
      simpa [hp] using hsnd
    exact hk_ne_j0 hk_eq
  · have hk_eq : k = j1 := by
      have hsnd := congrArg Prod.snd hpk
      simpa [hp] using hsnd
    exact hk_ne_j1 hk_eq

private theorem erase_left_column_disjoint_erase_base_row
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 i1 : I) (j0 j1 : J) :
    let sI : Finset (I × J) :=
      ((Finset.univ.erase i0).erase i1).image (fun i => (i, j0))
    let sJ : Finset (I × J) :=
      ((Finset.univ.erase j0).erase j1).image (fun j => (i0, j))
    Disjoint sI sJ := by
  classical
  intro sI sJ
  rw [Finset.disjoint_left]
  intro p hpI hpJ
  rcases Finset.mem_image.mp hpI with ⟨i, hi, hpi⟩
  rcases Finset.mem_image.mp hpJ with ⟨j, _hj, hpj⟩
  have hi_ne_i0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hfst : i = i0 := by
    have h := congrArg Prod.fst (hpi.trans hpj.symm)
    simpa using h
  exact hi_ne_i0 hfst

private theorem three_piece_support_card
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 i1 : I) (j0 j1 : J) (hi : i1 ≠ i0) (hj : j1 ≠ j0) :
    let s0 : Finset (I × J) := {(i0, j0), (i1, j1)}
    let sI : Finset (I × J) :=
      ((Finset.univ.erase i0).erase i1).image (fun i => (i, j0))
    let sJ : Finset (I × J) :=
      ((Finset.univ.erase j0).erase j1).image (fun j => (i0, j))
    (s0 ∪ sI ∪ sJ).card =
      2 + (Fintype.card I - 2) + (Fintype.card J - 2) := by
  classical
  intro s0 sI sJ
  have h0I : Disjoint s0 sI := two_cells_disjoint_erase_left_column i0 i1 j0 j1
  have h0J : Disjoint s0 sJ := two_cells_disjoint_erase_base_row i0 i1 j0 j1
  have hIJ : Disjoint sI sJ := erase_left_column_disjoint_erase_base_row i0 i1 j0 j1
  have h0I_J : Disjoint (s0 ∪ sI) sJ := by
    rw [Finset.disjoint_left]
    intro p hp hpJ
    rcases Finset.mem_union.mp hp with hp0 | hpI
    · exact (Finset.disjoint_left.mp h0J) hp0 hpJ
    · exact (Finset.disjoint_left.mp hIJ) hpI hpJ
  have hcard0 : s0.card = 2 := by
    dsimp [s0]
    have hpneq : (i0, j0) ≠ (i1, j1) := by
      intro h
      exact hi (congrArg Prod.fst h).symm
    rw [Finset.card_pair]
    simp [hpneq]
  have hcardI : sI.card = Fintype.card I - 2 := by
    dsimp [sI]
    rw [Finset.card_image_iff.mpr]
    · exact card_univ_erase_erase hi
    · intro x hx y hy hxy
      exact congrArg Prod.fst hxy
  have hcardJ : sJ.card = Fintype.card J - 2 := by
    dsimp [sJ]
    rw [Finset.card_image_iff.mpr]
    · exact card_univ_erase_erase hj
    · intro x hx y hy hxy
      exact congrArg Prod.snd hxy
  calc
    (s0 ∪ sI ∪ sJ).card = (s0 ∪ sI).card + sJ.card := by
      exact Finset.card_union_of_disjoint h0I_J
    _ = s0.card + sI.card + sJ.card := by
      rw [Finset.card_union_of_disjoint h0I]
    _ = 2 + (Fintype.card I - 2) + (Fintype.card J - 2) := by
      rw [hcard0, hcardI, hcardJ]

private theorem three_piece_le_coefficientNonzeroCount
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (i0 i1 : I) (j0 j1 : J)
    (hi : i1 ≠ i0) (hj : j1 ≠ j0)
    (h00 : a i0 j0 ≠ 0) (h11 : a i1 j1 ≠ 0)
    (hcol : ∀ i, i ≠ i0 → i ≠ i1 → a i j0 ≠ 0)
    (hrow : ∀ j, j ≠ j0 → j ≠ j1 → a i0 j ≠ 0) :
    2 + (Fintype.card I - 2) + (Fintype.card J - 2) ≤
      coefficientNonzeroCount a := by
  classical
  let s0 : Finset (I × J) := {(i0, j0), (i1, j1)}
  let sI : Finset (I × J) :=
    ((Finset.univ.erase i0).erase i1).image (fun i => (i, j0))
  let sJ : Finset (I × J) :=
    ((Finset.univ.erase j0).erase j1).image (fun j => (i0, j))
  let s : Finset (I × J) := s0 ∪ sI ∪ sJ
  have hs_nonzero : ∀ p ∈ s, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp0I | hpJ
    · rcases Finset.mem_union.mp hp0I with hp0 | hpI
      · have hp_cases : p = (i0, j0) ∨ p = (i1, j1) := by
          simpa [s0] using hp0
        rcases hp_cases with hp | hp
        · simpa [hp] using h00
        · simpa [hp] using h11
      · rcases Finset.mem_image.mp hpI with ⟨i, hi_mem, rfl⟩
        have hi_ne_i1 : i ≠ i1 := (Finset.mem_erase.mp hi_mem).1
        have hi_ne_i0 : i ≠ i0 :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi_mem).2).1
        exact hcol i hi_ne_i0 hi_ne_i1
    · rcases Finset.mem_image.mp hpJ with ⟨j, hj_mem, rfl⟩
      have hj_ne_j1 : j ≠ j1 := (Finset.mem_erase.mp hj_mem).1
      have hj_ne_j0 : j ≠ j0 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hj_mem).2).1
      exact hrow j hj_ne_j0 hj_ne_j1
  have hcard :
      s.card = 2 + (Fintype.card I - 2) + (Fintype.card J - 2) := by
    simpa [s, s0, sI, sJ] using three_piece_support_card i0 i1 j0 j1 hi hj
  rw [← hcard]
  exact finset_card_le_coefficientNonzeroCount a s hs_nonzero

private theorem pf38_count_lower_bound_of_cross_zero
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r i : I) (s j : J)
    (hri : i ≠ r) (hjs : j ≠ s)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hbase : a r s ≠ 0) (his : a i s = 0) (hrj : a r j = 0) :
    2 + (Fintype.card I - 2) + (Fintype.card J - 2) ≤
      coefficientNonzeroCount a := by
  classical
  let D :=
    (Unit ⊕ Unit) ⊕
      ({k : I // k ≠ r ∧ k ≠ i} ⊕ {l : J // l ≠ s ∧ l ≠ j})
  let f : D → {p : I × J // a p.1 p.2 ≠ 0} := fun x =>
    match x with
    | Sum.inl (Sum.inl _) => ⟨(r, s), hbase⟩
    | Sum.inl (Sum.inr _) =>
        ⟨(i, j), coefficient_cell_ne_zero_of_two_axes_zero a r i s j
          hrect hbase his hrj⟩
    | Sum.inr (Sum.inl k) =>
        if hks : a k.1 s ≠ 0 then ⟨(k.1, s), hks⟩ else
          ⟨(k.1, j), coefficient_cell_ne_zero_of_two_axes_zero a r k.1 s j
            hrect hbase (by simpa using hks) hrj⟩
    | Sum.inr (Sum.inr l) =>
        if hrl : a r l.1 ≠ 0 then ⟨(r, l.1), hrl⟩ else
          ⟨(i, l.1), coefficient_cell_ne_zero_of_two_axes_zero a r i s l.1
            hrect hbase his (by simpa using hrl)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp [f] at hxy ⊢ <;> aesop
  have hle : Fintype.card D ≤ coefficientNonzeroCount a := by
    simpa [coefficientNonzeroCount] using Fintype.card_le_of_injective f hf
  have hcardD :
      Fintype.card D = 2 + (Fintype.card I - 2) + (Fintype.card J - 2) := by
    simp [D, card_subtype_ne_and_ne hri, card_subtype_ne_and_ne hjs, add_assoc]
  simpa [hcardD] using hle

public theorem pf38_numeric_lower_bound
    {m n : ℕ} (hm : Odd m) (hn : Odd n) (hlt : m < n) :
    2 + (m - 2) + (n - 2) ≥ 2 * m := by
  rcases hm with ⟨a, rfl⟩
  rcases hn with ⟨b, rfl⟩
  omega

private theorem pf38_cross_zero_contradiction
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r i : I) (s j : J)
    (hri : i ≠ r) (hjs : j ≠ s)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hbase : a r s ≠ 0) (his : a i s = 0) (hrj : a r j = 0)
    (hcount : coefficientNonzeroCount a < 2 * Fintype.card I)
    (hoddI : Odd (Fintype.card I))
    (hoddJ : Odd (Fintype.card J))
    (hltIJ : Fintype.card I < Fintype.card J) :
    False := by
  have hge := pf38_count_lower_bound_of_cross_zero a r i s j hri hjs hrect hbase his hrj
  have hnum :
      2 + (Fintype.card I - 2) + (Fintype.card J - 2) ≥ 2 * Fintype.card I := by
    exact pf38_numeric_lower_bound hoddI hoddJ hltIJ
  omega

private theorem coefficientNonzeroCount_ge_two_card_left_of_two_nonzero_columns
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (s q : J) (hqs : q ≠ s)
    (hcols : ∀ i, a i s ≠ 0)
    (hcolq : ∀ i, a i q ≠ 0) :
    2 * Fintype.card I ≤ coefficientNonzeroCount a := by
  classical
  let sS : Finset (I × J) := Finset.univ.image (fun i : I => (i, s))
  let sQ : Finset (I × J) := Finset.univ.image (fun i : I => (i, q))
  let supp : Finset (I × J) := sS ∪ sQ
  have hs_nonzero : ∀ p ∈ supp, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpS | hpQ
    · rcases Finset.mem_image.mp hpS with ⟨i, _hi, rfl⟩
      exact hcols i
    · rcases Finset.mem_image.mp hpQ with ⟨i, _hi, rfl⟩
      exact hcolq i
  have hdisj : Disjoint sS sQ := by
    rw [Finset.disjoint_left]
    intro p hpS hpQ
    rcases Finset.mem_image.mp hpS with ⟨i, _hi, hpi⟩
    rcases Finset.mem_image.mp hpQ with ⟨k, _hk, hpk⟩
    have hsq : s = q := by
      simpa [hpi, hpk] using congrArg Prod.snd (hpi.trans hpk.symm)
    exact hqs hsq.symm
  have hcardS : sS.card = Fintype.card I := by
    dsimp [sS]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.fst hxy
  have hcardQ : sQ.card = Fintype.card I := by
    dsimp [sQ]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.fst hxy
  have hcardSupp : supp.card = 2 * Fintype.card I := by
    calc
      supp.card = sS.card + sQ.card := Finset.card_union_of_disjoint hdisj
      _ = Fintype.card I + Fintype.card I := by rw [hcardS, hcardQ]
      _ = 2 * Fintype.card I := by omega
  rw [← hcardSupp]
  exact finset_card_le_coefficientNonzeroCount a supp hs_nonzero

private theorem coefficientNonzeroCount_ge_card_left_add_card_right_sub_one_of_nonzero_column_row_off
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (i : I) (s q : J) (_hqs : q ≠ s)
    (hcol : ∀ k, a k s ≠ 0)
    (hrow : ∀ t, t ≠ s → a i t ≠ 0) :
    Fintype.card I + (Fintype.card J - 1) ≤ coefficientNonzeroCount a := by
  classical
  let sC : Finset (I × J) := Finset.univ.image (fun k : I => (k, s))
  let sR : Finset (I × J) := (Finset.univ.erase s).image (fun t : J => (i, t))
  let supp : Finset (I × J) := sC ∪ sR
  have hs_nonzero : ∀ p ∈ supp, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpC | hpR
    · rcases Finset.mem_image.mp hpC with ⟨k, _hk, rfl⟩
      exact hcol k
    · rcases Finset.mem_image.mp hpR with ⟨t, ht, rfl⟩
      exact hrow t (Finset.mem_erase.mp ht).1
  have hdisj : Disjoint sC sR := by
    rw [Finset.disjoint_left]
    intro p hpC hpR
    rcases Finset.mem_image.mp hpC with ⟨k, _hk, hpk⟩
    rcases Finset.mem_image.mp hpR with ⟨t, ht, hpt⟩
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    have hst : s = t := by
      simpa [hpk, hpt] using congrArg Prod.snd (hpk.trans hpt.symm)
    exact hts hst.symm
  have hcardC : sC.card = Fintype.card I := by
    dsimp [sC]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.fst hxy
  have hcardR : sR.card = Fintype.card J - 1 := by
    dsimp [sR]
    rw [Finset.card_image_iff.mpr]
    · rw [Finset.card_erase_of_mem (by simp : s ∈ (Finset.univ : Finset J))]
      simp
    · intro x hx y hy hxy
      exact congrArg Prod.snd hxy
  have hcardSupp : supp.card = Fintype.card I + (Fintype.card J - 1) := by
    calc
      supp.card = sC.card + sR.card := Finset.card_union_of_disjoint hdisj
      _ = Fintype.card I + (Fintype.card J - 1) := by rw [hcardC, hcardR]
  rw [← hcardSupp]
  exact finset_card_le_coefficientNonzeroCount a supp hs_nonzero

private theorem coefficientNonzeroCount_ge_two_card_right_of_two_nonzero_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r i : I) (hri : i ≠ r)
    (hrowr : ∀ j, a r j ≠ 0)
    (hrowi : ∀ j, a i j ≠ 0) :
    2 * Fintype.card J ≤ coefficientNonzeroCount a := by
  classical
  let sR : Finset (I × J) := Finset.univ.image (fun j : J => (r, j))
  let sI : Finset (I × J) := Finset.univ.image (fun j : J => (i, j))
  let supp : Finset (I × J) := sR ∪ sI
  have hs_nonzero : ∀ p ∈ supp, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpR | hpI
    · rcases Finset.mem_image.mp hpR with ⟨j, _hj, rfl⟩
      exact hrowr j
    · rcases Finset.mem_image.mp hpI with ⟨j, _hj, rfl⟩
      exact hrowi j
  have hdisj : Disjoint sR sI := by
    rw [Finset.disjoint_left]
    intro p hpR hpI
    rcases Finset.mem_image.mp hpR with ⟨j, _hj, hpj⟩
    rcases Finset.mem_image.mp hpI with ⟨k, _hk, hpk⟩
    have hri' : r = i := by
      simpa [hpj, hpk] using congrArg Prod.fst (hpj.trans hpk.symm)
    exact hri hri'.symm
  have hcardR : sR.card = Fintype.card J := by
    dsimp [sR]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.snd hxy
  have hcardI : sI.card = Fintype.card J := by
    dsimp [sI]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact congrArg Prod.snd hxy
  have hcardSupp : supp.card = 2 * Fintype.card J := by
    calc
      supp.card = sR.card + sI.card := Finset.card_union_of_disjoint hdisj
      _ = Fintype.card J + Fintype.card J := by rw [hcardR, hcardI]
      _ = 2 * Fintype.card J := by omega
  rw [← hcardSupp]
  exact finset_card_le_coefficientNonzeroCount a supp hs_nonzero

public theorem exists_nonzero_coefficient_of_positive_count
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) (hpos : 0 < coefficientNonzeroCount a) :
    ∃ p : I × J, a p.1 p.2 ≠ 0 := by
  classical
  by_contra h
  have hzero : coefficientNonzeroCount a = 0 := by
    rw [coefficientNonzeroCount_eq_zero_iff]
    intro i j
    by_contra hij
    exact h ⟨(i, j), hij⟩
  omega

private theorem pf38_local_single_column
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r : I) (s j0 : J)
    (hj0s : j0 ≠ s)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hbase : a r s ≠ 0)
    (hcount : coefficientNonzeroCount a < 2 * Fintype.card I)
    (hoddI : Odd (Fintype.card I))
    (hoddJ : Odd (Fintype.card J))
    (hltIJ : Fintype.card I < Fintype.card J)
    (hrj0 : a r j0 = 0) :
    coefficientNonzeroCount a = Fintype.card I ∧
      ∀ i q, a i q = if q = s then a r s else 0 := by
  have hs_nonzero : ∀ i, a i s ≠ 0 := by
    intro i
    by_cases hir : i = r
    · simpa [hir] using hbase
    · intro his
      exact pf38_cross_zero_contradiction a r i s j0 hir hj0s
        hrect hbase his hrj0 hcount hoddI hoddJ hltIJ
  have hcolzero : ∀ q, q ≠ s → a r q = 0 := by
    intro q hqs
    by_cases hq0 : q = j0
    · simpa [hq0] using hrj0
    · by_contra hrq
      have hq_nonzero : ∀ i, a i q ≠ 0 := by
        intro i
        by_cases hir : i = r
        · simpa [hir] using hrq
        · intro hiq
          exact pf38_cross_zero_contradiction a r i q j0 hir
            (by intro hqj; exact hq0 hqj.symm)
            hrect hrq hiq hrj0 hcount hoddI hoddJ hltIJ
      have htwo :
          2 * Fintype.card I ≤ coefficientNonzeroCount a := by
        exact coefficientNonzeroCount_ge_two_card_left_of_two_nonzero_columns
          a s q hqs hs_nonzero hq_nonzero
      omega
  have hintzero : ∀ i q, i ≠ r → q ≠ s → a i q = 0 := by
    intro i q hir hqs
    by_contra hiq
    have hrow_full : ∀ t, t ≠ s → a i t ≠ 0 := by
      intro t hts
      by_cases htq : t = q
      · simpa [htq] using hiq
      · intro hit
        exact pf38_cross_zero_contradiction a i r q t
          (by intro h; exact hir h.symm) htq
          hrect hiq (hcolzero q hqs) hit hcount hoddI hoddJ hltIJ
    have hmix :
        Fintype.card I + (Fintype.card J - 1) ≤ coefficientNonzeroCount a := by
      exact coefficientNonzeroCount_ge_card_left_add_card_right_sub_one_of_nonzero_column_row_off
        a i s q hqs hs_nonzero hrow_full
    omega
  have hshape := coefficients_eq_single_column_indicator
    a r s hrect hbase j0 hj0s hcolzero hintzero
  have hcount_eq :=
    coefficientNonzeroCount_eq_card_left_of_single_column a (a r s) s hbase hshape
  exact ⟨hcount_eq, hshape⟩

private theorem pf38_local_single_row
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (r : I) (s : J)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hbase : a r s ≠ 0)
    (hcount : coefficientNonzeroCount a < 2 * Fintype.card I)
    (hoddI : Odd (Fintype.card I))
    (hoddJ : Odd (Fintype.card J))
    (hltIJ : Fintype.card I < Fintype.card J)
    (hcardI3 : 3 ≤ Fintype.card I)
    (hrowfull : ∀ j, a r j ≠ 0) :
    coefficientNonzeroCount a = Fintype.card J ∧
      ∀ p j, a p j = if p = r then a r s else 0 := by
  have hintzero : ∀ i j, i ≠ r → j ≠ s → a i j = 0 := by
    intro i j hir hjs
    by_contra hij
    have hrow_i_full : ∀ t, a i t ≠ 0 := by
      intro t
      by_cases htj : t = j
      · simpa [htj] using hij
      · intro hit
        rcases pf38_local_single_column a i j t htj hrect hij
            hcount hoddI hoddJ hltIJ hit with
          ⟨_hcount_col, hshape_col⟩
        have hsj : s ≠ j := by
          intro hsj'
          exact hjs hsj'.symm
        have hrs : a r s = 0 := by
          simpa [hsj] using hshape_col r s
        exact hbase hrs
    have htwo :
        2 * Fintype.card J ≤ coefficientNonzeroCount a := by
      exact coefficientNonzeroCount_ge_two_card_right_of_two_nonzero_rows
        a r i hir hrowfull hrow_i_full
    omega
  have hrowzero : ∀ i, i ≠ r → a i s = 0 := by
    intro i hir
    by_contra his
    have hJgt1 : 1 < Fintype.card J := by
      omega
    obtain ⟨j, hjs⟩ := Fintype.exists_ne_of_one_lt_card hJgt1 s
    have hij0 : a i j = 0 := hintzero i j hir hjs
    rcases pf38_local_single_column a i s j hjs hrect his
        hcount hoddI hoddJ hltIJ hij0 with
      ⟨_hcount_col, hshape_col⟩
    have hrj0 : a r j = 0 := by
      simpa [hjs] using hshape_col r j
    exact hrowfull j hrj0
  have hIgt1 : 1 < Fintype.card I := by
    omega
  obtain ⟨i', hi'r⟩ := Fintype.exists_ne_of_one_lt_card hIgt1 r
  have hshape := coefficients_eq_single_row_indicator
    a r s hrect hbase i' hi'r hrowzero hintzero
  have hcount_eq :=
    coefficientNonzeroCount_eq_card_right_of_single_row a (a r s) r hbase hshape
  exact ⟨hcount_eq, hshape⟩

/-- Pure coefficient-matrix form of PF `(3.8)`: a nonzero rectangle matrix
with fewer than `2 * |I|` nonzero entries and `|I| < |J|` is either supported
on one column or supported on one row. -/
public theorem coefficient_rectangle_small_shape
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hcount : coefficientNonzeroCount a < 2 * Fintype.card I)
    (hoddI : Odd (Fintype.card I))
    (hoddJ : Odd (Fintype.card J))
    (hltIJ : Fintype.card I < Fintype.card J)
    (hcardI3 : 3 ≤ Fintype.card I) :
    (∀ i j, a i j = 0) ∨
      (∃ c : ℂ, c ≠ 0 ∧ ∃ j : J,
        ∀ i q, a i q = if q = j then c else 0) ∨
      (∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
        ∀ p j, a p j = if p = i then c else 0) := by
  classical
  by_cases hzero : coefficientNonzeroCount a = 0
  · exact Or.inl ((coefficientNonzeroCount_eq_zero_iff a).mp hzero)
  have hpos : 0 < coefficientNonzeroCount a := Nat.pos_of_ne_zero hzero
  rcases exists_nonzero_coefficient_of_positive_count a hpos with ⟨p, hp⟩
  by_cases hzero_row : ∃ j : J, j ≠ p.2 ∧ a p.1 j = 0
  · rcases hzero_row with ⟨j, hj, hpj⟩
    rcases pf38_local_single_column a p.1 p.2 j hj hrect hp
        hcount hoddI hoddJ hltIJ hpj with
      ⟨_hcount_eq, hshape⟩
    exact Or.inr <| Or.inl ⟨a p.1 p.2, hp, p.2, hshape⟩
  · have hrowfull : ∀ j, a p.1 j ≠ 0 := by
      intro j
      by_cases hj : j = p.2
      · simpa [hj] using hp
      · intro hpj
        exact hzero_row ⟨j, hj, hpj⟩
    rcases pf38_local_single_row a p.1 p.2 hrect hp
        hcount hoddI hoddJ hltIJ hcardI3 hrowfull with
      ⟨_hcount_eq, hshape⟩
    exact Or.inr <| Or.inr ⟨a p.1 p.2, hp, p.1, hshape⟩

public theorem proposition_3_8_strong_of_rectangle
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hψ : ψ = (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) + β)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j) :
    Nat.card W1 < Nat.card W2 →
      coefficientNonzeroCount a < 2 * Nat.card W1 →
        ψ = β ∨
          (coefficientNonzeroCount a = Nat.card W1 ∧
            ∃ c : ℂ, c ≠ 0 ∧ ∃ j : J,
              ψ = c • (∑ i : I, σ (ω i j)) + β) ∨
          (coefficientNonzeroCount a = Nat.card W2 ∧
            ∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
              ψ = c • (∑ j : J, σ (ω i j)) + β) := by
  intro hlt hcount
  by_cases hzero : coefficientNonzeroCount a = 0
  · have ha : ∀ i j, a i j = 0 :=
      (coefficientNonzeroCount_eq_zero_iff a).mp hzero
    refine Or.inl ?_
    rw [hψ]
    simp [ha]
  · have hpos : 0 < coefficientNonzeroCount a := Nat.pos_of_ne_zero hzero
    rcases exists_nonzero_coefficient_of_positive_count a hpos with ⟨p, hp⟩
    have hcount' : coefficientNonzeroCount a < 2 * Fintype.card I := by
      simpa [hω.card_left] using hcount
    have hoddI : Odd (Fintype.card I) := by
      rw [hω.card_left]
      exact odd_natCard_left_of_hypothesis_3_1 h
    have hoddJ : Odd (Fintype.card J) := by
      rw [hω.card_right]
      exact odd_natCard_right_of_hypothesis_3_1 h
    have hltIJ : Fintype.card I < Fintype.card J := by
      simpa [hω.card_left, hω.card_right] using hlt
    by_cases hzero_row : ∃ j : J, j ≠ p.2 ∧ a p.1 j = 0
    · rcases hzero_row with ⟨j, hj, hpj⟩
      rcases pf38_local_single_column a p.1 p.2 j hj hrect hp
          hcount' hoddI hoddJ hltIJ hpj with
        ⟨hcount_eq, hshape⟩
      have hcountW1 : coefficientNonzeroCount a = Nat.card W1 := by
        simpa [hω.card_left] using hcount_eq
      refine Or.inr <| Or.inl <| ⟨hcountW1, ?_⟩
      refine ⟨a p.1 p.2, ?_⟩
      refine ⟨hp, ?_⟩
      refine ⟨p.2, ?_⟩
      rw [hψ]
      have hsum :
          (∑ q : I × J, a q.1 q.2 • σ (ω q.1 q.2)) =
            ∑ q : I × J,
              (if q.2 = p.2 then a p.1 p.2 else 0) • σ (ω q.1 q.2) := by
        refine Finset.sum_congr rfl ?_
        intro q _hq
        rw [hshape q.1 q.2]
      rw [hsum, sum_sigma_single_column]
    · have hrowfull : ∀ j, a p.1 j ≠ 0 := by
        intro j
        by_cases hj : j = p.2
        · simpa [hj] using hp
        · have hpj_ne : a p.1 j ≠ 0 := by
            intro hpj
            exact hzero_row ⟨j, hj, hpj⟩
          exact hpj_ne
      have hcardI3 : 3 ≤ Fintype.card I := by
        simpa [hω.card_left] using natCard_left_ge_three_of_hypothesis_3_1 h
      rcases pf38_local_single_row a p.1 p.2 hrect hp
          hcount' hoddI hoddJ hltIJ hcardI3 hrowfull with
        ⟨hcount_eq, hshape⟩
      have hcountW2 : coefficientNonzeroCount a = Nat.card W2 := by
        simpa [hω.card_right] using hcount_eq
      refine Or.inr <| Or.inr <| ⟨hcountW2, ?_⟩
      refine ⟨a p.1 p.2, ?_⟩
      refine ⟨hp, ?_⟩
      refine ⟨p.1, ?_⟩
      rw [hψ]
      have hsum :
          (∑ q : I × J, a q.1 q.2 • σ (ω q.1 q.2)) =
            ∑ q : I × J,
              (if q.1 = p.1 then a p.1 p.2 else 0) • σ (ω q.1 q.2) := by
        refine Finset.sum_congr rfl ?_
        intro q _hq
        rw [hshape q.1 q.2]
      rw [hsum, sum_sigma_single_row]

public theorem proposition_3_8_orthogonal_of_rectangle
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hβorth :
      ∀ α : Section1.ClassFunction W,
        Section1.IsClassFunction α →
          Section1.scalarProduct G β (σ α) = 0)
    (hψ : ψ = (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) + β)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hlt : Nat.card W1 < Nat.card W2)
    (hcount : coefficientNonzeroCount a < 2 * Nat.card W1)
    (hnotCol : ∀ (c : ℂ) j, ψ ≠ c • (∑ i : I, σ (ω i j)) + β)
    (hnotRow : ∀ (c : ℂ) i, ψ ≠ c • (∑ j : J, σ (ω i j)) + β) :
    ∀ i j, Section1.scalarProduct G ψ (σ (ω i j)) = 0 := by
  intro i j
  have h38 := proposition_3_8_strong_of_rectangle
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a)
    h hω hψ hrect hlt hcount
  rcases h38 with hψeq | hcol | hrow
  · rw [hψeq]
    exact hβorth (ω i j) (hω.is_class i j)
  · rcases hcol with ⟨_hcount, c, _hc, j', hshape⟩
    exact False.elim (hnotCol c j' hshape)
  · rcases hrow with ⟨_hcount, c, _hc, i', hshape⟩
    exact False.elim (hnotRow c i' hshape)

public theorem proposition_3_8_strong
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω) :
    Nat.card W1 < Nat.card W2 →
      coefficientNonzeroCount a < 2 * Nat.card W1 →
        ψ = β ∨
          (coefficientNonzeroCount a = Nat.card W1 ∧
            ∃ c : ℂ, c ≠ 0 ∧ ∃ j : J,
              ψ = c • (∑ i : I, σ (ω i j)) + β) ∨
          (coefficientNonzeroCount a = Nat.card W2 ∧
            ∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
              ψ = c • (∑ j : J, σ (ω i j)) + β) := by
  exact proposition_3_8_strong_of_rectangle
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a)
    h hω h36.2.2.1
    (proposition_3_7
      (G := G) (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a)
      h hω h36).1

public theorem proposition_3_8
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω) :
    proposition_3_8_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω h36 := by
  intro hlt hcount
  rcases proposition_3_8_strong
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a)
      h hω h36 hlt hcount with
    hψeq | hcol | hrow
  · exact Or.inl hψeq
  · rcases hcol with ⟨hcountEq, c, _hc, j, hshape⟩
    exact Or.inr <| Or.inl <| ⟨hcountEq, c, j, hshape⟩
  · rcases hrow with ⟨hcountEq, c, _hc, i, hshape⟩
    exact Or.inr <| Or.inr <| ⟨hcountEq, c, i, hshape⟩

/--
PF `(3.8)` zero-coefficient corollary used by later sections: if the
Hypothesis `(3.6)` coefficient matrix has at most two nonzero entries, then
all coefficients are zero.
-/
public theorem proposition_3_8_coefficients_zero_of_count_le_two
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω)
    (hcount_le : coefficientNonzeroCount a ≤ 2) :
    ∀ i j, a i j = 0 := by
  classical
  let aT : J → I → ℂ := fun j i => a i j
  have hcount_swap : coefficientNonzeroCount aT = coefficientNonzeroCount a := by
    simpa [aT] using coefficientNonzeroCount_swap a
  have hne : Nat.card W1 ≠ Nat.card W2 := by
    intro hEq
    have hcop := natCard_left_right_coprime_of_hypothesis_3_1 h
    rw [hEq] at hcop
    have hgt1 : 1 < Nat.card W2 := by
      have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
      have hright3 : 3 ≤ Nat.card W2 := by
        rw [← hEq]
        exact hleft3
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd hgt1 (dvd_refl _) (dvd_refl _)) hcop
  have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
  have hright3 : 3 ≤ Nat.card W2 := natCard_right_ge_three_of_hypothesis_3_1 h
  have hcount_lt_left : coefficientNonzeroCount a < 2 * Nat.card W1 := by
    omega
  have hcount_lt_right : coefficientNonzeroCount a < 2 * Nat.card W2 := by
    omega
  by_cases hlt : Nat.card W1 < Nat.card W2
  · have h38 :=
      proposition_3_8_strong
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a)
        h hω h36 hlt hcount_lt_left
    rcases h38 with hψeq | hcol | hrow
    · exact hypothesis_3_6_all_coeff_zero_of_eq_beta h36 hψeq
    · rcases hcol with ⟨hcountEq, _c, _hc, _j, _hshape⟩
      have hcontra : Nat.card W1 ≤ 2 := by omega
      have hgt : 2 < Nat.card W1 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt)
    · rcases hrow with ⟨hcountEq, _c, _hc, _i, _hshape⟩
      have hcontra : Nat.card W2 ≤ 2 := by omega
      have hgt : 2 < Nat.card W2 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt)
  · have hgt : Nat.card W2 < Nat.card W1 := by omega
    have h36swap :
        hypothesis_3_6_statement W2 W1 W J I j0 i0
          (fun j i => ω i j) σ ψ β aT
          (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω) := by
      rcases h36 with ⟨h32, hβorth, hψ, hβclass, hψclass, hvanish⟩
      refine ⟨?_, hβorth, ?_, hβclass, hψclass, ?_⟩
      · rcases h32 with ⟨hiso, hvirt, hind, hclass, hone, hagree, hvanishOut⟩
        refine ⟨hiso, hvirt, ?_, hclass, hone, ?_, ?_⟩
        · intro α hα
          exact hind α (by
            simpa [cyclicTISet_swap W1 W2 W] using hα)
        · intro α hα x hx
          exact hagree α hα x (by simpa [cyclicTISet_swap W1 W2 W] using hx)
        · intro χ hχ hnot
          have hnot' : χ ∉ classFunctionImage σ := hnot
          have hvan := hvanishOut χ hχ hnot'
          intro x hx
          exact hvan x (by simpa [cyclicTISet_swap W1 W2 W] using hx)
      · rw [hψ]
        rw [Fintype.sum_prod_type]
        congr 1
        ext g
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc
          ∑ x : I, ∑ y : J, a x y * σ (ω x y) g =
              ∑ p : I × J, a p.1 p.2 * σ (ω p.1 p.2) g := by
                exact (Fintype.sum_prod_type
                  (f := fun p : I × J => a p.1 p.2 * σ (ω p.1 p.2) g)
                  ).symm
          _ = ∑ p : J × I, a p.2 p.1 * σ (ω p.2 p.1) g := by
                refine Fintype.sum_equiv (Equiv.prodComm I J)
                  (fun p : I × J => a p.1 p.2 * σ (ω p.1 p.2) g)
                  (fun p : J × I => a p.2 p.1 * σ (ω p.2 p.1) g) ?_
                intro p
                rfl
          _ = ∑ p : J × I, aT p.1 p.2 * σ (ω p.2 p.1) g := by
                simp [aT]
      · intro x hx
        exact hvanish x (by simpa [cyclicTISet_swap W1 W2 W] using hx)
    have hswap :=
      proposition_3_8_strong
        (W1 := W2) (W2 := W1) (W := W)
        (I := J) (J := I) (i0 := j0) (j0 := i0)
        (ω := fun j i => ω i j) (σ := σ) (ψ := ψ) (β := β)
        (a := aT)
        (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
        h36swap hgt (by simpa [hcount_swap] using hcount_lt_right)
    rcases hswap with hψeq | hcol | hrow
    · have hzero_swap :
          ∀ j i, a i j = 0 :=
        hypothesis_3_6_all_coeff_zero_of_eq_beta h36swap hψeq
      intro i j
      exact hzero_swap j i
    · rcases hcol with ⟨hcountEq, _c, _hc, _j, _hshape⟩
      have hcontra : Nat.card W2 ≤ 2 := by omega
      have hgt2 : 2 < Nat.card W2 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt2)
    · rcases hrow with ⟨hcountEq, _c, _hc, _i, _hshape⟩
      have hcontra : Nat.card W1 ≤ 2 := by omega
      have hgt2 : 2 < Nat.card W1 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt2)

/--
PF `(3.8)` counting corollary in its purely combinatorial form. A coefficient
matrix satisfying the PF `(3.7)` rectangle relation cannot have a nonzero entry
when its support has size at most two.
-/
public theorem coefficients_zero_of_rectangle_count_le_two
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (a : I → J → ℂ)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hrect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j)
    (hcount_le : coefficientNonzeroCount a ≤ 2) :
    ∀ i j, a i j = 0 := by
  classical
  let aT : J → I → ℂ := fun j i => a i j
  have hcount_swap : coefficientNonzeroCount aT = coefficientNonzeroCount a := by
    simpa [aT] using coefficientNonzeroCount_swap a
  have hne : Nat.card W1 ≠ Nat.card W2 := by
    intro hEq
    have hcop := natCard_left_right_coprime_of_hypothesis_3_1 h
    rw [hEq] at hcop
    have hgt1 : 1 < Nat.card W2 := by
      have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
      have hright3 : 3 ≤ Nat.card W2 := by
        rw [← hEq]
        exact hleft3
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd hgt1 (dvd_refl _) (dvd_refl _)) hcop
  have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
  have hright3 : 3 ≤ Nat.card W2 := natCard_right_ge_three_of_hypothesis_3_1 h
  have hcount_lt_left : coefficientNonzeroCount a < 2 * Nat.card W1 := by
    omega
  have hcount_lt_right : coefficientNonzeroCount a < 2 * Nat.card W2 := by
    omega
  by_cases hzero : coefficientNonzeroCount a = 0
  · exact (coefficientNonzeroCount_eq_zero_iff a).1 hzero
  have hpos : 0 < coefficientNonzeroCount a := Nat.pos_of_ne_zero hzero
  by_cases hlt : Nat.card W1 < Nat.card W2
  · rcases exists_nonzero_coefficient_of_positive_count a hpos with ⟨p, hp⟩
    have hcount' : coefficientNonzeroCount a < 2 * Fintype.card I := by
      simpa [hω.card_left] using hcount_lt_left
    have hoddI : Odd (Fintype.card I) := by
      rw [hω.card_left]
      exact odd_natCard_left_of_hypothesis_3_1 h
    have hoddJ : Odd (Fintype.card J) := by
      rw [hω.card_right]
      exact odd_natCard_right_of_hypothesis_3_1 h
    have hltIJ : Fintype.card I < Fintype.card J := by
      simpa [hω.card_left, hω.card_right] using hlt
    by_cases hzero_row : ∃ j : J, j ≠ p.2 ∧ a p.1 j = 0
    · rcases hzero_row with ⟨j, hj, hpj⟩
      rcases pf38_local_single_column a p.1 p.2 j hj hrect hp
          hcount' hoddI hoddJ hltIJ hpj with
        ⟨hcount_eq, _hshape⟩
      have hcontra : Nat.card W1 ≤ 2 := by
        rw [← hω.card_left, ← hcount_eq]
        exact hcount_le
      have hgt : 2 < Nat.card W1 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt)
    · have hrowfull : ∀ j, a p.1 j ≠ 0 := by
        intro j
        by_cases hj : j = p.2
        · simpa [hj] using hp
        · intro hpj
          exact hzero_row ⟨j, hj, hpj⟩
      have hcardI3 : 3 ≤ Fintype.card I := by
        simpa [hω.card_left] using hleft3
      rcases pf38_local_single_row a p.1 p.2 hrect hp
          hcount' hoddI hoddJ hltIJ hcardI3 hrowfull with
        ⟨hcount_eq, _hshape⟩
      have hcontra : Nat.card W2 ≤ 2 := by
        rw [← hω.card_right, ← hcount_eq]
        exact hcount_le
      have hgt : 2 < Nat.card W2 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt)
  · have hgt : Nat.card W2 < Nat.card W1 := by omega
    have hposT : 0 < coefficientNonzeroCount aT := by
      simpa [hcount_swap] using hpos
    rcases exists_nonzero_coefficient_of_positive_count aT hposT with ⟨p, hp⟩
    have hcountT_le : coefficientNonzeroCount aT ≤ 2 := by
      simpa [hcount_swap] using hcount_le
    have hrectT : ∀ j j' i i', aT j i + aT j' i' = aT j i' + aT j' i := by
      intro j j' i i'
      simpa [aT, add_comm] using hrect i i' j j'
    have hcountT' : coefficientNonzeroCount aT < 2 * Fintype.card J := by
      simpa [hcount_swap, hω.card_right] using hcount_lt_right
    have hoddJ : Odd (Fintype.card J) := by
      rw [hω.card_right]
      exact odd_natCard_right_of_hypothesis_3_1 h
    have hoddI : Odd (Fintype.card I) := by
      rw [hω.card_left]
      exact odd_natCard_left_of_hypothesis_3_1 h
    have hltJI : Fintype.card J < Fintype.card I := by
      simpa [hω.card_left, hω.card_right] using hgt
    by_cases hzero_row : ∃ i : I, i ≠ p.2 ∧ aT p.1 i = 0
    · rcases hzero_row with ⟨i, hi, hpi⟩
      rcases pf38_local_single_column aT p.1 p.2 i hi hrectT hp
          hcountT' hoddJ hoddI hltJI hpi with
        ⟨hcount_eq, _hshape⟩
      have hcontra : Nat.card W2 ≤ 2 := by
        rw [← hω.card_right, ← hcount_eq]
        exact hcountT_le
      have hgt2 : 2 < Nat.card W2 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt2)
    · have hrowfull : ∀ i, aT p.1 i ≠ 0 := by
        intro i
        by_cases hi : i = p.2
        · simpa [hi] using hp
        · intro hpi
          exact hzero_row ⟨i, hi, hpi⟩
      have hcardJ3 : 3 ≤ Fintype.card J := by
        simpa [hω.card_right] using hright3
      rcases pf38_local_single_row aT p.1 p.2 hrectT hp
          hcountT' hoddJ hoddI hltJI hcardJ3 hrowfull with
        ⟨hcount_eq, _hshape⟩
      have hcontra : Nat.card W1 ≤ 2 := by
        rw [← hω.card_left, ← hcount_eq]
        exact hcountT_le
      have hgt2 : 2 < Nat.card W1 := by omega
      exact False.elim ((not_lt_of_ge hcontra) hgt2)

end Section3
