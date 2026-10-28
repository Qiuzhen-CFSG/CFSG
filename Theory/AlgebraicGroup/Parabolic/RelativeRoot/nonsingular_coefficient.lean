module

public import Theory.AlgebraicGroup.RootData.ChevalleyClassification
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.Setup
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.Variety.Defs
public import Theory.AlgebraicGroup.Basic
public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.RootSystems.Dynkin

set_option warningAsError false

/-!
This module supplies the coefficient-nonvanishing bridge used by the
relative-root commutator series.  A Dynkin witness is first reduced to either
an irreducible connected table, where the existing Chevalley classification
theorem applies, or to one of the diagonal tables representing invalid ranks.
In the latter case, diagonal root arithmetic excludes the exceptional
coefficient patterns directly (including the short/long `3,2` pattern), so
the nonsingular-characteristic coefficient theorem still applies.  The
rank-one tables are treated as connected singletons; the source Dynkin tables
are the provenance for the valid-rank split.  The resulting irreducible-or-
diagonal dichotomy and the root description for a diagonal base are exported
for later relative-root arguments that must handle invalid-rank tables
explicitly.
-/

namespace Theory.AlgebraicGroup

variable {ι X Y : Type*} [Finite ι]
  [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]

/-- For a base with diagonal Cartan matrix, every root is a signed base root. -/
public lemma diagonal_base_root_eq_or_neg
    (P : RootPairing ι ℚ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ i j : b.support, i ≠ j → b.cartanMatrix i j = 0) :
    ∀ x, ∃ j : b.support,
      P.root x = P.root j ∨ P.root x = -P.root j := by
  intro x
  apply b.induction_reflect x
  · intro i hi
    obtain ⟨j, hroot⟩ := hi
    rcases hroot with hroot | hroot
    · refine ⟨j, Or.inr ?_⟩
      rw [P.root_reflectionPerm]
      rw [← hroot]
      exact P.reflection_apply_self i
    · refine ⟨j, Or.inl ?_⟩
      rw [P.root_reflectionPerm]
      have hroot' : P.root j = - P.root i := by rw [hroot]; simp
      rw [hroot']
      exact P.reflection_apply_self i
  · intro i hi
    exact ⟨⟨i, hi⟩, Or.inl rfl⟩
  · intro i j hi hj
    obtain ⟨s, hroot⟩ := hi
    rcases hroot with hroot | hroot
    · have hs := s.property
      let t : b.support := ⟨j, hj⟩
      by_cases hsj : s = t
      · have hsj' : (s : ι) = j := congrArg Subtype.val hsj
        subst j
        refine ⟨s, Or.inr ?_⟩
        rw [P.root_reflectionPerm, hroot]
        exact P.reflection_apply_self s
      · have hz : P.pairingIn ℤ s j = 0 := by
          change b.cartanMatrixIn ℤ s t = 0
          exact hdiag s t hsj
        refine ⟨s, Or.inl ?_⟩
        rw [P.root_reflectionPerm, hroot, P.reflection_apply_root' ℤ, hz]
        simp
    · have hs := s.property
      let t : b.support := ⟨j, hj⟩
      by_cases hsj : s = t
      · have hsj' : (s : ι) = j := congrArg Subtype.val hsj
        subst j
        refine ⟨s, Or.inl ?_⟩
        rw [P.root_reflectionPerm, hroot, map_neg]
        rw [P.reflection_apply_self]
        simp
      · have hz : P.pairingIn ℤ s j = 0 := by
          change b.cartanMatrixIn ℤ s t = 0
          exact hdiag s t hsj
        refine ⟨s, Or.inr ?_⟩
        rw [P.root_reflectionPerm, hroot, map_neg, P.reflection_apply_root' ℤ, hz]
        simp

private lemma fin_path_connected
    (n : ℕ) (edge : Fin n → Fin n → Prop) (hn : 0 < n)
    (hstep : ∀ i : Fin n, ∀ h : i.val + 1 < n,
      edge i ⟨i.val + 1, h⟩ ∧ edge ⟨i.val + 1, h⟩ i) :
    ∀ i j : Fin n, Relation.ReflTransGen edge i j := by
  cases n with
  | zero => omega
  | succ n =>
    intro i j
    have hto : ∀ i : Fin (n + 1),
        Relation.ReflTransGen edge i (0 : Fin (n + 1)) := by
      intro i
      induction i using Fin.induction with
      | zero => exact .refl
      | succ i hi =>
          have hbound : i.castSucc.val + 1 < n + 1 := by
            simpa using Nat.succ_lt_succ i.isLt
          apply Relation.ReflTransGen.head (hstep i.castSucc hbound |>.2)
          exact hi
    have hfrom : ∀ j : Fin (n + 1),
        Relation.ReflTransGen edge (0 : Fin (n + 1)) j := by
      intro j
      induction j using Fin.induction with
      | zero => exact .refl
      | succ j hj =>
          have hbound : j.castSucc.val + 1 < n + 1 := by
            simpa using Nat.succ_lt_succ j.isLt
          apply Relation.ReflTransGen.tail hj
          exact hstep j.castSucc hbound |>.1
    exact hto i |>.trans (hfrom j)

private lemma reflTransGen_reverse_of_symmetric
    {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.head (hsymm _ _ hyz) ih

private lemma dynkin_connected_A (n : ℕ) (hn : 0 < n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.A, n⟩ u v ≠ 0) i j := by
  refine fin_path_connected n (fun u v => dynkinCartanEntry ⟨.A, n⟩ u v ≠ 0) ?_ ?_
  · exact hn
  · intro i hi
    let j : Fin n := ⟨i.val + 1, hi⟩
    have hne : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [j] at this
    have hne' : j ≠ i := Ne.symm hne
    constructor <;> simp [dynkinCartanEntry, j, hne, hne'] <;>
      split_ifs <;> norm_num

private lemma dynkin_connected_B (n : ℕ) (hn : 1 < n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.B, n⟩ u v ≠ 0) i j := by
  refine fin_path_connected n (fun u v => dynkinCartanEntry ⟨.B, n⟩ u v ≠ 0) (by omega) ?_
  intro i hi
  let j : Fin n := ⟨i.val + 1, hi⟩
  have hne : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
  have hne' : j ≠ i := Ne.symm hne
  constructor <;> simp [dynkinCartanEntry, j, hne, hne'] <;>
    split_ifs <;> norm_num

private lemma dynkin_connected_C (n : ℕ) (hn : 1 < n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.C, n⟩ u v ≠ 0) i j := by
  refine fin_path_connected n (fun u v => dynkinCartanEntry ⟨.C, n⟩ u v ≠ 0) (by omega) ?_
  intro i hi
  let j : Fin n := ⟨i.val + 1, hi⟩
  have hne : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
  have hne' : j ≠ i := Ne.symm hne
  constructor <;> simp [dynkinCartanEntry, j, hne, hne'] <;>
    split_ifs <;> norm_num

private lemma dynkin_connected_D (n : ℕ) (hn : 2 < n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.D, n⟩ u v ≠ 0) i j := by
  let edge : Fin n → Fin n → Prop :=
    fun u v => dynkinCartanEntry ⟨.D, n⟩ u v ≠ 0
  let center : Fin n := ⟨n - 3, by omega⟩
  let zero : Fin n := ⟨0, by omega⟩
  have hto_aux : ∀ m, m < n → ∀ i : Fin n, i.val = m →
      Relation.ReflTransGen edge i zero := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn i hi
      have hi' : i = ⟨m, hmn⟩ := Fin.ext hi
      subst i
      by_cases hzero : m = 0
      · subst m
        have hz : (⟨0, hmn⟩ : Fin n) = zero := by
          apply Fin.ext
          rfl
        rw [hz]
        done
      have hmpos : 0 < m := by omega
      by_cases hfork : m + 2 = n
      · have hed : edge (⟨m, hmn⟩ : Fin n) center := by
          dsimp [edge, center]
          simp only [dynkinCartanEntry]
          split_ifs <;> norm_num <;> omega
        have hcval : center.val = n - 3 := by rfl
        exact Relation.ReflTransGen.head hed (ih (m := n - 3) (by omega) (by omega)
          center hcval)
      by_cases hlast : m + 1 = n
      · have hed : edge (⟨m, hmn⟩ : Fin n) center := by
          dsimp [edge, center]
          simp only [dynkinCartanEntry]
          split_ifs <;> norm_num <;> omega
        have hcval : center.val = n - 3 := by rfl
        exact Relation.ReflTransGen.head hed (ih (m := n - 3) (by omega) (by omega)
          center hcval)
      · let prev : Fin n := ⟨m - 1, by omega⟩
        have hprev : prev.val < m := by dsimp [prev]; omega
        have hed : edge (⟨m, hmn⟩ : Fin n) prev := by
          dsimp [edge, prev]
          simp only [dynkinCartanEntry]
          split_ifs <;> norm_num <;> omega
        exact Relation.ReflTransGen.head hed (ih (m := m - 1) hprev (by omega) prev (by
          rfl))
  have hto : ∀ i : Fin n, Relation.ReflTransGen edge i zero := by
    intro i
    exact hto_aux i.val i.isLt i rfl
  have hsymm : ∀ a b, edge a b → edge b a := by
    intro a b hab
    dsimp [edge] at hab ⊢
    simpa only [dynkinCartanEntry_D_symmetric_any_rank n a b] using hab
  intro i j
  exact hto i |>.trans
    (reflTransGen_reverse_of_symmetric hsymm (hto j))

private lemma dynkin_connected_F4 :
    ∀ i j : Fin 4,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.F4, 4⟩ u v ≠ 0) i j := by
  refine fin_path_connected 4 (fun u v => dynkinCartanEntry ⟨.F4, 4⟩ u v ≠ 0)
    (by norm_num) ?_
  intro i hi
  fin_cases i
  · norm_num [dynkinCartanEntry, Fin.ext_iff] at *
  · norm_num [dynkinCartanEntry, Fin.ext_iff] at *
  · norm_num [dynkinCartanEntry, Fin.ext_iff] at *
  · norm_num at hi

private lemma dynkin_connected_G2 :
    ∀ i j : Fin 2,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.G2, 2⟩ u v ≠ 0) i j := by
  refine fin_path_connected 2 (fun u v => dynkinCartanEntry ⟨.G2, 2⟩ u v ≠ 0)
    (by norm_num) ?_
  intro i hi
  fin_cases i
  · norm_num [dynkinCartanEntry, Fin.ext_iff] at *
  · norm_num at hi

private lemma dynkin_connected_E6 :
    ∀ i j : Fin 6,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.E6, 6⟩ u v ≠ 0) i j := by
  let edge : Fin 6 → Fin 6 → Prop :=
    fun u v => dynkinCartanEntry ⟨.E6, 6⟩ u v ≠ 0
  have h10 : edge 1 0 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h21 : edge 2 1 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h32 : edge 3 2 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h42 : edge 4 2 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h54 : edge 5 4 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have hto : ∀ i : Fin 6, Relation.ReflTransGen edge i (0 : Fin 6) := by
    intro i
    fin_cases i
    · exact .refl
    · exact .head h10 (.refl)
    · exact .head h21 (.head h10 (.refl))
    · exact .head h32 (.head h21 (.head h10 (.refl)))
    · exact .head h42 (.head h21 (.head h10 (.refl)))
    · exact .head h54 (.head h42 (.head h21 (.head h10 (.refl))))
  have hsymm : ∀ a b, edge a b → edge b a := by
    intro a b hab
    dsimp [edge] at hab ⊢
    simpa only [dynkinCartanEntry_E6_symmetric_any_rank 6 a b] using hab
  intro i j
  exact hto i |>.trans
    (reflTransGen_reverse_of_symmetric hsymm (hto j))

private lemma dynkin_connected_E7 :
    ∀ i j : Fin 7,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.E7, 7⟩ u v ≠ 0) i j := by
  let edge : Fin 7 → Fin 7 → Prop :=
    fun u v => dynkinCartanEntry ⟨.E7, 7⟩ u v ≠ 0
  have h10 : edge 1 0 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h21 : edge 2 1 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h32 : edge 3 2 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h42 : edge 4 2 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h54 : edge 5 4 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h65 : edge 6 5 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have hto : ∀ i : Fin 7, Relation.ReflTransGen edge i (0 : Fin 7) := by
    intro i
    fin_cases i
    · exact .refl
    · exact .head h10 (.refl)
    · exact .head h21 (.head h10 (.refl))
    · exact .head h32 (.head h21 (.head h10 (.refl)))
    · exact .head h42 (.head h21 (.head h10 (.refl)))
    · exact .head h54 (.head h42 (.head h21 (.head h10 (.refl))))
    · exact .head h65 (.head h54 (.head h42 (.head h21 (.head h10 (.refl)))))
  have hsymm : ∀ a b, edge a b → edge b a := by
    intro a b hab
    dsimp [edge] at hab ⊢
    simpa only [dynkinCartanEntry_E7_symmetric_any_rank 7 a b] using hab
  intro i j
  exact hto i |>.trans
    (reflTransGen_reverse_of_symmetric hsymm (hto j))

private lemma dynkin_connected_E8 :
    ∀ i j : Fin 8,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨.E8, 8⟩ u v ≠ 0) i j := by
  let edge : Fin 8 → Fin 8 → Prop :=
    fun u v => dynkinCartanEntry ⟨.E8, 8⟩ u v ≠ 0
  have h10 : edge 1 0 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h21 : edge 2 1 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h32 : edge 3 2 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h42 : edge 4 2 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h54 : edge 5 4 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h65 : edge 6 5 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have h76 : edge 7 6 := by norm_num [edge, dynkinCartanEntry] <;> split_ifs <;> norm_num
  have hto : ∀ i : Fin 8, Relation.ReflTransGen edge i (0 : Fin 8) := by
    intro i
    fin_cases i
    · exact .refl
    · exact .head h10 (.refl)
    · exact .head h21 (.head h10 (.refl))
    · exact .head h32 (.head h21 (.head h10 (.refl)))
    · exact .head h42 (.head h21 (.head h10 (.refl)))
    · exact .head h54 (.head h42 (.head h21 (.head h10 (.refl))))
    · exact .head h65 (.head h54 (.head h42 (.head h21 (.head h10 (.refl)))))
    · exact .head h76 (.head h65 (.head h54 (.head h42 (.head h21 (.head h10 (.refl))))))
  have hsymm : ∀ a b, edge a b → edge b a := by
    intro a b hab
    dsimp [edge] at hab ⊢
    simpa only [dynkinCartanEntry_E8_symmetric_any_rank 8 a b] using hab
  intro i j
  exact hto i |>.trans
    (reflTransGen_reverse_of_symmetric hsymm (hto j))

private lemma dynkin_connected_singleton (kind : DynkinType) :
    ∀ i j : Fin 1,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry ⟨kind, 1⟩ u v ≠ 0) i j := by
  intro i j
  fin_cases i <;> fin_cases j
  exact .refl

private lemma dynkin_diagonal_D2 :
    ∀ i j : Fin 2, i ≠ j → dynkinCartanEntry ⟨.D, 2⟩ i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [dynkinCartanEntry]

private lemma dynkin_diagonal_E6_invalid (n : ℕ) (hn : n ≠ 6) :
    ∀ i j : Fin n, i ≠ j → dynkinCartanEntry ⟨.E6, n⟩ i j = 0 := by
  intro i j hij
  simp [dynkinCartanEntry, hn, hij]

private lemma dynkin_diagonal_E7_invalid (n : ℕ) (hn : n ≠ 7) :
    ∀ i j : Fin n, i ≠ j → dynkinCartanEntry ⟨.E7, n⟩ i j = 0 := by
  intro i j hij
  simp [dynkinCartanEntry, hn, hij]

private lemma dynkin_diagonal_E8_invalid (n : ℕ) (hn : n ≠ 8) :
    ∀ i j : Fin n, i ≠ j → dynkinCartanEntry ⟨.E8, n⟩ i j = 0 := by
  intro i j hij
  simp [dynkinCartanEntry, hn, hij]

private lemma dynkin_diagonal_F4_invalid (n : ℕ) (hn : n ≠ 4) :
    ∀ i j : Fin n, i ≠ j → dynkinCartanEntry ⟨.F4, n⟩ i j = 0 := by
  intro i j hij
  simp [dynkinCartanEntry, hn, hij]

private lemma dynkin_diagonal_G2_invalid (n : ℕ) (hn : n ≠ 2) :
    ∀ i j : Fin n, i ≠ j → dynkinCartanEntry ⟨.G2, n⟩ i j = 0 := by
  intro i j hij
  simp [dynkinCartanEntry, hn, hij]

private lemma diagonal_base_of_hType
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (C : RootClassification) (hType : HasDynkinType P C)
    (hTable : ∀ i j : Fin C.rank, i ≠ j → dynkinCartanEntry C i j = 0) :
    ∃ b : P.Base, ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0 := by
  rcases hType with ⟨b, e, hbe⟩
  refine ⟨b, ?_⟩
  intro s t hst
  change b.cartanMatrixIn ℤ s t = 0
  rw [hbe]
  apply hTable
  intro h
  apply hst
  exact e.injective h

private lemma pair_coeff_zero
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) {s t : b.support} (hst : s ≠ t)
    (a d : ℚ) (h : a • P.root s + d • P.root t = 0) :
    a = 0 ∧ d = 0 := by
  let l : b.support →₀ ℚ := Finsupp.single s a + Finsupp.single t d
  have hl : (Finsupp.linearCombination ℚ (fun z : b.support => P.root z)) l = 0 := by
    dsimp [l]
    simp only [map_add, Finsupp.linearCombination_single]
    simpa [smul_add, add_smul] using h
  have hl0 : l = 0 := b.linearIndepOn_root.linearIndependent (by simpa [hl])
  have hs := congrArg (fun z => z s) hl0
  have ht := congrArg (fun z => z t) hl0
  constructor
  · simpa [l, hst] using hs
  · simpa [l, hst] using ht

private lemma triple_coeff_zero
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (s t u : b.support) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (a d e : ℚ) (h : a • P.root s + d • P.root t + e • P.root u = 0) :
    a = 0 ∧ d = 0 ∧ e = 0 := by
  let l : b.support →₀ ℚ := Finsupp.single s a + Finsupp.single t d + Finsupp.single u e
  have hl : (Finsupp.linearCombination ℚ (fun z : b.support => P.root z)) l = 0 := by
    dsimp [l]
    simp only [map_add, Finsupp.linearCombination_single]
    simpa [smul_add, add_smul, add_assoc] using h
  have hl0 : l = 0 := b.linearIndepOn_root.linearIndependent (by simpa [hl])
  have hs := congrArg (fun z => z s) hl0
  have ht := congrArg (fun z => z t) hl0
  have hu := congrArg (fun z => z u) hl0
  refine ⟨?_, ?_, ?_⟩
  · simpa [l, hst, hsu] using hs
  · simpa [l, hst, htu] using ht
  · simpa [l, hsu, htu] using hu

private lemma diagonal_normalized_combination_false
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    (s t u : b.support) (c a d : ℚ)
    (hc : c ≠ a + d ∨ s ≠ t ∨ u ≠ s) (hc0 : c ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0)
    (h : c • P.root u = a • P.root s + d • P.root t) : False := by
  have hrel : c • P.root u - a • P.root s - d • P.root t = 0 := by
    rw [h]
    module
  by_cases hst : s = t
  · subst t
    by_cases hus : u = s
    · subst u
      have hs : c = a + d := by
        apply smul_left_injective ℚ (P.ne_zero s)
        calc
          c • P.root s = a • P.root s + d • P.root s := by
            apply eq_of_sub_eq_zero
            simpa [sub_eq_add_neg, add_smul, add_assoc, add_comm] using hrel
          _ = (a + d) • P.root s := by module
      rcases hc with hc | hst | hus
      · exact hc hs
      · exact hst rfl
      · exact hus rfl
    · have hpEq : (-(a + d)) • P.root s + c • P.root u = 0 := by
        calc
          (-(a + d)) • P.root s + c • P.root u =
              c • P.root u - a • P.root s - d • P.root s := by module
          _ = 0 := hrel
      have hp := pair_coeff_zero b (Ne.symm hus) (-(a + d)) c hpEq
      exact hc0 (by simpa using hp.2)
  · by_cases hus : u = s
    · subst u
      have hpEq : (c - a) • P.root s + (-d) • P.root t = 0 := by
        calc
          (c - a) • P.root s + (-d) • P.root t =
              c • P.root s - a • P.root s - d • P.root t := by module
          _ = 0 := hrel
      have hp := pair_coeff_zero b hst (c - a) (-d) hpEq
      exact hd (by simpa using hp.2)
    · by_cases hut : u = t
      · subst u
        have hpEq : (-a) • P.root s + (c - d) • P.root t = 0 := by
          calc
            (-a) • P.root s + (c - d) • P.root t =
                c • P.root t - a • P.root s - d • P.root t := by module
            _ = 0 := hrel
        have hp := pair_coeff_zero b hst (-a) (c - d) hpEq
        exact ha (by simpa using hp.1)
      · have htriEq : (-a) • P.root s + (-d) • P.root t + c • P.root u = 0 := by
          calc
            (-a) • P.root s + (-d) • P.root t + c • P.root u =
                c • P.root u - a • P.root s - d • P.root t := by module
            _ = 0 := hrel
        have htri := triple_coeff_zero b s t u hst (Ne.symm hus) (Ne.symm hut)
          (-a) (-d) c htriEq
        exact hc0 (by simpa using htri.2.2)

private lemma diagonal_root_sum_false
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    {i j γ : ι} (hγ : P.root γ = P.root i + P.root j) : False := by
  obtain ⟨si, hsi⟩ := diagonal_base_root_eq_or_neg P b hdiag i
  obtain ⟨sj, hsj⟩ := diagonal_base_root_eq_or_neg P b hdiag j
  obtain ⟨sg, hsg⟩ := diagonal_base_root_eq_or_neg P b hdiag γ
  rcases hsi with hsi | hsi <;> rcases hsj with hsj | hsj <;>
    rcases hsg with hsg | hsg
  all_goals
    first
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 1 1 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) 1 1 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 1 (-1) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) 1 (-1) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 (-1) 1 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) (-1) 1 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 (-1) (-1) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) (-1) (-1) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by simpa [hsi, hsj, hsg] using hγ)

private lemma diagonal_special_weighted_false_pos
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    {i j : ι} (hnotop : P.root i ≠ -P.root j)
    {s t u : b.support} (hsi : P.root i = P.root s)
    (hsj : P.root j = -P.root t)
    (h : (1 : ℚ) • P.root u = (3 : ℚ) • P.root s + (-2 : ℚ) • P.root t) : False := by
  by_cases hst : s = t
  · by_cases hus : u = s
    · apply hnotop
      simpa [hsi, hsj, hst]
    · exact diagonal_normalized_combination_false b hdiag s t u 1 3 (-2)
        (Or.inr (Or.inr hus)) (by norm_num) (by norm_num) (by norm_num) h
  · exact diagonal_normalized_combination_false b hdiag s t u 1 3 (-2)
      (Or.inr (Or.inl hst)) (by norm_num) (by norm_num) (by norm_num) h

private lemma diagonal_special_weighted_false_neg
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    {i j : ι} (hnotop : P.root i ≠ -P.root j)
    {s t u : b.support} (hsi : P.root i = -P.root s)
    (hsj : P.root j = P.root t)
    (h : (-1 : ℚ) • P.root u = (-3 : ℚ) • P.root s + (2 : ℚ) • P.root t) : False := by
  by_cases hst : s = t
  · by_cases hus : u = s
    · apply hnotop
      simpa [hsi, hsj, hst]
    · exact diagonal_normalized_combination_false b hdiag s t u (-1) (-3) 2
        (Or.inr (Or.inr hus)) (by norm_num) (by norm_num) (by norm_num) h
  · exact diagonal_normalized_combination_false b hdiag s t u (-1) (-3) 2
      (Or.inr (Or.inl hst)) (by norm_num) (by norm_num) (by norm_num) h

private lemma diagonal_weighted_root_false
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    {i j γ : ι} (hnotop : P.root i ≠ -P.root j)
    (hroot : P.root γ = (3 : ℚ) • P.root i + (2 : ℚ) • P.root j) : False := by
  obtain ⟨si, hsi⟩ := diagonal_base_root_eq_or_neg P b hdiag i
  obtain ⟨sj, hsj⟩ := diagonal_base_root_eq_or_neg P b hdiag j
  obtain ⟨sg, hsg⟩ := diagonal_base_root_eq_or_neg P b hdiag γ
  rcases hsi with hsi | hsi <;> rcases hsj with hsj | hsj <;>
    rcases hsg with hsg | hsg
  all_goals
    first
    | exact diagonal_special_weighted_false_pos b hdiag hnotop hsi hsj
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_special_weighted_false_neg b hdiag hnotop hsi hsj
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 3 2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) 3 2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) 3 (-2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 (-3) 2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_normalized_combination_false b hdiag si sj sg 1 (-3) (-2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa [hsi, hsj, hsg] using hroot)
    | exact diagonal_normalized_combination_false b hdiag si sj sg (-1) (-3) (-2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa [hsi, hsj, hsg] using hroot)

private lemma diagonal_pairingIn_eq_zero_or_two_or_neg_two
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    (i j : ι) :
    P.pairingIn ℤ i j = 0 ∨ P.pairingIn ℤ i j = 2 ∨
      P.pairingIn ℤ i j = -2 := by
  obtain ⟨si, hsi⟩ := diagonal_base_root_eq_or_neg P b hdiag i
  obtain ⟨sj, hsj⟩ := diagonal_base_root_eq_or_neg P b hdiag j
  rcases hsi with hsi | hsi <;> rcases hsj with hsj | hsj
  all_goals
    have hi : i = si ∨ i = P.reflectionPerm si si := by
      first | exact Or.inl (P.root.injective hsi) | exact Or.inr (P.root_eq_neg_iff.mp hsi)
    have hj : j = sj ∨ j = P.reflectionPerm sj sj := by
      first | exact Or.inl (P.root.injective hsj) | exact Or.inr (P.root_eq_neg_iff.mp hsj)
    have hbase : P.pairingIn ℤ si sj = 0 ∨ si = sj := by
      by_cases hst : si = sj
      · exact Or.inr hst
      · exact Or.inl (by
          change b.cartanMatrixIn ℤ si sj = 0
          exact hdiag si sj hst)
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rcases hbase with hzero | heq
      · exact Or.inl hzero
      · subst sj
        exact Or.inr (Or.inl (by simp))
    · rcases hbase with hzero | heq
      · exact Or.inl (by simpa using hzero)
      · subst sj
        exact Or.inr (Or.inr (by simp))
    · rcases hbase with hzero | heq
      · exact Or.inl (by simpa using hzero)
      · subst sj
        exact Or.inr (Or.inr (by simp))
    · rcases hbase with hzero | heq
      · exact Or.inl (by simpa using hzero)
      · subst sj
        exact Or.inr (Or.inl (by simp))

private lemma simple_roots_not_opposite
    {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base) (hD : D.IsRealization)
    (hRealization : IsRootSystemRealization D P e b)
    {α β : D.Root} (hα : α ∈ D.simple) (hβ : β ∈ D.simple) (hne : α ≠ β) :
    P.root (e α) ≠ -P.root (e β) := by
  intro hneg
  have hidx : e α = e (D.neg β) := by
    rw [P.root_eq_neg_iff] at hneg
    exact hneg.trans (hRealization.2.2.1 β).symm
  have hab : α = D.neg β := e.injective hidx
  rcases hD with ⟨_, _, _, _, _, _, _, _, hnegHeight, _, hPositive, hSimple⟩
  have hαpos : 0 < D.height α := by
    have hmem : α ∈ D.positive := (hSimple.1 α).mp hα |>.1
    simpa [hPositive] using hmem
  have hβpos : 0 < D.height β := by
    have hmem : β ∈ D.positive := (hSimple.1 β).mp hβ |>.1
    simpa [hPositive] using hmem
  have hnegpos : 0 < D.height (D.neg β) := by
    have hmem : D.neg β ∈ D.positive := by
      rw [← hab]
      exact (hSimple.1 α).mp hα |>.1
    simpa [hPositive] using hmem
  rw [hnegHeight] at hnegpos
  linarith

private lemma irreducible_of_hasDynkinType_of_standard_connected
    {ι M N : Type*} [Finite ι] [Nonempty ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (C : RootClassification) (hType : HasDynkinType P C)
    (hstd : ∀ i j : Fin C.rank,
      Relation.ReflTransGen
        (fun u v => dynkinCartanEntry C u v ≠ 0) i j) : P.IsIrreducible := by
  rcases hType with ⟨b, e, hbe⟩
  have hbase : b.support.Nonempty := b.support_nonempty
  have hconn : ∀ s t : b.support,
      Relation.ReflTransGen
        (fun u v : b.support => b.cartanMatrix u v ≠ 0) s t := by
    intro s t
    have map_path : ∀ {i j : Fin C.rank},
        Relation.ReflTransGen
          (fun u v => dynkinCartanEntry C u v ≠ 0) i j →
        Relation.ReflTransGen
          (fun u v : b.support => b.cartanMatrix u v ≠ 0)
          (e.symm i) (e.symm j) := by
      intro i j h
      induction h with
      | refl => exact .refl
      | tail hxy hyz ih =>
          apply Relation.ReflTransGen.tail ih
          change b.cartanMatrixIn ℤ (e.symm _) (e.symm _) ≠ 0
          rw [hbe]
          simpa using hyz
    simpa using map_path (hstd (e s) (e t))
  exact isIrreducible_of_cartan_connected P b hbase hconn

/-- A classified root pairing is irreducible, except for the invalid-rank
tables whose Dynkin matrix is explicitly diagonal. -/
public lemma irreducible_or_diagonal_of_hasDynkinType
    {ι M N : Type*} [Finite ι] [Nonempty ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (C : RootClassification) (hType : HasDynkinType P C) :
    P.IsIrreducible ∨ ∃ b : P.Base, ∀ s t : b.support,
      s ≠ t → b.cartanMatrix s t = 0 := by
  rcases hType with ⟨b, e, hbe⟩
  have hbase : b.support.Nonempty := b.support_nonempty
  have hrank : 0 < C.rank := by
    obtain ⟨s, hs⟩ := hbase
    have hslt := (e ⟨s, hs⟩).isLt
    omega
  have hType' : HasDynkinType P C := ⟨b, e, hbe⟩
  rcases C with ⟨kind, rank⟩
  have hrank' : 0 < rank := by simpa using hrank
  cases kind with
  | A =>
      exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
        ⟨.A, rank⟩ hType' (dynkin_connected_A rank hrank'))
  | B =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.B, 1⟩ hType' (dynkin_connected_singleton .B))
      · have hrank2 : 1 < rank := by omega
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.B, rank⟩ hType' (dynkin_connected_B rank hrank2))
  | C =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.C, 1⟩ hType' (dynkin_connected_singleton .C))
      · have hrank2 : 1 < rank := by omega
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.C, rank⟩ hType' (dynkin_connected_C rank hrank2))
  | D =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.D, 1⟩ hType' (dynkin_connected_singleton .D))
      · by_cases hrank2 : rank = 2
        · subst rank
          exact Or.inr (diagonal_base_of_hType ⟨.D, 2⟩ hType' dynkin_diagonal_D2)
        · have hrank3 : 2 < rank := by omega
          exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
            ⟨.D, rank⟩ hType' (dynkin_connected_D rank hrank3))
  | E6 =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.E6, 1⟩ hType' (dynkin_connected_singleton .E6))
      · by_cases hrank6 : rank = 6
        · subst rank
          exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
            ⟨.E6, 6⟩ hType' dynkin_connected_E6)
        · exact Or.inr (diagonal_base_of_hType ⟨.E6, rank⟩ hType'
            (dynkin_diagonal_E6_invalid rank hrank6))
  | E7 =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.E7, 1⟩ hType' (dynkin_connected_singleton .E7))
      · by_cases hrank7 : rank = 7
        · subst rank
          exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
            ⟨.E7, 7⟩ hType' dynkin_connected_E7)
        · exact Or.inr (diagonal_base_of_hType ⟨.E7, rank⟩ hType'
            (dynkin_diagonal_E7_invalid rank hrank7))
  | E8 =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.E8, 1⟩ hType' (dynkin_connected_singleton .E8))
      · by_cases hrank8 : rank = 8
        · subst rank
          exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
            ⟨.E8, 8⟩ hType' dynkin_connected_E8)
        · exact Or.inr (diagonal_base_of_hType ⟨.E8, rank⟩ hType'
            (dynkin_diagonal_E8_invalid rank hrank8))
  | F4 =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.F4, 1⟩ hType' (dynkin_connected_singleton .F4))
      · by_cases hrank4 : rank = 4
        · subst rank
          exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
            ⟨.F4, 4⟩ hType' dynkin_connected_F4)
        · exact Or.inr (diagonal_base_of_hType ⟨.F4, rank⟩ hType'
            (dynkin_diagonal_F4_invalid rank hrank4))
  | G2 =>
      by_cases hrank1 : rank = 1
      · subst rank
        exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
          ⟨.G2, 1⟩ hType' (dynkin_connected_singleton .G2))
      · by_cases hrank2 : rank = 2
        · subst rank
          exact Or.inl (irreducible_of_hasDynkinType_of_standard_connected P
            ⟨.G2, 2⟩ hType' dynkin_connected_G2)
        · exact Or.inr (diagonal_base_of_hType ⟨.G2, rank⟩ hType'
            (dynkin_diagonal_G2_invalid rank hrank2))

public theorem HasExpectedChevalleyCoefficient.ne_zero_of_nonsingular_of_hasDynkinType_or_diagonal
    {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) (hD : D.IsRealization)
    (hRealization : IsRootSystemRealization D P e base)
    (classification : RootClassification)
    (hType : HasDynkinType P classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    {α β : D.Root} {q : ChevalleyCommutatorTerm D.Root} {c : k}
    (h : HasExpectedChevalleyCoefficient D P e α β q c) :
    c ≠ 0 := by
  letI := Fintype.ofFinite ι
  letI : Nonempty ι := ⟨e α⟩
  rcases irreducible_or_diagonal_of_hasDynkinType P classification hType with
    hirred | ⟨b, hdiag⟩
  · letI := hirred
    exact h.ne_zero_of_nonsingular_of_hasDynkinType
      D P e classification hType hNonsingular
  · have hTwoKind :
        IsChevalleyCoefficientExceptionalTwo D P e α β q →
          classification.kind = .B ∨ classification.kind = .C ∨
            classification.kind = .F4 ∨ classification.kind = .G2 := by
      intro hex
      rcases hex with ⟨hvalid, hcase⟩
      rcases hcase with hfirst | hsecond | hthird
      · rcases hfirst with ⟨hqi, hqj, _, _⟩
        have hroot : P.root (e q.root) =
            P.root (e α) + P.root (e β) := by
          simpa [hqi, hqj] using hvalid.2.2
        exact (diagonal_root_sum_false b hdiag hroot).elim
      · rcases hsecond with ⟨hqi, hqj, _, _, _⟩
        have hroot : P.root (e q.root) =
            P.root (e α) + P.root (e β) := by
          simpa [hqi, hqj] using hvalid.2.2
        exact (diagonal_root_sum_false b hdiag hroot).elim
      · rcases hthird with ⟨hqi, hqj, hα, hβ, hab, _⟩
        have hroot : P.root (e q.root) =
            (3 : ℚ) • P.root (e α) + (2 : ℚ) • P.root (e β) := by
          simpa [hqi, hqj] using hvalid.2.2
        have hnotop := simple_roots_not_opposite D P e base hD hRealization
          hα hβ hab
        exact (diagonal_weighted_root_false b hdiag hnotop hroot).elim
    have hThreeKind :
        IsChevalleyCoefficientExceptionalThree D P e α β q →
          classification.kind = .G2 := by
      intro hex
      obtain ⟨i, j, hpair⟩ :=
        chevalleyExceptionalThree_pairingIn_three D P e hex
      rcases diagonal_pairingIn_eq_zero_or_two_or_neg_two b hdiag i j with
        hzero | htwo | hneg
      · omega
      · omega
      · omega
    exact h.ne_zero_of_nonsingular D P e classification
      hNonsingular hTwoKind hThreeKind

public theorem ParabolicRelativeRootSetup.expectedChevalleyCoefficient_ne_zero
    {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    {α β : S.D.Root} {q : ChevalleyCommutatorTerm S.D.Root} {c : k}
    (h : HasExpectedChevalleyCoefficient S.D S.rootPairing S.rootEquiv α β q c) :
    c ≠ 0 := by
  exact h.ne_zero_of_nonsingular_of_hasDynkinType_or_diagonal
    S.D S.rootPairing S.rootEquiv S.rootBase S.rootGroupRealization
      S.rootSystemRealization classification hType hNonsingular

end Theory.AlgebraicGroup
