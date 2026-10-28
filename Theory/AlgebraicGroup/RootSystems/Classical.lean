module

public import Theory.AlgebraicGroup.RootSystems.Coordinate
public import Theory.AlgebraicGroup.RootSystems.GraphDegree

namespace Theory.AlgebraicGroup

namespace StandardRootSystem

@[expose]
public noncomputable def typeARoots (m : ℕ) : Set (Vec (m + 1)) :=
  {x | ∃ i j : Fin (m + 1), i ≠ j ∧
    (x = basisVector i - basisVector j ∨ x = basisVector j - basisVector i)}

@[expose]
public noncomputable def typeASimpleRoot (m : ℕ) (i : Fin m) : Vec (m + 1) :=
  basisVector i.castSucc - basisVector i.succ

@[expose]
public noncomputable def typeALowestRoot (m : ℕ) : Vec (m + 1) :=
  basisVector (Fin.last m) - basisVector 0

@[expose]
public noncomputable def typeBRoots (m : ℕ) : Set (Vec m) :=
  pairRoots m ∪ signedUnitRoots m

@[expose]
public noncomputable def typeCRoots (m : ℕ) : Set (Vec m) :=
  pairRoots m ∪ signedDoubleUnitRoots m

@[expose]
public noncomputable def typeDRoots (m : ℕ) : Set (Vec m) := pairRoots m

@[expose]
public noncomputable def typeBSimpleRoot (m : ℕ) (i : Fin (m + 2)) : Vec (m + 2) :=
  if h : i.val < m + 1 then
    basisVector i - basisVector ⟨i.val + 1, Nat.succ_lt_succ h⟩
  else
    basisVector i

@[expose]
public noncomputable def typeBLowestRoot (m : ℕ) : Vec (m + 2) :=
  -basisVector 0 - basisVector 1

@[expose]
public noncomputable def typeCSimpleRoot (m : ℕ) (i : Fin (m + 1)) : Vec (m + 1) :=
  if h : i.val < m then
    basisVector i - basisVector ⟨i.val + 1, Nat.succ_lt_succ h⟩
  else
    2 • basisVector i

@[expose]
public noncomputable def typeCLowestRoot (m : ℕ) : Vec (m + 1) :=
  -(2 • basisVector 0)

@[expose]
public noncomputable def typeDSimpleRoot (m : ℕ) (i : Fin (m + 2)) : Vec (m + 2) :=
  if h : i.val < m + 1 then
    basisVector i - basisVector ⟨i.val + 1, Nat.succ_lt_succ h⟩
  else
    basisVector ⟨m, by omega⟩ + basisVector ⟨m + 1, by omega⟩

@[expose]
public noncomputable def typeDLowestRoot (m : ℕ) : Vec (m + 2) :=
  -basisVector 0 - basisVector 1

public abbrev TypeDRootIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2} ×
    ({-1, 1} : Set ℝ) × ({-1, 1} : Set ℝ)

@[expose] public noncomputable def typeDRootVector (n : ℕ) : TypeDRootIndex n → Vec n
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩ => s.1 • basisVector i + t.1 • basisVector j

@[expose] public noncomputable def typeDRootEmbedding (n : ℕ) :
    TypeDRootIndex n → typeDRoots n :=
  fun r => ⟨typeDRootVector n r, by
    rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    exact ⟨i, j, hij.ne, s.1, t.1, s.2, t.2, rfl⟩⟩

/-- For positive rank, the displayed lowest root of the standard type `A` model belongs to its
root set. -/
public lemma typeALowestRoot_mem_typeARoots (m : ℕ) (hm : 0 < m) :
    typeALowestRoot m ∈ typeARoots m := by
  refine ⟨Fin.last m, 0, ?_, Or.inl rfl⟩
  intro h
  have := congrArg Fin.val h
  simp_all

open Set

/-- Every displayed simple root of the standard type `A` model belongs to its root set. -/
public lemma typeASimpleRoot_mem_typeARoots (m : ℕ) (i : Fin m) :
    typeASimpleRoot m i ∈ typeARoots m := by
  refine ⟨i.castSucc, i.succ, ?_, Or.inl rfl⟩
  intro h
  have := congrArg Fin.val h
  simp at this

open Set

/-- The displayed lowest root of the standard type `B` model belongs to its root set. -/
public lemma typeBLowestRoot_mem_typeBRoots (m : ℕ) :
    typeBLowestRoot m ∈ typeBRoots (m + 2) := by
  left
  refine ⟨0, 1, ?_, -1, -1, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
  · simp
  · simp
  · simp [typeBLowestRoot, basisVector, sub_eq_add_neg]

open Set

public abbrev TypeBPairRootIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2} ×
    ({-1, 1} : Set ℝ) × ({-1, 1} : Set ℝ)

public abbrev TypeBRootIndex (n : ℕ) :=
  Sum (TypeBPairRootIndex n) (Fin n × Bool)

@[expose]
public noncomputable def typeBRootVector (n : ℕ) : TypeBRootIndex n → Vec n
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩ => s.1 • basisVector i + t.1 • basisVector j
  | .inr ⟨i, false⟩ => basisVector i
  | .inr ⟨i, true⟩ => -basisVector i

@[expose]
public noncomputable def typeBRootEmbedding (n : ℕ) :
    TypeBRootIndex n → typeBRoots n :=
  fun r => ⟨typeBRootVector n r, by
    cases r with
    | inl r =>
      rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
      apply Set.mem_union_left
      exact ⟨i, j, hij.ne, s.1, t.1, s.2, t.2, rfl⟩
    | inr r =>
      rcases r with ⟨i, s⟩
      apply Set.mem_union_right
      refine ⟨i, ?_⟩
      cases s <;> simp [typeBRootVector]⟩

private lemma pairRoot_support (n : ℕ) (i j : Fin n) (hij : i < j)
    (s t : ({-1, 1} : Set ℝ)) :
    Function.support (fun k => s.1 • basisVector i k + t.1 • basisVector j k) = {i, j} := by
  have hs : s.1 ≠ 0 := by rcases s.2 with hs | hs <;> rw [hs] <;> norm_num
  have ht : t.1 ≠ 0 := by rcases t.2 with ht | ht <;> rw [ht] <;> norm_num
  ext k
  by_cases hki : k = i
  · subst k
    simp [Function.mem_support, basisVector, Pi.single_apply, hij.ne, hs]
  · by_cases hkj : k = j
    · subst k
      simp [Function.mem_support, basisVector, Pi.single_apply, hij.ne', ht]
    · simp [Function.mem_support, basisVector, Pi.single_apply, hki, hkj]

private lemma pairRootVector_injective (n : ℕ) :
    Function.Injective (fun r : TypeBPairRootIndex n => typeBRootVector n (.inl r)) := by
  intro r q h
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  rcases q with ⟨⟨⟨k, l⟩, hkl⟩, u, v⟩
  have hsupp : ({i, j} : Set (Fin n)) = {k, l} := by
    rw [← pairRoot_support n i j hij s t, ← pairRoot_support n k l hkl u v]
    exact congrArg Function.support h
  have hindices : i = k ∧ j = l := by
    rcases Set.pair_eq_pair_iff.mp hsupp with hdirect | ⟨hil, hjk⟩
    · exact hdirect
    · rw [hil, hjk] at hij
      exact False.elim (asymm hkl hij)
  obtain ⟨rfl, rfl⟩ := hindices
  have hs : s = u := by
    apply Subtype.ext
    have hi := congrFun h i
    simpa [typeBRootVector, basisVector, hij.ne] using hi
  have ht : t = v := by
    apply Subtype.ext
    have hj := congrFun h j
    simpa [typeBRootVector, basisVector, hij.ne] using hj
  simp [hs, ht]

private lemma unitRootVector_injective (n : ℕ) :
    Function.Injective (fun r : Fin n × Bool => typeBRootVector n (.inr r)) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have hij : i = j := by
    by_contra hne
    have hi := congrFun h i
    cases s <;> cases t <;> simp [typeBRootVector, basisVector, hne] at hi
  subst j
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · have hi := congrFun h i
      norm_num [typeBRootVector, basisVector] at hi
    · have hi := congrFun h i
      norm_num [typeBRootVector, basisVector] at hi
    · rfl
  simp [hst]

private lemma pairRootVector_ne_unitRootVector (n : ℕ) (r : TypeBPairRootIndex n)
    (q : Fin n × Bool) : typeBRootVector n (.inl r) ≠ typeBRootVector n (.inr q) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  rcases q with ⟨k, u⟩
  have hs : s.1 ≠ 0 := by rcases s.2 with hs | hs <;> rw [hs] <;> norm_num
  have ht : t.1 ≠ 0 := by rcases t.2 with ht | ht <;> rw [ht] <;> norm_num
  intro h
  by_cases hik : i = k
  · subst k
    have hj := congrFun h j
    cases u <;> simp [typeBRootVector, basisVector, hij.ne, ht] at hj
  · have hi := congrFun h i
    cases u <;> simp [typeBRootVector, basisVector, hik, hij.ne, hs] at hi

public lemma typeBRootEmbedding_injective (n : ℕ) :
    Function.Injective (typeBRootEmbedding n) := by
  intro r q h
  have hval := congrArg Subtype.val h
  change typeBRootVector n r = typeBRootVector n q at hval
  cases r with
  | inl r =>
    cases q with
    | inl q => exact congrArg Sum.inl (pairRootVector_injective n hval)
    | inr q => exact (pairRootVector_ne_unitRootVector n r q hval).elim
  | inr r =>
    cases q with
    | inl q => exact (pairRootVector_ne_unitRootVector n q r hval.symm).elim
    | inr q => exact congrArg Sum.inr (unitRootVector_injective n hval)

open Set

/-- Every displayed simple root of the standard type `B` model belongs to its root set. -/
public lemma typeBSimpleRoot_mem_typeBRoots (m : ℕ) (i : Fin (m + 2)) :
    typeBSimpleRoot m i ∈ typeBRoots (m + 2) := by
  by_cases hi : i = Fin.last (m + 1)
  · subst i
    right
    refine ⟨Fin.last (m + 1), Or.inl ?_⟩
    simp [typeBSimpleRoot]
  · left
    have hilast : i.val < m + 1 := by
      by_contra h
      apply hi
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    refine ⟨i, ⟨i.val + 1, Nat.succ_lt_succ hilast⟩, ?_, 1, -1, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · simp
    · simp
    · simp [typeBSimpleRoot, hilast, sub_eq_add_neg]

private lemma dot_sub_left {n : ℕ} (x y z : Vec n) :
    dot (x - y) z = dot x z - dot y z := by
  simp only [dot, Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

private lemma dot_sub_right {n : ℕ} (x y z : Vec n) :
    dot x (y - z) = dot x y - dot x z := by
  simp only [dot, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

private lemma dot_basisVector_basisVector {n : ℕ} (i j : Fin n) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma val_lt_of_ne_last (m : ℕ) (i : Fin (m + 2))
    (hi : i ≠ Fin.last (m + 1)) : i.val < m + 1 := by
  by_contra h
  apply hi
  apply Fin.ext
  simp only [Fin.val_last]
  omega

private lemma typeBSimpleRoot_dot_of_ne_last (m : ℕ) (i j : Fin (m + 2))
    (hi : i ≠ Fin.last (m + 1)) (hj : j ≠ Fin.last (m + 1)) :
    dot (typeBSimpleRoot m i) (typeBSimpleRoot m j) =
      if i = j then 2 else if i.val + 1 = j.val then -1
      else if j.val + 1 = i.val then -1 else 0 := by
  have hiv := val_lt_of_ne_last m i hi
  have hjv := val_lt_of_ne_last m j hj
  simp only [typeBSimpleRoot, dif_pos hiv, dif_pos hjv]
  rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_basisVector_basisVector,
    dot_basisVector_basisVector, dot_basisVector_basisVector, dot_basisVector_basisVector]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> norm_num at * <;> omega

private lemma typeBSimpleRoot_dot_last (m : ℕ) (i : Fin (m + 2))
    (hi : i ≠ Fin.last (m + 1)) :
    dot (typeBSimpleRoot m i) (typeBSimpleRoot m (Fin.last (m + 1))) =
      if i = Fin.last (m + 1) then 2
      else if i.val + 1 = (Fin.last (m + 1)).val then -1
      else if (Fin.last (m + 1)).val + 1 = i.val then -1 else 0 := by
  have hiv := val_lt_of_ne_last m i hi
  have hlast : ¬(Fin.last (m + 1)).val < m + 1 := by simp
  simp only [typeBSimpleRoot, dif_pos hiv, dif_neg hlast]
  rw [dot_sub_left, dot_basisVector_basisVector, dot_basisVector_basisVector]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> norm_num at * <;> omega

private lemma typeBSimpleRoot_last_dot (m : ℕ) (j : Fin (m + 2))
    (hj : j ≠ Fin.last (m + 1)) :
    dot (typeBSimpleRoot m (Fin.last (m + 1))) (typeBSimpleRoot m j) =
      if Fin.last (m + 1) = j then 2
      else if (Fin.last (m + 1)).val + 1 = j.val then -1
      else if j.val + 1 = (Fin.last (m + 1)).val then -1 else 0 := by
  have hjv := val_lt_of_ne_last m j hj
  have hlast : ¬(Fin.last (m + 1)).val < m + 1 := by simp
  simp only [typeBSimpleRoot, dif_neg hlast, dif_pos hjv]
  rw [dot_sub_right, dot_basisVector_basisVector, dot_basisVector_basisVector]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> norm_num at * <;> omega

/-- The displayed type `B` simple roots have their Cartan pairing, with the coroot
determined by the second root: the terminal short root doubles the dot product. -/
public lemma typeBSimpleRoot_pairing (m : ℕ) (i j : Fin (m + 2)) :
    (if j = Fin.last (m + 1) then
        2 * dot (typeBSimpleRoot m i) (typeBSimpleRoot m j)
      else dot (typeBSimpleRoot m i) (typeBSimpleRoot m j)) =
      if i = j then 2
      else if i.val + 1 = j.val then
        if j = Fin.last (m + 1) then -2 else -1
      else if j.val + 1 = i.val then -1 else 0 := by
  by_cases hi : i = Fin.last (m + 1)
  · subst i
    by_cases hj : j = Fin.last (m + 1)
    · subst j
      simp [typeBSimpleRoot, dot_basisVector_basisVector]
    · simp only [if_neg hj]
      rw [typeBSimpleRoot_last_dot m j hj]
  · by_cases hj : j = Fin.last (m + 1)
    · subst j
      rw [typeBSimpleRoot_dot_last m i hi]
      split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_last] <;> norm_num at *; omega
    · simp only [if_neg hj]
      rw [typeBSimpleRoot_dot_of_ne_last m i j hi hj]

open Set

/-- The displayed lowest root of the standard type `C` model belongs to its root set. -/
public lemma typeCLowestRoot_mem_typeCRoots (m : ℕ) :
    typeCLowestRoot m ∈ typeCRoots (m + 1) := by
  right
  exact ⟨0, Or.inr rfl⟩

open Set

public abbrev TypeCPairRootIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2} ×
    ({-1, 1} : Set ℝ) × ({-1, 1} : Set ℝ)

public abbrev TypeCRootIndex (n : ℕ) :=
  Sum (TypeCPairRootIndex n) (Fin n × Bool)

@[expose]
public noncomputable def typeCRootVector (n : ℕ) : TypeCRootIndex n → Vec n
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩ => s.1 • basisVector i + t.1 • basisVector j
  | .inr ⟨i, false⟩ => 2 • basisVector i
  | .inr ⟨i, true⟩ => -(2 • basisVector i)

@[expose]
public noncomputable def typeCRootEmbedding (n : ℕ) :
    TypeCRootIndex n → typeCRoots n :=
  fun r => ⟨typeCRootVector n r, by
    cases r with
    | inl r =>
      rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
      apply Set.mem_union_left
      exact ⟨i, j, hij.ne, s.1, t.1, s.2, t.2, rfl⟩
    | inr r =>
      rcases r with ⟨i, s⟩
      apply Set.mem_union_right
      refine ⟨i, ?_⟩
      cases s <;> simp [typeCRootVector]⟩

private lemma pairRoot_support_C (n : ℕ) (i j : Fin n) (hij : i < j)
    (s t : ({-1, 1} : Set ℝ)) :
    Function.support (fun k => s.1 • basisVector i k + t.1 • basisVector j k) = {i, j} := by
  have hs : s.1 ≠ 0 := by rcases s.2 with hs | hs <;> rw [hs] <;> norm_num
  have ht : t.1 ≠ 0 := by rcases t.2 with ht | ht <;> rw [ht] <;> norm_num
  ext k
  by_cases hki : k = i
  · subst k
    simp [Function.mem_support, basisVector, Pi.single_apply, hij.ne, hs]
  · by_cases hkj : k = j
    · subst k
      simp [Function.mem_support, basisVector, Pi.single_apply, hij.ne', ht]
    · simp [Function.mem_support, basisVector, Pi.single_apply, hki, hkj]

private lemma pairRootVector_injective_C (n : ℕ) :
    Function.Injective (fun r : TypeCPairRootIndex n => typeCRootVector n (.inl r)) := by
  intro r q h
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  rcases q with ⟨⟨⟨k, l⟩, hkl⟩, u, v⟩
  have hsupp : ({i, j} : Set (Fin n)) = {k, l} := by
    rw [← pairRoot_support_C n i j hij s t, ← pairRoot_support_C n k l hkl u v]
    exact congrArg Function.support h
  have hindices : i = k ∧ j = l := by
    rcases Set.pair_eq_pair_iff.mp hsupp with hdirect | ⟨hil, hjk⟩
    · exact hdirect
    · rw [hil, hjk] at hij
      exact False.elim (asymm hkl hij)
  obtain ⟨rfl, rfl⟩ := hindices
  have hs : s = u := by
    apply Subtype.ext
    have hi := congrFun h i
    simpa [typeCRootVector, basisVector, hij.ne] using hi
  have ht : t = v := by
    apply Subtype.ext
    have hj := congrFun h j
    simpa [typeCRootVector, basisVector, hij.ne] using hj
  simp [hs, ht]

private lemma doubleUnitRootVector_injective_C (n : ℕ) :
    Function.Injective (fun r : Fin n × Bool => typeCRootVector n (.inr r)) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have hij : i = j := by
    by_contra hne
    have hi := congrFun h i
    cases s <;> cases t <;> norm_num [typeCRootVector, basisVector, hne] at hi
  subst j
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · have hi := congrFun h i
      norm_num [typeCRootVector, basisVector] at hi
    · have hi := congrFun h i
      norm_num [typeCRootVector, basisVector] at hi
    · rfl
  simp [hst]

private lemma pairRootVector_ne_doubleUnitRootVector_C (n : ℕ) (r : TypeCPairRootIndex n)
    (q : Fin n × Bool) : typeCRootVector n (.inl r) ≠ typeCRootVector n (.inr q) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  rcases q with ⟨k, u⟩
  have hs : s.1 ≠ 0 := by rcases s.2 with hs | hs <;> rw [hs] <;> norm_num
  have ht : t.1 ≠ 0 := by rcases t.2 with ht | ht <;> rw [ht] <;> norm_num
  intro h
  by_cases hik : i = k
  · subst k
    have hj := congrFun h j
    cases u <;> simp [typeCRootVector, basisVector, hij.ne, ht] at hj
  · have hi := congrFun h i
    cases u <;> simp [typeCRootVector, basisVector, hik, hij.ne, hs] at hi

public lemma typeCRootEmbedding_injective (n : ℕ) :
    Function.Injective (typeCRootEmbedding n) := by
  intro r q h
  have hval := congrArg Subtype.val h
  change typeCRootVector n r = typeCRootVector n q at hval
  cases r with
  | inl r =>
    cases q with
    | inl q => exact congrArg Sum.inl (pairRootVector_injective_C n hval)
    | inr q => exact (pairRootVector_ne_doubleUnitRootVector_C n r q hval).elim
  | inr r =>
    cases q with
    | inl q => exact (pairRootVector_ne_doubleUnitRootVector_C n q r hval.symm).elim
    | inr q => exact congrArg Sum.inr (doubleUnitRootVector_injective_C n hval)

open Set

/-- Every displayed simple root of the standard type `C` model belongs to its root set. -/
public lemma typeCSimpleRoot_mem_typeCRoots (m : ℕ) (i : Fin (m + 1)) :
    typeCSimpleRoot m i ∈ typeCRoots (m + 1) := by
  by_cases hi : i.val < m
  · left
    refine ⟨i, ⟨i.val + 1, Nat.succ_lt_succ hi⟩, ?_, 1, -1, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · simp
    · simp
    · simp [typeCSimpleRoot, hi, sub_eq_add_neg]
  · right
    refine ⟨i, Or.inl ?_⟩
    simp [typeCSimpleRoot, hi]

private lemma dot_smul_left {n : ℕ} (c : ℝ) (x y : Vec n) :
    dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma dot_smul_right {n : ℕ} (c : ℝ) (x y : Vec n) :
    dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma two_nsmul_eq_two_smul {n : ℕ} (x : Vec n) :
    2 • x = (2 : ℝ) • x := by
  ext k
  simp

private lemma dot_basisVector_basisVector_C {n : ℕ} (i j : Fin n) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma dot_two_nsmul_basisVector_self {n : ℕ} (i : Fin n) :
    dot (2 • basisVector i) (2 • basisVector i) = 4 := by
  rw [two_nsmul_eq_two_smul, dot_smul_left, dot_smul_right,
    dot_basisVector_basisVector]
  norm_num

private lemma val_lt_of_ne_last_C (m : ℕ) (i : Fin (m + 1))
    (hi : i ≠ Fin.last m) : i.val < m := by
  by_contra h
  apply hi
  apply Fin.ext
  simp only [Fin.val_last]
  omega

private lemma typeCSimpleRoot_dot_of_ne_last (m : ℕ) (i j : Fin (m + 1))
    (hi : i ≠ Fin.last m) (hj : j ≠ Fin.last m) :
    dot (typeCSimpleRoot m i) (typeCSimpleRoot m j) =
      if i = j then 2 else if i.val + 1 = j.val then -1
      else if j.val + 1 = i.val then -1 else 0 := by
  have hiv := val_lt_of_ne_last_C m i hi
  have hjv := val_lt_of_ne_last_C m j hj
  simp only [typeCSimpleRoot, dif_pos hiv, dif_pos hjv]
  rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_basisVector_basisVector_C,
    dot_basisVector_basisVector_C, dot_basisVector_basisVector_C, dot_basisVector_basisVector_C]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> norm_num at * <;> omega

private lemma typeCSimpleRoot_dot_last (m : ℕ) (i : Fin (m + 1))
    (hi : i ≠ Fin.last m) :
    dot (typeCSimpleRoot m i) (typeCSimpleRoot m (Fin.last m)) =
      if i = Fin.last m then 4
      else if i.val + 1 = (Fin.last m).val then -2
      else if (Fin.last m).val + 1 = i.val then -2 else 0 := by
  have hiv := val_lt_of_ne_last_C m i hi
  have hlast : ¬(Fin.last m).val < m := by simp
  simp only [typeCSimpleRoot, dif_pos hiv, dif_neg hlast]
  rw [two_nsmul_eq_two_smul]
  rw [dot_sub_left, dot_smul_right, dot_smul_right,
    dot_basisVector_basisVector_C, dot_basisVector_basisVector_C]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> norm_num at * <;> omega

private lemma typeCSimpleRoot_last_dot (m : ℕ) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    dot (typeCSimpleRoot m (Fin.last m)) (typeCSimpleRoot m j) =
      if Fin.last m = j then 4
      else if (Fin.last m).val + 1 = j.val then -2
      else if j.val + 1 = (Fin.last m).val then -2 else 0 := by
  have hjv := val_lt_of_ne_last_C m j hj
  have hlast : ¬(Fin.last m).val < m := by simp
  simp only [typeCSimpleRoot, dif_neg hlast, dif_pos hjv]
  rw [two_nsmul_eq_two_smul]
  rw [dot_sub_right, dot_smul_left, dot_smul_left,
    dot_basisVector_basisVector_C, dot_basisVector_basisVector_C]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> norm_num at * <;> omega

/-- The displayed type `C` simple roots have their Cartan pairing, with the coroot
determined by the second root: the terminal long root halves the dot product. -/
public lemma typeCSimpleRoot_pairing (m : ℕ) (i j : Fin (m + 1)) :
    (if j = Fin.last m then
        (1 / 2 : ℝ) * dot (typeCSimpleRoot m i) (typeCSimpleRoot m j)
      else dot (typeCSimpleRoot m i) (typeCSimpleRoot m j)) =
      if i = j then 2
      else if i.val + 1 = j.val then -1
      else if j.val + 1 = i.val then
        if i = Fin.last m then -2 else -1
      else 0 := by
  by_cases hi : i = Fin.last m
  · subst i
    by_cases hj : j = Fin.last m
    · subst j
      have hlast : ¬(Fin.last m).val < m := by simp
      simp only [typeCSimpleRoot, dif_neg hlast]
      rw [dot_two_nsmul_basisVector_self]
      norm_num
    · simp only [if_neg hj]
      rw [typeCSimpleRoot_last_dot m j hj]
      split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_last] <;> norm_num at *
      all_goals omega
  · by_cases hj : j = Fin.last m
    · subst j
      rw [typeCSimpleRoot_dot_last m i hi]
      split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_last] <;> norm_num at *
    · simp only [if_neg hj]
      rw [typeCSimpleRoot_dot_of_ne_last m i j hi hj]
      simp [hi]

/-- The standard type `D` Cartan matrix, with the terminal root at `Fin.last (m + 1)`. -/
@[expose] public def typeDCartanMatrix (m : ℕ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  fun i j => if i = j then 2
    else if j = Fin.last (m + 1) then
      if i.val + 2 = j.val then -1 else 0
    else if i = Fin.last (m + 1) then
      if j.val + 2 = i.val then -1 else 0
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then -1 else 0

open Set

/-- The displayed lowest root of the standard type `D` model belongs to its root set. -/
public lemma typeDLowestRoot_mem_typeDRoots (m : ℕ) :
    typeDLowestRoot m ∈ typeDRoots (m + 2) := by
  change typeDLowestRoot m ∈ pairRoots (m + 2)
  refine ⟨0, 1, ?_, -1, -1, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
  · simp
  · simp
  · simp [typeDLowestRoot, basisVector, sub_eq_add_neg]

open Set

/-- Every displayed simple root of the standard type `D` model belongs to its root set. -/
public lemma typeDSimpleRoot_mem_typeDRoots (m : ℕ) (i : Fin (m + 2)) :
    typeDSimpleRoot m i ∈ typeDRoots (m + 2) := by
  by_cases hi : i.val < m + 1
  · refine ⟨i, ⟨i.val + 1, Nat.succ_lt_succ hi⟩, ?_, 1, -1, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · simp
    · simp
    · simp [typeDSimpleRoot, hi, sub_eq_add_neg]
  · refine ⟨⟨m, by omega⟩, ⟨m + 1, by omega⟩, ?_, 1, 1, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · simp
    · simp
    · simp [typeDSimpleRoot, hi]

private lemma dot_add_left {n : ℕ} (x y z : Vec n) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

private lemma dot_add_right {n : ℕ} (x y z : Vec n) :
    dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

private lemma dot_basisVector_basisVector_D {n : ℕ} (i j : Fin n) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma val_lt_of_ne_last_D (m : ℕ) (i : Fin (m + 2))
    (hi : i ≠ Fin.last (m + 1)) : i.val < m + 1 := by
  by_contra h
  apply hi
  apply Fin.ext
  simp only [Fin.val_last]
  omega

private lemma typeDSimpleRoot_dot_of_ne_last (m : ℕ) (i j : Fin (m + 2))
    (hi : i ≠ Fin.last (m + 1)) (hj : j ≠ Fin.last (m + 1)) :
    dot (typeDSimpleRoot m i) (typeDSimpleRoot m j) =
      if i = j then 2 else if i.val + 1 = j.val then -1
      else if j.val + 1 = i.val then -1 else 0 := by
  have hiv := val_lt_of_ne_last_D m i hi
  have hjv := val_lt_of_ne_last_D m j hj
  simp only [typeDSimpleRoot, dif_pos hiv, dif_pos hjv]
  rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_basisVector_basisVector_D,
    dot_basisVector_basisVector_D, dot_basisVector_basisVector_D, dot_basisVector_basisVector_D]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> norm_num at * <;> omega

private lemma typeDSimpleRoot_dot_last (m : ℕ) (i : Fin (m + 2))
    (hi : i ≠ Fin.last (m + 1)) :
    dot (typeDSimpleRoot m i) (typeDSimpleRoot m (Fin.last (m + 1))) =
      if i.val + 2 = (Fin.last (m + 1)).val then -1 else 0 := by
  have hiv := val_lt_of_ne_last_D m i hi
  have hlast : ¬(Fin.last (m + 1)).val < m + 1 := by simp
  simp only [typeDSimpleRoot, dif_pos hiv, dif_neg hlast]
  rw [dot_sub_left, dot_add_right, dot_add_right,
    dot_basisVector_basisVector_D, dot_basisVector_basisVector_D,
    dot_basisVector_basisVector_D, dot_basisVector_basisVector_D]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> norm_num at * <;> omega

private lemma typeDSimpleRoot_last_dot (m : ℕ) (j : Fin (m + 2))
    (hj : j ≠ Fin.last (m + 1)) :
    dot (typeDSimpleRoot m (Fin.last (m + 1))) (typeDSimpleRoot m j) =
      if j.val + 2 = (Fin.last (m + 1)).val then -1 else 0 := by
  have hjv := val_lt_of_ne_last_D m j hj
  have hlast : ¬(Fin.last (m + 1)).val < m + 1 := by simp
  simp only [typeDSimpleRoot, dif_neg hlast, dif_pos hjv]
  rw [dot_add_left, dot_sub_right, dot_sub_right,
    dot_basisVector_basisVector_D, dot_basisVector_basisVector_D,
    dot_basisVector_basisVector_D, dot_basisVector_basisVector_D]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> norm_num at * <;> omega

/-- The displayed type `D` simple roots have the simply-laced Cartan pairing,
including the fork from the penultimate chain root to the terminal root. -/
public lemma typeDSimpleRoot_pairing (m : ℕ) (i j : Fin (m + 2)) :
    dot (typeDSimpleRoot m i) (typeDSimpleRoot m j) =
      if i = j then 2
      else if j = Fin.last (m + 1) then
        if i.val + 2 = j.val then -1 else 0
      else if i = Fin.last (m + 1) then
        if j.val + 2 = i.val then -1 else 0
      else if i.val + 1 = j.val then -1
      else if j.val + 1 = i.val then -1 else 0 := by
  by_cases hi : i = Fin.last (m + 1)
  · subst i
    by_cases hj : j = Fin.last (m + 1)
    · subst j
      have hlast : ¬(Fin.last (m + 1)).val < m + 1 := by simp
      simp only [typeDSimpleRoot, dif_neg hlast]
      rw [dot_add_left, dot_add_right, dot_add_right,
        dot_basisVector_basisVector_D, dot_basisVector_basisVector_D,
        dot_basisVector_basisVector_D, dot_basisVector_basisVector_D]
      norm_num
    · have hji : Fin.last (m + 1) ≠ j := Ne.symm hj
      rw [typeDSimpleRoot_last_dot m j hj]
      simp [hj, hji]
  · by_cases hj : j = Fin.last (m + 1)
    · subst j
      rw [typeDSimpleRoot_dot_last m i hi]
      simp [hi]
    · rw [typeDSimpleRoot_dot_of_ne_last m i j hi hj]
      simp [hi, hj]

open Set

public lemma typeDRootEmbedding_injective (n : ℕ) :
    Function.Injective (typeDRootEmbedding n) := by
  intro r q h
  have hval := congrArg Subtype.val h
  change typeDRootVector n r = typeDRootVector n q at hval
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  rcases q with ⟨⟨⟨k, l⟩, hkl⟩, u, v⟩
  have pairRoot_support (a b : Fin n) (hab : a < b)
      (x y : ({-1, 1} : Set ℝ)) :
      Function.support (fun c => x.1 • basisVector a c + y.1 • basisVector b c) =
        {a, b} := by
    have hx : x.1 ≠ 0 := by
      rcases x.2 with hx | hx <;> rw [hx] <;> norm_num
    have hy : y.1 ≠ 0 := by
      rcases y.2 with hy | hy <;> rw [hy] <;> norm_num
    ext c
    by_cases hca : c = a
    · subst c
      simp [Function.mem_support, basisVector, Pi.single_apply, hab.ne, hx]
    · by_cases hcb : c = b
      · subst c
        simp [Function.mem_support, basisVector, Pi.single_apply, hab.ne', hy]
      · simp [Function.mem_support, basisVector, Pi.single_apply, hca, hcb]
  have hsupp : ({i, j} : Set (Fin n)) = {k, l} := by
    rw [← pairRoot_support i j hij s t, ← pairRoot_support k l hkl u v]
    exact congrArg Function.support hval
  have hindices : i = k ∧ j = l := by
    rcases Set.pair_eq_pair_iff.mp hsupp with hdirect | ⟨hil, hjk⟩
    · exact hdirect
    · rw [hil, hjk] at hij
      exact False.elim (asymm hkl hij)
  obtain ⟨rfl, rfl⟩ := hindices
  have hs : s = u := by
    apply Subtype.ext
    have hi := congrFun hval i
    simpa [typeDRootVector, basisVector, hij.ne] using hi
  have ht : t = v := by
    apply Subtype.ext
    have hj := congrFun hval j
    simpa [typeDRootVector, basisVector, hij.ne] using hj
  simp [hs, ht]

open Set

public lemma typeDRootEmbedding_surjective (n : ℕ) :
    Function.Surjective (typeDRootEmbedding n) := by
  intro x
  rcases x with ⟨x, hx⟩
  change x ∈ pairRoots n at hx
  rcases hx with ⟨i, j, hij, s, t, hs, ht, hroot⟩
  by_cases hlt : i < j
  · let si : ({-1, 1} : Set ℝ) := ⟨s, hs⟩
    let ti : ({-1, 1} : Set ℝ) := ⟨t, ht⟩
    refine ⟨⟨⟨⟨i, j⟩, hlt⟩, si, ti⟩, ?_⟩
    apply Subtype.ext
    simp [typeDRootEmbedding, typeDRootVector, si, ti, hroot]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    let si : ({-1, 1} : Set ℝ) := ⟨t, ht⟩
    let ti : ({-1, 1} : Set ℝ) := ⟨s, hs⟩
    refine ⟨⟨⟨⟨j, i⟩, hji⟩, si, ti⟩, ?_⟩
    apply Subtype.ext
    simp [typeDRootEmbedding, typeDRootVector, si, ti, hroot, add_comm]

/-- The canonical Type D root index representing each displayed simple root. -/
@[expose] public noncomputable def typeDSimpleRootIndex (m : ℕ) (i : Fin (m + 2)) :
    TypeDRootIndex (m + 2) :=
  if h : i.val < m + 1 then
    ⟨⟨⟨i, ⟨i.val + 1, Nat.succ_lt_succ h⟩⟩, by
      change i.val < i.val + 1
      exact Nat.lt_succ_self _⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩
  else
    let left : Fin (m + 2) := ⟨m, by omega⟩
    let right : Fin (m + 2) := ⟨m + 1, by omega⟩
    ⟨⟨⟨left, right⟩, by
      change left.val < right.val
      simp [left, right]⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

private lemma basisVector_sub_dot_basisVector_sub {n : ℕ} (a b c d : Fin n) :
    dot (basisVector a - basisVector b) (basisVector c - basisVector d) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) -
      (if b = c then 1 else 0) + (if b = d then 1 else 0) := by
  classical
  rw [show dot (basisVector a - basisVector b) (basisVector c - basisVector d) =
      dot (basisVector a) (basisVector c - basisVector d) -
        dot (basisVector b) (basisVector c - basisVector d) by
      simp [dot, sub_mul, Finset.sum_sub_distrib]]
  simp [dot, basisVector, Pi.single_apply, eq_comm]
  ring

/-- The displayed type `A` simple roots have the path Gram matrix: diagonal entries are `2`,
adjacent entries are `-1`, and all other entries are zero. -/
public lemma typeASimpleRoot_dot_typeASimpleRoot (m : ℕ) (i j : Fin m) :
    dot (typeASimpleRoot m i) (typeASimpleRoot m j) =
      if i = j then 2 else if i.succ = j.castSucc then -1
      else if j.succ = i.castSucc then -1 else 0 := by
  simp only [typeASimpleRoot]
  rw [basisVector_sub_dot_basisVector_sub]
  by_cases hij : i = j
  · subst j
    have hself : i.succ ≠ i.castSucc := ne_of_gt i.castSucc_lt_succ
    norm_num [hself, hself.symm]
  · simp only [hij, ↓reduceIte]
    by_cases hforward : i.succ = j.castSucc
    · have hcross : i.castSucc ≠ j.succ := by
        intro h
        have hforwardVal := congrArg Fin.val hforward
        have hVal := congrArg Fin.val h
        simp at hforwardVal hVal
        omega
      have hjself : j.castSucc ≠ j.succ := ne_of_lt j.castSucc_lt_succ
      simp [hij, hforward, hcross, hjself]
    · simp only [hforward, ↓reduceIte]
      by_cases hbackward : j.succ = i.castSucc
      · have hiself : i.succ ≠ i.castSucc := ne_of_gt i.castSucc_lt_succ
        simp [hij, hbackward, hiself]
      · have hcross : i.castSucc ≠ j.succ := fun h => hbackward h.symm
        simp [hij, hbackward, hcross]

open Set

/-- The canonical type `B` root vectors span the full coordinate module because
all positive unit roots occur in the signed-unit branch. -/
public lemma typeBRootEmbedding_span_eq_top (n : ℕ) :
    Submodule.span ℝ (range (fun r : TypeBRootIndex n =>
      (typeBRootEmbedding n r : Vec n))) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun ℝ (Fin n))).mpr
  intro i
  have hi : (typeBRootEmbedding n (Sum.inr (i, false) : TypeBRootIndex n) : Vec n) ∈
      Submodule.span ℝ (range (fun r : TypeBRootIndex n =>
        (typeBRootEmbedding n r : Vec n))) :=
    Submodule.subset_span (mem_range_self (Sum.inr (i, false) : TypeBRootIndex n))
  simpa [typeBRootEmbedding, typeBRootVector, Pi.basisFun_apply, basisVector] using hi

open Set

public lemma typeBRootEmbedding_surjective (n : ℕ) :
    Function.Surjective (typeBRootEmbedding n) := by
  intro x
  rcases x with ⟨x, hx⟩
  change x ∈ pairRoots n ∪ signedUnitRoots n at hx
  rcases hx with hx | hx
  · rcases hx with ⟨i, j, hij, s, t, hs, ht, hroot⟩
    by_cases hlt : i < j
    · let si : ({-1, 1} : Set ℝ) := ⟨s, hs⟩
      let ti : ({-1, 1} : Set ℝ) := ⟨t, ht⟩
      refine ⟨.inl ⟨⟨⟨i, j⟩, hlt⟩, si, ti⟩, ?_⟩
      apply Subtype.ext
      simp [typeBRootEmbedding, typeBRootVector, si, ti, hroot]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      let si : ({-1, 1} : Set ℝ) := ⟨t, ht⟩
      let ti : ({-1, 1} : Set ℝ) := ⟨s, hs⟩
      refine ⟨.inl ⟨⟨⟨j, i⟩, hji⟩, si, ti⟩, ?_⟩
      apply Subtype.ext
      simp [typeBRootEmbedding, typeBRootVector, si, ti, hroot, add_comm]
  · rcases hx with ⟨i, hunit | hunit⟩
    · refine ⟨.inr (i, false), ?_⟩
      apply Subtype.ext
      simp [typeBRootEmbedding, typeBRootVector, hunit]
    · refine ⟨.inr (i, true), ?_⟩
      apply Subtype.ext
      simp [typeBRootEmbedding, typeBRootVector, hunit]

@[expose] public noncomputable def typeBSimpleRootIndex (m : ℕ) (i : Fin (m + 2)) :
    TypeBRootIndex (m + 2) :=
  if h : i.val < m + 1 then
    Sum.inl
      ⟨⟨⟨i, ⟨i.val + 1, Nat.succ_lt_succ h⟩⟩, by
        change i.val < i.val + 1
        exact Nat.lt_succ_self _⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩
  else
    Sum.inr (i, false)

public lemma typeBRootEmbedding_typeBSimpleRootIndex (m : ℕ) (i : Fin (m + 2)) :
    (typeBRootEmbedding (m + 2) (typeBSimpleRootIndex m i) : Vec (m + 2)) =
      typeBSimpleRoot m i := by
  by_cases h : i.val < m + 1
  · simp [typeBSimpleRootIndex, typeBRootEmbedding, typeBRootVector,
      typeBSimpleRoot, h, basisVector, sub_eq_add_neg]
  · simp [typeBSimpleRootIndex, typeBRootEmbedding, typeBRootVector,
      typeBSimpleRoot, h, basisVector]

open Set

/-- The canonical type `C` root vectors span the full coordinate module because
all positive double-unit roots occur in the signed-double-unit branch. -/
public lemma typeCRootEmbedding_span_eq_top (n : ℕ) :
    Submodule.span ℝ (range (fun r : TypeCRootIndex n =>
      (typeCRootEmbedding n r : Vec n))) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun ℝ (Fin n))).mpr
  intro i
  have hi : (typeCRootEmbedding n (Sum.inr (i, false) : TypeCRootIndex n) : Vec n) ∈
      Submodule.span ℝ (range (fun r : TypeCRootIndex n =>
        (typeCRootEmbedding n r : Vec n))) :=
    Submodule.subset_span (mem_range_self (Sum.inr (i, false) : TypeCRootIndex n))
  have hhalf := Submodule.smul_mem
    (Submodule.span ℝ (range (fun r : TypeCRootIndex n =>
      (typeCRootEmbedding n r : Vec n)))) (1 / 2 : ℝ) hi
  rw [show (Pi.basisFun ℝ (Fin n)) i =
      (1 / 2 : ℝ) •
        (typeCRootEmbedding n (Sum.inr (i, false) : TypeCRootIndex n) : Vec n) by
    ext j
    simp [typeCRootEmbedding, typeCRootVector, Pi.basisFun_apply, basisVector]]
  exact hhalf

open Set

public lemma typeCRootEmbedding_surjective (n : ℕ) :
    Function.Surjective (typeCRootEmbedding n) := by
  intro x
  rcases x with ⟨x, hx⟩
  change x ∈ pairRoots n ∪ signedDoubleUnitRoots n at hx
  rcases hx with hx | hx
  · rcases hx with ⟨i, j, hij, s, t, hs, ht, hroot⟩
    by_cases hlt : i < j
    · let si : ({-1, 1} : Set ℝ) := ⟨s, hs⟩
      let ti : ({-1, 1} : Set ℝ) := ⟨t, ht⟩
      refine ⟨.inl ⟨⟨⟨i, j⟩, hlt⟩, si, ti⟩, ?_⟩
      apply Subtype.ext
      simp [typeCRootEmbedding, typeCRootVector, si, ti, hroot]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      let si : ({-1, 1} : Set ℝ) := ⟨t, ht⟩
      let ti : ({-1, 1} : Set ℝ) := ⟨s, hs⟩
      refine ⟨.inl ⟨⟨⟨j, i⟩, hji⟩, si, ti⟩, ?_⟩
      apply Subtype.ext
      simp [typeCRootEmbedding, typeCRootVector, si, ti, hroot, add_comm]
  · rcases hx with ⟨i, hdouble | hdouble⟩
    · refine ⟨.inr (i, false), ?_⟩
      apply Subtype.ext
      simp [typeCRootEmbedding, typeCRootVector, hdouble]
    · refine ⟨.inr (i, true), ?_⟩
      apply Subtype.ext
      simp [typeCRootEmbedding, typeCRootVector, hdouble]

@[expose] public noncomputable def typeCSimpleRootIndex (m : ℕ) (i : Fin (m + 1)) :
    TypeCRootIndex (m + 1) :=
  if h : i.val < m then
    Sum.inl
      ⟨⟨⟨i, ⟨i.val + 1, Nat.succ_lt_succ h⟩⟩, by
        change i.val < i.val + 1
        exact Nat.lt_succ_self _⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩
  else
    Sum.inr (i, false)

/-- The standard type `C` Cartan matrix, oriented so the terminal long
simple root determines the reverse adjacent entry `-2`. -/
@[expose] public def typeCCartanMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  fun i j => if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i = Fin.last m then -2 else -1
    else 0

/-- The coordinate pairing of the displayed type `D` simple roots is the
standard type `D` Cartan matrix. -/
public lemma typeDSimpleRoot_pairing_eq_typeDCartanMatrix
    (m : ℕ) (i j : Fin (m + 2)) :
    dot (typeDSimpleRoot m i) (typeDSimpleRoot m j) = typeDCartanMatrix m i j := by
  simpa [typeDCartanMatrix] using typeDSimpleRoot_pairing m i j

open Set

@[expose] public noncomputable def typeDRootSpan (n : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (range (fun r : TypeDRootIndex n =>
    (typeDRootEmbedding n r : Vec n)))

@[expose] public noncomputable def typeDRootInSpan (n : ℕ) :
    TypeDRootIndex n ↪ typeDRootSpan n where
  toFun r := ⟨(typeDRootEmbedding n r : Vec n),
    Submodule.subset_span (mem_range_self r)⟩
  inj' := by
    intro r s h
    apply typeDRootEmbedding_injective n
    apply Subtype.ext
    exact congrArg (fun x : typeDRootSpan n => (x : Vec n)) h

@[expose] public noncomputable def typeDRootDotFunctional (n : ℕ) (r : TypeDRootIndex n) :
    Module.Dual ℝ (typeDRootSpan n) where
  toFun x := dot (typeDRootEmbedding n r : Vec n) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (typeDRootEmbedding n r : Vec n) i * (c * (x : Vec n) i) =
      c * ((typeDRootEmbedding n r : Vec n) i * (x : Vec n) i)
    ring

@[expose] public noncomputable def typeDRootFunctional (n : ℕ) (r : TypeDRootIndex n) :
    Module.Dual ℝ (typeDRootSpan n) :=
  typeDRootDotFunctional n r

@[expose] public noncomputable def typeDCorootVector (n : ℕ) (r : TypeDRootIndex n) : Vec n :=
  typeDRootEmbedding n r

open Set

/-- The canonical type `D_{m+2}` root vectors span the full coordinate module. -/
public lemma typeDRootEmbedding_span_eq_top (m : ℕ) :
    Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
      (typeDRootEmbedding (m + 2) r : Vec (m + 2)))) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun ℝ (Fin (m + 2)))).mpr
  intro i
  let last : Fin (m + 2) := Fin.last (m + 1)
  let zero : Fin (m + 2) := ⟨0, by omega⟩
  let pos : ({-1, 1} : Set ℝ) := ⟨1, by simp⟩
  let neg : ({-1, 1} : Set ℝ) := ⟨-1, by simp⟩
  by_cases hi : i = last
  · have hzeroLast : zero < last := by
      change 0 < m + 1
      omega
    let r₁ : TypeDRootIndex (m + 2) :=
      ⟨⟨⟨zero, last⟩, hzeroLast⟩, pos, pos⟩
    let r₂ : TypeDRootIndex (m + 2) :=
      ⟨⟨⟨zero, last⟩, hzeroLast⟩, neg, pos⟩
    have h₁ : (typeDRootEmbedding (m + 2) r₁ : Vec (m + 2)) ∈
        Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
          (typeDRootEmbedding (m + 2) r : Vec (m + 2)))) :=
      Submodule.subset_span (mem_range_self r₁)
    have h₂ : (typeDRootEmbedding (m + 2) r₂ : Vec (m + 2)) ∈
        Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
          (typeDRootEmbedding (m + 2) r : Vec (m + 2)))) :=
      Submodule.subset_span (mem_range_self r₂)
    have hhalf := Submodule.smul_mem
      (Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
        (typeDRootEmbedding (m + 2) r : Vec (m + 2)))))
      (1 / 2 : ℝ) (Submodule.add_mem _ h₁ h₂)
    rw [show (Pi.basisFun ℝ (Fin (m + 2))) i =
        (1 / 2 : ℝ) • ((typeDRootEmbedding (m + 2) r₁ : Vec (m + 2)) +
          (typeDRootEmbedding (m + 2) r₂ : Vec (m + 2))) by
      subst i
      simp only [Pi.basisFun_apply]
      change basisVector last = (1 / 2 : ℝ) •
        (typeDRootVector (m + 2) r₁ + typeDRootVector (m + 2) r₂)
      simp [r₁, r₂, typeDRootVector, pos, neg]
      module]
    exact hhalf
  · have hiLast : i < last := by
      change i.val < m + 1
      have hine : i.val ≠ m + 1 := by
        intro hval
        apply hi
        apply Fin.ext
        simpa [last] using hval
      omega
    let r₁ : TypeDRootIndex (m + 2) :=
      ⟨⟨⟨i, last⟩, hiLast⟩, pos, pos⟩
    let r₂ : TypeDRootIndex (m + 2) :=
      ⟨⟨⟨i, last⟩, hiLast⟩, pos, neg⟩
    have h₁ : (typeDRootEmbedding (m + 2) r₁ : Vec (m + 2)) ∈
        Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
          (typeDRootEmbedding (m + 2) r : Vec (m + 2)))) :=
      Submodule.subset_span (mem_range_self r₁)
    have h₂ : (typeDRootEmbedding (m + 2) r₂ : Vec (m + 2)) ∈
        Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
          (typeDRootEmbedding (m + 2) r : Vec (m + 2)))) :=
      Submodule.subset_span (mem_range_self r₂)
    have hhalf := Submodule.smul_mem
      (Submodule.span ℝ (range (fun r : TypeDRootIndex (m + 2) =>
        (typeDRootEmbedding (m + 2) r : Vec (m + 2)))))
      (1 / 2 : ℝ) (Submodule.add_mem _ h₁ h₂)
    rw [show (Pi.basisFun ℝ (Fin (m + 2))) i =
        (1 / 2 : ℝ) • ((typeDRootEmbedding (m + 2) r₁ : Vec (m + 2)) +
          (typeDRootEmbedding (m + 2) r₂ : Vec (m + 2))) by
      simp only [Pi.basisFun_apply]
      change basisVector i = (1 / 2 : ℝ) •
        (typeDRootVector (m + 2) r₁ + typeDRootVector (m + 2) r₂)
      simp [r₁, r₂, typeDRootVector, pos, neg]
      module]
    exact hhalf

public lemma typeDRootEmbedding_typeDSimpleRootIndex
    (m : ℕ) (i : Fin (m + 2)) :
    (typeDRootEmbedding (m + 2) (typeDSimpleRootIndex m i) : Vec (m + 2)) =
      typeDSimpleRoot m i := by
  by_cases h : i.val < m + 1
  · simp [typeDSimpleRootIndex, typeDRootEmbedding, typeDRootVector,
      typeDSimpleRoot, h, basisVector, sub_eq_add_neg]
  · simp [typeDSimpleRootIndex, typeDRootEmbedding, typeDRootVector,
      typeDSimpleRoot, h, basisVector]

open Set

/-- Ordered unequal endpoint pairs indexing the roots `e_i - e_j` of type `A_m`. -/
public abbrev TypeARootIndex (m : ℕ) :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1 ≠ p.2}

/-- The indexed coordinate roots `e_i - e_j` of type `A_m`. -/
@[expose] public noncomputable def typeARootEmbedding (m : ℕ) : TypeARootIndex m ↪ Vec (m + 1) where
  toFun r := basisVector r.1.1 - basisVector r.1.2
  inj' := by
    intro r s h
    have hfirst : r.1.1 = s.1.1 := by
      by_contra hrs
      by_cases hcross : r.1.1 = s.1.2
      · have hsr : s.1.2 ≠ r.1.2 := by
          intro hsr
          exact r.2 (hcross.trans hsr)
        have heval := congrFun h r.1.1
        norm_num [basisVector, Pi.single_apply, r.2, s.2, hrs, hcross, hsr] at heval
      · have heval := congrFun h r.1.1
        norm_num [basisVector, Pi.single_apply, r.2, hrs, hcross] at heval
    have hsecond : r.1.2 = s.1.2 := by
      have heval := congrFun h r.1.2
      by_contra hrs
      norm_num [basisVector, Pi.single_apply, r.2, s.2, hfirst, hrs] at heval
    apply Subtype.ext
    exact Prod.ext hfirst hsecond

@[simp] public lemma typeARootEmbedding_apply (m : ℕ) (r : TypeARootIndex m) :
    typeARootEmbedding m r = basisVector r.1.1 - basisVector r.1.2 := rfl

/-- Dot pairing of two coordinate roots, expressed by their four endpoint incidences. -/
public lemma typeARoot_dot_typeARoot {n : ℕ} (a b c d : Fin n) :
    dot (basisVector a - basisVector b) (basisVector c - basisVector d) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) -
      (if b = c then 1 else 0) + (if b = d then 1 else 0) := by
  classical
  rw [show dot (basisVector a - basisVector b) (basisVector c - basisVector d) =
      dot (basisVector a) (basisVector c - basisVector d) -
        dot (basisVector b) (basisVector c - basisVector d) by
      simp [dot, sub_mul, Finset.sum_sub_distrib]]
  simp [dot, basisVector, Pi.single_apply, eq_comm]
  ring

/-- Dot pairing of two indexed coordinate roots, expressed by endpoint incidences. -/
public lemma typeARootEmbedding_dot (m : ℕ) (r s : TypeARootIndex m) :
    dot (typeARootEmbedding m r) (typeARootEmbedding m s) =
      (if r.1.1 = s.1.1 then 1 else 0) - (if r.1.1 = s.1.2 then 1 else 0) -
      (if r.1.2 = s.1.1 then 1 else 0) + (if r.1.2 = s.1.2 then 1 else 0) := by
  change dot (basisVector r.1.1 - basisVector r.1.2)
    (basisVector s.1.1 - basisVector s.1.2) = _
  exact typeARoot_dot_typeARoot r.1.1 r.1.2 s.1.1 s.1.2

/-- Reflection in the coordinate root `e_a - e_b` swaps the endpoint coordinates of every
coordinate root. -/
public lemma typeARoot_reflection_eq_swap {n : ℕ} (a b c d : Fin n) (hab : a ≠ b) :
    (basisVector c - basisVector d) -
        dot (basisVector a - basisVector b) (basisVector c - basisVector d) •
          (basisVector a - basisVector b) =
      basisVector (Equiv.swap a b c) - basisVector (Equiv.swap a b d) := by
  classical
  rw [typeARoot_dot_typeARoot]
  have hba : b ≠ a := hab.symm
  by_cases hca : c = a
  · subst c
    by_cases hda : d = a
    · subst d
      simp
    · have had : a ≠ d := fun h => hda h.symm
      by_cases hdb : d = b
      · subst d
        simp [hab, hba, Equiv.swap_apply_left, Equiv.swap_apply_right]
        module
      · have hbd : b ≠ d := fun h => hdb h.symm
        rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hda hdb]
        simp only [if_neg had, if_neg hba, if_neg hbd, if_true, sub_zero]
        module
  · have hac : a ≠ c := fun h => hca h.symm
    by_cases hcb : c = b
    · subst c
      by_cases hda : d = a
      · subst d
        simp [hab, hba, Equiv.swap_apply_left, Equiv.swap_apply_right]
        module
      · have had : a ≠ d := fun h => hda h.symm
        by_cases hdb : d = b
        · subst d
          simp
        · have hbd : b ≠ d := fun h => hdb h.symm
          rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hda hdb]
          simp only [if_neg hab, if_neg had, if_neg hbd, if_true, zero_sub, sub_self, add_zero]
          module
    · have hbc : b ≠ c := fun h => hcb h.symm
      by_cases hda : d = a
      · subst d
        rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
        simp only [if_neg hac, if_neg hbc, if_neg hba, if_true, zero_sub, sub_zero, add_zero]
        module
      · have had : a ≠ d := fun h => hda h.symm
        by_cases hdb : d = b
        · subst d
          rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right]
          simp only [if_neg hac, if_neg hab, if_neg hbc, if_true, sub_zero]
          module
        · have hbd : b ≠ d := fun h => hdb h.symm
          rw [Equiv.swap_apply_of_ne_of_ne hca hcb,
            Equiv.swap_apply_of_ne_of_ne hda hdb]
          simp only [if_neg hac, if_neg had, if_neg hbc, if_neg hbd, sub_zero, zero_add,
            zero_smul]

/-- The coordinate reflection in any indexed type `A` root preserves the indexed root range.
This includes closure under every displayed simple-root reflection. -/
public lemma typeARoot_reflection_mapsTo (m : ℕ) (r : TypeARootIndex m) :
    MapsTo
      (fun x => x - dot (typeARootEmbedding m r) x • typeARootEmbedding m r)
      (range (typeARootEmbedding m)) (range (typeARootEmbedding m)) := by
  rintro _ ⟨s, rfl⟩
  let t : TypeARootIndex m :=
    ⟨(Equiv.swap r.1.1 r.1.2 s.1.1, Equiv.swap r.1.1 r.1.2 s.1.2),
      fun h => s.2 ((Equiv.swap r.1.1 r.1.2).injective h)⟩
  refine ⟨t, ?_⟩
  exact (typeARoot_reflection_eq_swap r.1.1 r.1.2 s.1.1 s.1.2 r.2).symm

/-- The real span of the coordinate roots of type `A_m`. -/
@[expose] public noncomputable def typeARootSpan (m : ℕ) : Submodule ℝ (Vec (m + 1)) :=
  Submodule.span ℝ (range (typeARootEmbedding m))

/-- The coordinate roots regarded as vectors in their own span. -/
@[expose] public noncomputable def typeARootInSpan (m : ℕ) : TypeARootIndex m ↪ typeARootSpan m where
  toFun r := ⟨typeARootEmbedding m r, Submodule.subset_span (mem_range_self r)⟩
  inj' := fun _ _ h => (typeARootEmbedding m).injective (Subtype.ext_iff.mp h)

@[simp] public lemma typeARootInSpan_val (m : ℕ) (r : TypeARootIndex m) :
    (typeARootInSpan m r : Vec (m + 1)) = typeARootEmbedding m r := rfl

/-- The dot-product functional associated to an indexed type `A` root. -/
public noncomputable def typeARootFunctional (m : ℕ) (r : TypeARootIndex m) :
    Module.Dual ℝ (typeARootSpan m) where
  toFun x := dot (typeARootEmbedding m r) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (typeARootEmbedding m r) i * (c * (x : Vec (m + 1)) i) =
      c * ((typeARootEmbedding m r) i * (x : Vec (m + 1)) i)
    ring

/-- The coordinate dot product is symmetric. -/
public lemma dot_comm {n : ℕ} (x y : Vec n) : dot x y = dot y x := by
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- Distinct coordinate roots induce distinct dot-product functionals on their root span. -/
public lemma typeARootFunctional_injective (m : ℕ) :
    Function.Injective (typeARootFunctional m) := by
  intro r s h
  apply (typeARootEmbedding m).injective
  let x : typeARootSpan m := typeARootInSpan m r - typeARootInSpan m s
  have hx : dot (typeARootEmbedding m r - typeARootEmbedding m s)
      (typeARootEmbedding m r - typeARootEmbedding m s) = 0 := by
    have heval := LinearMap.congr_fun h x
    dsimp [typeARootFunctional, x, typeARootInSpan] at heval
    rw [show dot (typeARootEmbedding m r - typeARootEmbedding m s)
        (typeARootEmbedding m r - typeARootEmbedding m s) =
      dot (typeARootEmbedding m r) (typeARootEmbedding m r - typeARootEmbedding m s) -
      dot (typeARootEmbedding m s) (typeARootEmbedding m r - typeARootEmbedding m s) by
        simp [dot, sub_mul, Finset.sum_sub_distrib]]
    exact sub_eq_zero.mpr heval
  apply sub_eq_zero.mp
  funext i
  have hsum : ∑ j, ((typeARootEmbedding m r - typeARootEmbedding m s) j) *
      ((typeARootEmbedding m r - typeARootEmbedding m s) j) = 0 := hx
  have hall := (Finset.sum_mul_self_eq_zero_iff Finset.univ
    (fun j => (typeARootEmbedding m r - typeARootEmbedding m s) j)).mp (by simpa using hsum)
  simpa using hall i (Finset.mem_univ i)

/-- The coroot embedding obtained from dot-product functionals on the type `A` root span. -/
public noncomputable def typeACorootEmbedding (m : ℕ) :
    TypeARootIndex m ↪ Module.Dual ℝ (typeARootSpan m) :=
  ⟨typeARootFunctional m, typeARootFunctional_injective m⟩

/-- Evaluating an indexed type `A` coroot on an indexed root is their coordinate dot product. -/
public lemma typeARootInSpan_coroot_eval_apply (m : ℕ) (r s : TypeARootIndex m) :
    Module.Dual.eval ℝ (typeARootSpan m) (typeARootInSpan m r)
      (typeACorootEmbedding m s) = dot (typeARootEmbedding m r) (typeARootEmbedding m s) := by
  simp [Module.Dual.eval_apply, typeARootInSpan, typeACorootEmbedding, typeARootFunctional]
  exact dot_comm _ _

/-- Every indexed type `A` root pairs to `2` with its corresponding dot-product coroot. -/
public lemma typeARootInSpan_coroot_eval (m : ℕ) (r : TypeARootIndex m) :
    Module.Dual.eval ℝ (typeARootSpan m) (typeARootInSpan m r)
      (typeACorootEmbedding m r) = 2 := by
  rw [typeARootInSpan_coroot_eval_apply]
  change dot (basisVector r.1.1 - basisVector r.1.2)
    (basisVector r.1.1 - basisVector r.1.2) = 2
  rw [typeARoot_dot_typeARoot]
  norm_num [r.2, r.2.symm]

/-- Coordinate-root reflection closure lifted from vectors to their root span. -/
public lemma typeARootInSpan_reflection_mapsTo (m : ℕ) (r : TypeARootIndex m) :
    MapsTo
      (Module.preReflection (typeARootInSpan m r)
        ((Module.Dual.eval ℝ (typeARootSpan m)).flip (typeACorootEmbedding m r)))
      (range (typeARootInSpan m)) (range (typeARootInSpan m)) := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := typeARoot_reflection_mapsTo m r (mem_range_self s)
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change typeARootEmbedding m t =
    typeARootEmbedding m s - dot (typeARootEmbedding m r) (typeARootEmbedding m s) •
      typeARootEmbedding m r
  exact ht

/-- The indexed coordinate roots span their ambient type `A` root space. -/
public lemma typeARootInSpan_span_eq_top (m : ℕ) :
    Submodule.span ℝ (range (typeARootInSpan m)) = ⊤ := by
  apply top_unique
  intro x hx
  refine Submodule.span_induction
    (p := fun y hy => (⟨y, hy⟩ : typeARootSpan m) ∈
      Submodule.span ℝ (range (typeARootInSpan m))) ?_ ?_ ?_ ?_ x.property
  · intro y hy
    obtain ⟨r, rfl⟩ := hy
    exact Submodule.subset_span (mem_range_self r)
  · exact Submodule.zero_mem _
  · intro x y hx hy hxm hym
    exact Submodule.add_mem _ hxm hym
  · intro c x hx hxm
    exact Submodule.smul_mem _ c hxm

public lemma typeCRootEmbedding_typeCSimpleRootIndex (m : ℕ) (i : Fin (m + 1)) :
    (typeCRootEmbedding (m + 1) (typeCSimpleRootIndex m i) : Vec (m + 1)) =
      typeCSimpleRoot m i := by
  by_cases h : i.val < m
  · simp [typeCSimpleRootIndex, typeCRootEmbedding, typeCRootVector,
      typeCSimpleRoot, h, basisVector, sub_eq_add_neg]
  · simp [typeCSimpleRootIndex, typeCRootEmbedding, typeCRootVector,
      typeCSimpleRoot, h, basisVector]

/-- A path with the displayed terminal reverse double bond is the standard
type `C` Cartan matrix.  The hypotheses expose only matrix entries and carry
no classification conclusion. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_pathGraph_eq_typeCCartanMatrix_of_entries
    {κ : Type*} (A : Matrix κ κ ℤ) {m : ℕ} (e : Fin (m + 1) ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hforward : ∀ {i j : Fin (m + 1)}, i.val + 1 = j.val →
      A (e i) (e j) = -1)
    (hreverse : ∀ {i j : Fin (m + 1)}, j.val + 1 = i.val →
      A (e i) (e j) = if i = Fin.last m then -2 else -1)
    (hzero : ∀ {i j : Fin (m + 1)}, i ≠ j → i.val + 1 ≠ j.val →
      j.val + 1 ≠ i.val → A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeCCartanMatrix m i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeCCartanMatrix] using hdiag i
  by_cases hforward' : i.val + 1 = j.val
  · rw [typeCCartanMatrix, if_neg hij, if_pos hforward']
    exact hforward hforward'
  by_cases hreverse' : j.val + 1 = i.val
  · rw [typeCCartanMatrix, if_neg hij, if_neg hforward', if_pos hreverse']
    exact hreverse hreverse'
  rw [typeCCartanMatrix, if_neg hij, if_neg hforward', if_neg hreverse']
  exact hzero hij hforward' hreverse'

/-- A matrix with the displayed chain-and-fork entries is the standard type `D`
Cartan matrix.  The parameter `m = 2` gives `D₄`. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_forkGraph_eq_typeDCartanMatrix_of_entries
    {κ : Type*} (A : Matrix κ κ ℤ) {m : ℕ} (e : Fin (m + 2) ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hbranchForward : ∀ {i j : Fin (m + 2)},
      j = Fin.last (m + 1) → i.val + 2 = j.val → A (e i) (e j) = -1)
    (hbranchReverse : ∀ {i j : Fin (m + 2)},
      i = Fin.last (m + 1) → j.val + 2 = i.val → A (e i) (e j) = -1)
    (hchainForward : ∀ {i j : Fin (m + 2)},
      j ≠ Fin.last (m + 1) →
      i.val + 1 = j.val → A (e i) (e j) = -1)
    (hchainReverse : ∀ {i j : Fin (m + 2)},
      i ≠ Fin.last (m + 1) →
      j.val + 1 = i.val → A (e i) (e j) = -1)
    (hzeroBranchForward : ∀ {i j : Fin (m + 2)},
      i ≠ j →
      j = Fin.last (m + 1) → i.val + 2 ≠ j.val → A (e i) (e j) = 0)
    (hzeroBranchReverse : ∀ {i j : Fin (m + 2)},
      i ≠ j →
      i = Fin.last (m + 1) → j.val + 2 ≠ i.val → A (e i) (e j) = 0)
    (hzeroInterior : ∀ {i j : Fin (m + 2)}, i ≠ j →
      j ≠ Fin.last (m + 1) → i ≠ Fin.last (m + 1) →
      i.val + 1 ≠ j.val → j.val + 1 ≠ i.val →
      A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeDCartanMatrix m i j := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeDCartanMatrix] using hdiag i
  by_cases hjlast : j = Fin.last (m + 1)
  · by_cases hsum : i.val + 2 = j.val
    · have hilast : i ≠ Fin.last (m + 1) := by
        intro hi
        exact hij (hi.trans hjlast.symm)
      simpa [typeDCartanMatrix, hij, hjlast, hsum, hilast] using
        hbranchForward hjlast hsum
    · simp only [typeDCartanMatrix, hjlast]
      have hilast : i ≠ Fin.last (m + 1) := by
        intro hi
        exact hij (hi.trans hjlast.symm)
      have hsum' : i.val + 2 ≠ m + 1 := by
        simpa [hjlast] using hsum
      simpa [typeDCartanMatrix, hij, hjlast, hilast, hsum, hsum'] using
        hzeroBranchForward hij hjlast hsum
  by_cases hilast : i = Fin.last (m + 1)
  · by_cases hsum : j.val + 2 = i.val
    · have hjlast' : j ≠ Fin.last (m + 1) := by
        intro hj
        exact hij (hilast.trans hj.symm)
      have hjlast'' : Fin.last (m + 1) ≠ j := Ne.symm hjlast'
      simpa [typeDCartanMatrix, hij, hjlast, hilast, hsum, hjlast', hjlast''] using
        hbranchReverse hilast hsum
    · simp only [typeDCartanMatrix, hjlast, hilast]
      have hjlast' : j ≠ Fin.last (m + 1) := by
        intro hj
        exact hij (hilast.trans hj.symm)
      have hjlast'' : Fin.last (m + 1) ≠ j := Ne.symm hjlast'
      have hsum' : j.val + 2 ≠ m + 1 := by
        simpa [hilast] using hsum
      simpa [typeDCartanMatrix, hij, hjlast, hilast, hjlast', hjlast'', hsum, hsum'] using
        hzeroBranchReverse hij hilast hsum
  by_cases hnext : i.val + 1 = j.val
  · simpa [typeDCartanMatrix, hij, hjlast, hilast, hnext] using
      hchainForward hjlast hnext
  by_cases hprev : j.val + 1 = i.val
  · simpa [typeDCartanMatrix, hij, hjlast, hilast, hnext, hprev] using
      hchainReverse hilast hprev
  · simp only [typeDCartanMatrix, hij, hjlast, hilast, hnext, hprev]
    exact hzeroInterior hij hjlast hilast hnext hprev

public lemma typeDCorootVector_injective (n : ℕ) :
    Function.Injective (typeDCorootVector n) := by
  intro r s h
  apply typeDRootEmbedding_injective n
  apply Subtype.ext
  change (typeDRootEmbedding n r : Vec n) = (typeDRootEmbedding n s : Vec n) at h
  exact h

public lemma typeDRootFunctional_apply (n : ℕ) (r : TypeDRootIndex n)
    (x : typeDRootSpan n) :
    typeDRootFunctional n r x = dot (typeDCorootVector n r) x.1 := by
  rfl

public lemma typeDRootInSpan_coroot_eval (n : ℕ) (r : TypeDRootIndex n) :
    Module.Dual.eval ℝ (typeDRootSpan n) (typeDRootInSpan n r)
      (typeDRootFunctional n r) = 2 := by
  classical
  have dot_add_right (x y z : Vec n) : dot x (y + z) = dot x y + dot x z := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  have dot_smul_right (x y : Vec n) (c : ℝ) : dot x (c • y) = c * dot x y := by
    simp [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have dot_add_left (x y z : Vec n) : dot (x + y) z = dot x z + dot y z := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  have dot_smul_left (x y : Vec n) (c : ℝ) : dot (c • x) y = c * dot x y := by
    simp [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have dot_basisVector_basisVector (i j : Fin n) :
      dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
    simp [dot, basisVector, Pi.single_apply, eq_comm]
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  simp only [Module.Dual.eval_apply, typeDRootFunctional, typeDRootDotFunctional,
    typeDRootInSpan, typeDRootEmbedding, typeDRootVector]
  change dot (s.1 • basisVector i + t.1 • basisVector j)
    (s.1 • basisVector i + t.1 • basisVector j) = 2
  rcases s.2 with hs | hs <;> rcases t.2 with ht | ht <;>
    rw [hs, ht, dot_add_left, dot_smul_left, dot_smul_left,
      dot_add_right, dot_add_right, dot_smul_right, dot_smul_right,
      dot_smul_right, dot_smul_right] <;>
    simp [dot_basisVector_basisVector, hij.ne, hij.ne'] <;> norm_num

public lemma typeDRootInSpan_coroot_eval_apply (n : ℕ) (r s : TypeDRootIndex n) :
    Module.Dual.eval ℝ (typeDRootSpan n) (typeDRootInSpan n r)
      (typeDRootFunctional n s) =
      dot (typeDRootEmbedding n s : Vec n) (typeDRootEmbedding n r : Vec n) := by
  change dot (typeDRootEmbedding n s : Vec n)
      (typeDRootEmbedding n r : Vec n) = _
  rfl

open Set

/-- The canonical type `D` roots span their defining root span. -/
public lemma typeDRootInSpan_span_eq_top (n : ℕ) :
    Submodule.span ℝ (range (typeDRootInSpan n)) = ⊤ := by
  apply top_unique
  intro x hx
  refine Submodule.span_induction
    (p := fun y hy => (⟨y, hy⟩ : typeDRootSpan n) ∈
      Submodule.span ℝ (range (typeDRootInSpan n))) ?_ ?_ ?_ ?_ x.property
  · intro y hy
    obtain ⟨r, rfl⟩ := hy
    exact Submodule.subset_span (mem_range_self r)
  · exact Submodule.zero_mem _
  · intro y z hy hz hym hzm
    exact Submodule.add_mem _ hym hzm
  · intro c y hy hym
    exact Submodule.smul_mem _ c hym

@[simp] public lemma typeDRootInSpan_val (n : ℕ) (r : TypeDRootIndex n) :
    (typeDRootInSpan n r : Vec n) = (typeDRootEmbedding n r : Vec n) := by
  simp [typeDRootInSpan]

open Set

/-- In rank at least two, distinct canonical type `D` roots define distinct
dot-product coroot functionals on the root span. -/
public lemma typeDRootFunctional_injective (m : ℕ) :
    Function.Injective (typeDRootFunctional (m + 2)) := by
  intro r s h
  apply typeDRootEmbedding_injective (m + 2)
  apply Subtype.ext
  funext i
  have hi : basisVector i ∈ typeDRootSpan (m + 2) := by
    change basisVector i ∈ Submodule.span ℝ (range (fun q : TypeDRootIndex (m + 2) =>
      (typeDRootEmbedding (m + 2) q : Vec (m + 2))))
    rw [typeDRootEmbedding_span_eq_top]
    exact Submodule.mem_top
  have heval := LinearMap.congr_fun h (⟨basisVector i, hi⟩ : typeDRootSpan (m + 2))
  change dot (typeDRootEmbedding (m + 2) r : Vec (m + 2)) (basisVector i) =
    dot (typeDRootEmbedding (m + 2) s : Vec (m + 2)) (basisVector i) at heval
  simpa [dot, basisVector, Pi.single_apply] using heval

/-- The canonical type `D` simple indices have the standard Cartan pairing in
the embedding order used by the concrete root pairing. -/
public lemma typeDRootEmbedding_simpleIndex_pairing
    (m : ℕ) (i j : Fin (m + 2)) :
    dot (typeDRootEmbedding (m + 2) (typeDSimpleRootIndex m j) : Vec (m + 2))
        (typeDRootEmbedding (m + 2) (typeDSimpleRootIndex m i) : Vec (m + 2)) =
      typeDCartanMatrix m i j := by
  rw [typeDRootEmbedding_typeDSimpleRootIndex,
    typeDRootEmbedding_typeDSimpleRootIndex]
  calc
    dot (typeDSimpleRoot m j) (typeDSimpleRoot m i) =
        dot (typeDSimpleRoot m i) (typeDSimpleRoot m j) := by
      simp only [dot]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_comm]
    _ = typeDCartanMatrix m i j :=
      typeDSimpleRoot_pairing_eq_typeDCartanMatrix m i j

open Set

/-- The concrete coordinate root pairing of type `A_m`, indexed by ordered unequal endpoint
pairs and living in the real span of its roots. -/
@[expose] public noncomputable def typeARootPairing (m : ℕ) :
    RootPairing (TypeARootIndex m) ℝ (typeARootSpan m) (Module.Dual ℝ (typeARootSpan m)) :=
  RootPairing.mk'' (Module.Dual.eval ℝ (typeARootSpan m)) (typeARootInSpan m)
    (typeACorootEmbedding m) (typeARootInSpan_coroot_eval m)
    (typeARootInSpan_reflection_mapsTo m) (typeARootInSpan_span_eq_top m)

@[simp] public lemma typeARootPairing_root (m : ℕ) (r : TypeARootIndex m) :
    (typeARootPairing m).root r = typeARootInSpan m r := rfl

/-- Pairing in the concrete type `A` root pairing is the coordinate dot product. -/
@[simp] public lemma typeARootPairing_pairing (m : ℕ) (r s : TypeARootIndex m) :
    (typeARootPairing m).pairing r s =
      dot (typeARootEmbedding m r) (typeARootEmbedding m s) := by
  change Module.Dual.eval ℝ (typeARootSpan m) (typeARootInSpan m r)
    (typeACorootEmbedding m s) = _
  exact typeARootInSpan_coroot_eval_apply m r s

public instance typeARootPairing_isRootSystem (m : ℕ) : (typeARootPairing m).IsRootSystem := by
  apply RootPairing.isRootSystem_mk''
  intro r s
  let z : ℤ :=
    (if r.1.1 = s.1.1 then 1 else 0) - (if r.1.1 = s.1.2 then 1 else 0) -
      (if r.1.2 = s.1.1 then 1 else 0) + (if r.1.2 = s.1.2 then 1 else 0)
  refine ⟨z, ?_⟩
  rw [typeARootInSpan_coroot_eval_apply]
  rw [typeARootEmbedding_dot]
  simp [z]

public instance typeARootPairing_isCrystallographic (m : ℕ) :
    (typeARootPairing m).IsCrystallographic := by
  constructor
  intro r s
  let z : ℤ :=
    (if r.1.1 = s.1.1 then 1 else 0) - (if r.1.1 = s.1.2 then 1 else 0) -
      (if r.1.2 = s.1.1 then 1 else 0) + (if r.1.2 = s.1.2 then 1 else 0)
  refine ⟨z, ?_⟩
  rw [typeARootPairing_pairing]
  rw [typeARootEmbedding_dot]
  simp [z]

public instance typeARootPairing_isReduced (m : ℕ) : (typeARootPairing m).IsReduced := by
  constructor
  intro r s hdep
  have hsmul := (typeARootPairing m).pairing_smul_root_eq_of_not_linearIndependent hdep
  have hsymm : (typeARootPairing m).pairing r s = (typeARootPairing m).pairing s r := by
    rw [typeARootPairing_pairing, typeARootPairing_pairing]
    exact dot_comm _ _
  have hprod : (typeARootPairing m).pairing s r * (typeARootPairing m).pairing s r = 4 := by
    have h := congrArg (fun x => (typeARootPairing m).toLinearMap x
      ((typeARootPairing m).coroot s)) hsmul
    have h' : (typeARootPairing m).pairing s r * (typeARootPairing m).pairing r s =
        (2 : ℝ) * 2 := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      rw [RootPairing.root_coroot_eq_pairing, RootPairing.root_coroot_eq_pairing] at h
      rw [RootPairing.pairing_same] at h
      exact h
    rw [hsymm] at h'
    norm_num at h' ⊢
    exact h'
  have hc : (typeARootPairing m).pairing s r = 2 ∨
      (typeARootPairing m).pairing s r = -2 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    calc
      ((typeARootPairing m).pairing s r) ^ 2 =
          (typeARootPairing m).pairing s r * (typeARootPairing m).pairing s r := by rw [pow_two]
      _ = 4 := hprod
      _ = (2 : ℝ) ^ 2 := by norm_num
  rcases hc with hc | hc
  · left
    rw [hc] at hsmul
    exact (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
  · right
    rw [hc] at hsmul
    have hsmul' : -((2 : ℝ) • (typeARootPairing m).root r) =
        (2 : ℝ) • (typeARootPairing m).root s := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul] at hsmul
      exact hsmul
    have hs : (2 : ℝ) • (-(typeARootPairing m).root r) =
        (2 : ℝ) • (typeARootPairing m).root s := by
      rw [smul_neg]
      exact hsmul'
    have hneg : -(typeARootPairing m).root r = (typeARootPairing m).root s :=
      (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hs
    exact neg_eq_iff_eq_neg.mp hneg

open Set

/-- The two length-dependent reflection formulas of the standard type `B` roots
preserve the full type `B` root set. -/
public lemma typeBRoot_reflection_mapsTo (n : ℕ) :
    (∀ r ∈ pairRoots n,
      MapsTo (fun x => x - dot r x • r) (typeBRoots n) (typeBRoots n)) ∧
    ∀ r ∈ signedUnitRoots n,
      MapsTo (fun x => x - (2 * dot r x) • r) (typeBRoots n) (typeBRoots n) := by
  classical
  have hdot_add (r x y : Vec n) : dot r (x + y) = dot r x + dot r y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  have hdot_smul (r x : Vec n) (s : ℝ) : dot r (s • x) = s * dot r x := by
    simp [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdot_neg (r x : Vec n) : dot r (-x) = -dot r x := by
    calc
      dot r (-x) = dot r ((-1 : ℝ) • x) := by simp
      _ = (-1 : ℝ) * dot r x := hdot_smul r x (-1)
      _ = -dot r x := by ring
  have hdot_left_neg (r x : Vec n) : dot (-r) x = -dot r x := by
    rw [dot_comm, hdot_neg, dot_comm]
  have hreflect_neg (r x : Vec n) :
      x - dot (-r) x • (-r) = x - dot r x • r := by
    rw [hdot_left_neg]
    module
  have hreflect_neg_fun (r : Vec n) :
      (fun x => x - dot (-r) x • (-r)) = (fun x => x - dot r x • r) := by
    funext x
    exact hreflect_neg r x
  have hreflect_decomp (r x y : Vec n) (s t : ℝ) :
      (s • x + t • y) - dot r (s • x + t • y) • r =
        s • (x - dot r x • r) + t • (y - dot r y • r) := by
    rw [hdot_add, hdot_smul, hdot_smul]
    module
  have hreflect_decomp_two (r x y : Vec n) (s t : ℝ) :
      (s • x + t • y) - (2 * dot r (s • x + t • y)) • r =
        s • (x - (2 * dot r x) • r) + t • (y - (2 * dot r y) • r) := by
    rw [hdot_add, hdot_smul, hdot_smul]
    module
  have hsum_basis (a b c : Fin n) (hab : a ≠ b) :
      basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
          (basisVector a + basisVector b) =
        (if c = a then (-1 : ℝ) else if c = b then -1 else 1) •
          basisVector (Equiv.swap a b c) := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply, hab, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst c
        simp [dot, basisVector, Pi.single_apply, hab.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        simp only [if_neg hca, if_neg hcb, one_smul]
        ext j
        simp [dot, basisVector, Pi.single_apply, hca, hcb]
  have hdiff_basis (a b c : Fin n) (hab : a ≠ b) :
      basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
          (basisVector a - basisVector b) =
        basisVector (Equiv.swap a b c) := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply, hab, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst c
        simp [dot, basisVector, Pi.single_apply, hab.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        ext j
        simp [dot, basisVector, Pi.single_apply, hca, hcb]
  have hunit_basis (a c : Fin n) :
      basisVector c - (2 * dot (basisVector a) (basisVector c)) • basisVector a =
        (if c = a then (-1 : ℝ) else 1) • basisVector c := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply]
      module
    · simp only [if_neg hca, one_smul]
      ext j
      simp [dot, basisVector, Pi.single_apply, hca]
  have hsum_maps (a b : Fin n) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a + basisVector b) x •
        (basisVector a + basisVector b)) (typeBRoots n) (typeBRoots n) := by
    intro x hx
    rcases hx with hx | hx
    · left
      rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
      change (s • basisVector c + t • basisVector d) -
        dot (basisVector a + basisVector b) (s • basisVector c + t • basisVector d) •
          (basisVector a + basisVector b) ∈ pairRoots n
      rw [hreflect_decomp, hsum_basis a b c hab, hsum_basis a b d hab]
      let εc : ℝ := if c = a then -1 else if c = b then -1 else 1
      let εd : ℝ := if d = a then -1 else if d = b then -1 else 1
      refine ⟨Equiv.swap a b c, Equiv.swap a b d, ?_, s * εc, t * εd, ?_, ?_, ?_⟩
      · exact fun h => hcd ((Equiv.swap a b).injective h)
      · have hεc : εc = -1 ∨ εc = 1 := by
          dsimp [εc]
          by_cases hca : c = a <;> by_cases hcb : c = b <;> simp [hca, hcb]
        rcases hs with hs | hs <;> rcases hεc with hεc | hεc <;>
          subst s <;> rw [hεc] <;> norm_num
      · have hεd : εd = -1 ∨ εd = 1 := by
          dsimp [εd]
          by_cases hda : d = a <;> by_cases hdb : d = b <;> simp [hda, hdb]
        rcases ht with ht | ht <;> rcases hεd with hεd | hεd <;>
          subst t <;> rw [hεd] <;> norm_num
      · dsimp [εc, εd]
        by_cases hca : c = a <;> by_cases hcb : c = b <;>
          by_cases hda : d = a <;> by_cases hdb : d = b <;> simp [hca, hcb, hda, hdb]
    · right
      rcases hx with ⟨c, rfl | rfl⟩
      · change basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
          (basisVector a + basisVector b) ∈ signedUnitRoots n
        rw [hsum_basis a b c hab]
        by_cases hca : c = a
        · exact ⟨Equiv.swap a b c, Or.inr (by simp [hca])⟩
        · by_cases hcb : c = b
          · exact ⟨Equiv.swap a b c, Or.inr (by simp [hcb])⟩
          · exact ⟨Equiv.swap a b c, Or.inl (by simp [hca, hcb])⟩
      · change -basisVector c - dot (basisVector a + basisVector b) (-basisVector c) •
          (basisVector a + basisVector b) ∈ signedUnitRoots n
        rw [show -basisVector c - dot (basisVector a + basisVector b) (-basisVector c) •
            (basisVector a + basisVector b) =
            -(basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
              (basisVector a + basisVector b)) by
              rw [hdot_neg]
              module,
          hsum_basis a b c hab]
        by_cases hca : c = a
        · exact ⟨Equiv.swap a b c, Or.inl (by simp [hca])⟩
        · by_cases hcb : c = b
          · exact ⟨Equiv.swap a b c, Or.inl (by simp [hcb])⟩
          · exact ⟨Equiv.swap a b c, Or.inr (by simp [hca, hcb])⟩
  have hdiff_maps (a b : Fin n) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a - basisVector b) x •
        (basisVector a - basisVector b)) (typeBRoots n) (typeBRoots n) := by
    intro x hx
    rcases hx with hx | hx
    · left
      rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
      change (s • basisVector c + t • basisVector d) -
        dot (basisVector a - basisVector b) (s • basisVector c + t • basisVector d) •
          (basisVector a - basisVector b) ∈ pairRoots n
      rw [hreflect_decomp, hdiff_basis a b c hab, hdiff_basis a b d hab]
      exact ⟨Equiv.swap a b c, Equiv.swap a b d,
        fun h => hcd ((Equiv.swap a b).injective h), s, t, hs, ht, rfl⟩
    · right
      rcases hx with ⟨c, rfl | rfl⟩
      · change basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
          (basisVector a - basisVector b) ∈ signedUnitRoots n
        rw [hdiff_basis a b c hab]
        exact ⟨Equiv.swap a b c, Or.inl rfl⟩
      · change -basisVector c - dot (basisVector a - basisVector b) (-basisVector c) •
          (basisVector a - basisVector b) ∈ signedUnitRoots n
        rw [show -basisVector c - dot (basisVector a - basisVector b) (-basisVector c) •
            (basisVector a - basisVector b) =
            -(basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
              (basisVector a - basisVector b)) by
              rw [hdot_neg]
              module,
          hdiff_basis a b c hab]
        exact ⟨Equiv.swap a b c, Or.inr rfl⟩
  have hunit_maps (a : Fin n) :
      MapsTo (fun x => x - (2 * dot (basisVector a) x) • basisVector a)
        (typeBRoots n) (typeBRoots n) := by
    intro x hx
    rcases hx with hx | hx
    · left
      rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
      change (s • basisVector c + t • basisVector d) -
        (2 * dot (basisVector a) (s • basisVector c + t • basisVector d)) •
          basisVector a ∈ pairRoots n
      rw [hreflect_decomp_two, hunit_basis a c, hunit_basis a d]
      let εc : ℝ := if c = a then -1 else 1
      let εd : ℝ := if d = a then -1 else 1
      refine ⟨c, d, hcd, s * εc, t * εd, ?_, ?_, ?_⟩
      · have hεc : εc = -1 ∨ εc = 1 := by
          dsimp [εc]
          by_cases hca : c = a <;> simp [hca]
        rcases hs with hs | hs <;> rcases hεc with hεc | hεc <;>
          subst s <;> rw [hεc] <;> norm_num
      · have hεd : εd = -1 ∨ εd = 1 := by
          dsimp [εd]
          by_cases hda : d = a <;> simp [hda]
        rcases ht with ht | ht <;> rcases hεd with hεd | hεd <;>
          subst t <;> rw [hεd] <;> norm_num
      · dsimp [εc, εd]
        by_cases hca : c = a <;> by_cases hda : d = a <;> simp [hca, hda]
    · right
      rcases hx with ⟨c, rfl | rfl⟩
      · change basisVector c - (2 * dot (basisVector a) (basisVector c)) •
          basisVector a ∈ signedUnitRoots n
        rw [hunit_basis a c]
        by_cases hca : c = a
        · exact ⟨c, Or.inr (by simp [hca])⟩
        · exact ⟨c, Or.inl (by simp [hca])⟩
      · change -basisVector c - (2 * dot (basisVector a) (-basisVector c)) •
          basisVector a ∈ signedUnitRoots n
        rw [show -basisVector c - (2 * dot (basisVector a) (-basisVector c)) • basisVector a =
            -(basisVector c - (2 * dot (basisVector a) (basisVector c)) • basisVector a) by
              rw [hdot_neg]
              module,
          hunit_basis a c]
        by_cases hca : c = a
        · exact ⟨c, Or.inl (by simp [hca])⟩
        · exact ⟨c, Or.inr (by simp [hca])⟩
  constructor
  · intro r hr
    rcases hr with ⟨a, b, hab, s, t, hs, ht, rfl⟩
    rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
    · simp only [one_smul, neg_smul]
      have hfun := hreflect_neg_fun (basisVector a + basisVector b)
      rw [show -basisVector a + -basisVector b = -(basisVector a + basisVector b) by module]
      rw [hfun]
      exact hsum_maps a b hab
    · simp only [one_smul, neg_smul]
      have hfun := hreflect_neg_fun (basisVector a - basisVector b)
      rw [show -basisVector a + basisVector b = -(basisVector a - basisVector b) by module]
      rw [hfun]
      exact hdiff_maps a b hab
    · simp only [one_smul, neg_smul]
      exact hdiff_maps a b hab
    · simp only [one_smul]
      exact hsum_maps a b hab
  · intro r hr
    rcases hr with ⟨a, rfl | rfl⟩
    · exact hunit_maps a
    · have hpoint : (fun x => x - (2 * dot (-basisVector a) x) • (-basisVector a)) =
          (fun x => x - (2 * dot (basisVector a) x) • basisVector a) := by
        funext x
        rw [hdot_left_neg]
        module
      rw [hpoint]
      exact hunit_maps a

open Set

/-- The two length-dependent reflection formulas of the standard type `C` roots
preserve the full type `C` root set. -/
public lemma typeCRoot_reflection_mapsTo (n : ℕ) :
    (∀ r ∈ pairRoots n,
      MapsTo (fun x => x - dot r x • r) (typeCRoots n) (typeCRoots n)) ∧
    ∀ r ∈ signedDoubleUnitRoots n,
      MapsTo (fun x => x - ((1 / 2) * dot r x) • r) (typeCRoots n) (typeCRoots n) := by
  classical
  have hdot_add (r x y : Vec n) : dot r (x + y) = dot r x + dot r y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  have hdot_smul (r x : Vec n) (s : ℝ) : dot r (s • x) = s * dot r x := by
    simp [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdot_two (r x : Vec n) : dot r (2 • x) = 2 * dot r x := by
    rw [two_smul, hdot_add]
    ring
  have hdot_neg (r x : Vec n) : dot r (-x) = -dot r x := by
    calc
      dot r (-x) = dot r ((-1 : ℝ) • x) := by simp
      _ = (-1 : ℝ) * dot r x := hdot_smul r x (-1)
      _ = -dot r x := by ring
  have hdot_left_neg (r x : Vec n) : dot (-r) x = -dot r x := by
    rw [dot_comm, hdot_neg, dot_comm]
  have hreflect_neg (r x : Vec n) :
      x - dot (-r) x • (-r) = x - dot r x • r := by
    rw [hdot_left_neg]
    module
  have hreflect_neg_fun (r : Vec n) :
      (fun x => x - dot (-r) x • (-r)) = (fun x => x - dot r x • r) := by
    funext x
    exact hreflect_neg r x
  have hreflect_decomp (r x y : Vec n) (s t : ℝ) :
      (s • x + t • y) - dot r (s • x + t • y) • r =
        s • (x - dot r x • r) + t • (y - dot r y • r) := by
    rw [hdot_add, hdot_smul, hdot_smul]
    module
  have hreflect_decomp_two (r x y : Vec n) (s t : ℝ) :
      (s • x + t • y) - (2 * dot r (s • x + t • y)) • r =
        s • (x - (2 * dot r x) • r) + t • (y - (2 * dot r y) • r) := by
    rw [hdot_add, hdot_smul, hdot_smul]
    module
  have hsum_basis (a b c : Fin n) (hab : a ≠ b) :
      basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
          (basisVector a + basisVector b) =
        (if c = a then (-1 : ℝ) else if c = b then -1 else 1) •
          basisVector (Equiv.swap a b c) := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply, hab, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst c
        simp [dot, basisVector, Pi.single_apply, hab.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        simp only [if_neg hca, if_neg hcb, one_smul]
        ext j
        simp [dot, basisVector, Pi.single_apply, hca, hcb]
  have hdiff_basis (a b c : Fin n) (hab : a ≠ b) :
      basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
          (basisVector a - basisVector b) =
        basisVector (Equiv.swap a b c) := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply, hab, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst c
        simp [dot, basisVector, Pi.single_apply, hab.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        ext j
        simp [dot, basisVector, Pi.single_apply, hca, hcb]
  have hunit_basis (a c : Fin n) :
      basisVector c - (2 * dot (basisVector a) (basisVector c)) • basisVector a =
        (if c = a then (-1 : ℝ) else 1) • basisVector c := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply]
      module
    · simp only [if_neg hca, one_smul]
      ext j
      simp [dot, basisVector, Pi.single_apply, hca]
  have hsum_maps (a b : Fin n) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a + basisVector b) x •
        (basisVector a + basisVector b)) (typeCRoots n) (typeCRoots n) := by
    intro x hx
    rcases hx with hx | hx
    · left
      rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
      change (s • basisVector c + t • basisVector d) -
        dot (basisVector a + basisVector b) (s • basisVector c + t • basisVector d) •
          (basisVector a + basisVector b) ∈ pairRoots n
      rw [hreflect_decomp, hsum_basis a b c hab, hsum_basis a b d hab]
      let εc : ℝ := if c = a then -1 else if c = b then -1 else 1
      let εd : ℝ := if d = a then -1 else if d = b then -1 else 1
      refine ⟨Equiv.swap a b c, Equiv.swap a b d, ?_, s * εc, t * εd, ?_, ?_, ?_⟩
      · exact fun h => hcd ((Equiv.swap a b).injective h)
      · have hεc : εc = -1 ∨ εc = 1 := by
          dsimp [εc]
          by_cases hca : c = a <;> by_cases hcb : c = b <;> simp [hca, hcb]
        rcases hs with hs | hs <;> rcases hεc with hεc | hεc <;>
          subst s <;> rw [hεc] <;> norm_num
      · have hεd : εd = -1 ∨ εd = 1 := by
          dsimp [εd]
          by_cases hda : d = a <;> by_cases hdb : d = b <;> simp [hda, hdb]
        rcases ht with ht | ht <;> rcases hεd with hεd | hεd <;>
          subst t <;> rw [hεd] <;> norm_num
      · dsimp [εc, εd]
        by_cases hca : c = a <;> by_cases hcb : c = b <;>
          by_cases hda : d = a <;> by_cases hdb : d = b <;> simp [hca, hcb, hda, hdb]
    · right
      rcases hx with ⟨c, rfl | rfl⟩
      · change (2 • basisVector c) - dot (basisVector a + basisVector b) (2 • basisVector c) •
          (basisVector a + basisVector b) ∈ signedDoubleUnitRoots n
        rw [show (2 • basisVector c) - dot (basisVector a + basisVector b) (2 • basisVector c) •
            (basisVector a + basisVector b) =
            2 • (basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
              (basisVector a + basisVector b)) by
              rw [hdot_two]
              module,
          hsum_basis a b c hab]
        by_cases hca : c = a
        · exact ⟨Equiv.swap a b c, Or.inr (by simp [hca])⟩
        · by_cases hcb : c = b
          · exact ⟨Equiv.swap a b c, Or.inr (by simp [hcb])⟩
          · exact ⟨Equiv.swap a b c, Or.inl (by simp [hca, hcb])⟩
      · change -(2 • basisVector c) - dot (basisVector a + basisVector b) (-(2 • basisVector c)) •
          (basisVector a + basisVector b) ∈ signedDoubleUnitRoots n
        rw [show -(2 • basisVector c) - dot (basisVector a + basisVector b) (-(2 • basisVector c)) •
            (basisVector a + basisVector b) =
            -(2 • (basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
              (basisVector a + basisVector b))) by
              rw [hdot_neg, hdot_two]
              module,
          hsum_basis a b c hab]
        by_cases hca : c = a
        · exact ⟨Equiv.swap a b c, Or.inl (by simp [hca])⟩
        · by_cases hcb : c = b
          · exact ⟨Equiv.swap a b c, Or.inl (by simp [hcb])⟩
          · exact ⟨Equiv.swap a b c, Or.inr (by simp [hca, hcb])⟩
  have hdiff_maps (a b : Fin n) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a - basisVector b) x •
        (basisVector a - basisVector b)) (typeCRoots n) (typeCRoots n) := by
    intro x hx
    rcases hx with hx | hx
    · left
      rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
      change (s • basisVector c + t • basisVector d) -
        dot (basisVector a - basisVector b) (s • basisVector c + t • basisVector d) •
          (basisVector a - basisVector b) ∈ pairRoots n
      rw [hreflect_decomp, hdiff_basis a b c hab, hdiff_basis a b d hab]
      exact ⟨Equiv.swap a b c, Equiv.swap a b d,
        fun h => hcd ((Equiv.swap a b).injective h), s, t, hs, ht, rfl⟩
    · right
      rcases hx with ⟨c, rfl | rfl⟩
      · change (2 • basisVector c) - dot (basisVector a - basisVector b) (2 • basisVector c) •
          (basisVector a - basisVector b) ∈ signedDoubleUnitRoots n
        rw [show (2 • basisVector c) - dot (basisVector a - basisVector b) (2 • basisVector c) •
            (basisVector a - basisVector b) =
            2 • (basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
              (basisVector a - basisVector b)) by
              rw [hdot_two]
              module,
          hdiff_basis a b c hab]
        exact ⟨Equiv.swap a b c, Or.inl (by simp)⟩
      · change -(2 • basisVector c) - dot (basisVector a - basisVector b) (-(2 • basisVector c)) •
          (basisVector a - basisVector b) ∈ signedDoubleUnitRoots n
        rw [show -(2 • basisVector c) - dot (basisVector a - basisVector b) (-(2 • basisVector c)) •
            (basisVector a - basisVector b) =
            -(2 • (basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
              (basisVector a - basisVector b))) by
              rw [hdot_neg, hdot_two]
              module,
          hdiff_basis a b c hab]
        exact ⟨Equiv.swap a b c, Or.inr (by simp)⟩
  have hunit_maps (a : Fin n) :
      MapsTo (fun x => x - (2 * dot (basisVector a) x) • basisVector a)
        (typeCRoots n) (typeCRoots n) := by
    intro x hx
    rcases hx with hx | hx
    · left
      rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
      change (s • basisVector c + t • basisVector d) -
        (2 * dot (basisVector a) (s • basisVector c + t • basisVector d)) •
          basisVector a ∈ pairRoots n
      rw [hreflect_decomp_two, hunit_basis a c, hunit_basis a d]
      let εc : ℝ := if c = a then -1 else 1
      let εd : ℝ := if d = a then -1 else 1
      refine ⟨c, d, hcd, s * εc, t * εd, ?_, ?_, ?_⟩
      · have hεc : εc = -1 ∨ εc = 1 := by
          dsimp [εc]
          by_cases hca : c = a <;> simp [hca]
        rcases hs with hs | hs <;> rcases hεc with hεc | hεc <;>
          subst s <;> rw [hεc] <;> norm_num
      · have hεd : εd = -1 ∨ εd = 1 := by
          dsimp [εd]
          by_cases hda : d = a <;> simp [hda]
        rcases ht with ht | ht <;> rcases hεd with hεd | hεd <;>
          subst t <;> rw [hεd] <;> norm_num
      · dsimp [εc, εd]
        by_cases hca : c = a <;> by_cases hda : d = a <;> simp [hca, hda]
    · right
      rcases hx with ⟨c, rfl | rfl⟩
      · change (2 • basisVector c) - (2 * dot (basisVector a) (2 • basisVector c)) •
          basisVector a ∈ signedDoubleUnitRoots n
        rw [show (2 • basisVector c) - (2 * dot (basisVector a) (2 • basisVector c)) • basisVector a =
            2 • (basisVector c - (2 * dot (basisVector a) (basisVector c)) • basisVector a) by
              rw [hdot_two]
              module,
          hunit_basis a c]
        by_cases hca : c = a
        · exact ⟨c, Or.inr (by simp [hca])⟩
        · exact ⟨c, Or.inl (by simp [hca])⟩
      · change -(2 • basisVector c) - (2 * dot (basisVector a) (-(2 • basisVector c))) •
          basisVector a ∈ signedDoubleUnitRoots n
        rw [show -(2 • basisVector c) - (2 * dot (basisVector a) (-(2 • basisVector c))) • basisVector a =
            -(2 • (basisVector c - (2 * dot (basisVector a) (basisVector c)) • basisVector a)) by
              rw [hdot_neg, hdot_two]
              module,
          hunit_basis a c]
        by_cases hca : c = a
        · exact ⟨c, Or.inl (by simp [hca])⟩
        · exact ⟨c, Or.inr (by simp [hca])⟩
  constructor
  · intro r hr
    rcases hr with ⟨a, b, hab, s, t, hs, ht, rfl⟩
    rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
    · simp only [one_smul, neg_smul]
      have hfun := hreflect_neg_fun (basisVector a + basisVector b)
      rw [show -basisVector a + -basisVector b = -(basisVector a + basisVector b) by module]
      rw [hfun]
      exact hsum_maps a b hab
    · simp only [one_smul, neg_smul]
      have hfun := hreflect_neg_fun (basisVector a - basisVector b)
      rw [show -basisVector a + basisVector b = -(basisVector a - basisVector b) by module]
      rw [hfun]
      exact hdiff_maps a b hab
    · simp only [one_smul, neg_smul]
      exact hdiff_maps a b hab
    · simp only [one_smul]
      exact hsum_maps a b hab
  · intro r hr
    rcases hr with ⟨a, rfl | rfl⟩
    · have hpoint : (fun x => x - ((1 / 2) * dot (2 • basisVector a) x) •
          (2 • basisVector a)) =
          (fun x => x - (2 * dot (basisVector a) x) • basisVector a) := by
        funext x
        have hd : dot (2 • basisVector a) x = 2 * dot (basisVector a) x := by
          rw [dot_comm, hdot_two, dot_comm]
        rw [hd]
        module
      rw [hpoint]
      exact hunit_maps a
    · have hneg : (fun x => x - ((1 / 2) * dot (-(2 • basisVector a)) x) •
          (-(2 • basisVector a))) =
          (fun x => x - ((1 / 2) * dot (2 • basisVector a) x) •
            (2 • basisVector a)) := by
        funext x
        rw [hdot_left_neg]
        module
      have hpoint : (fun x => x - ((1 / 2) * dot (2 • basisVector a) x) •
          (2 • basisVector a)) =
          (fun x => x - (2 * dot (basisVector a) x) • basisVector a) := by
        funext x
        have hd : dot (2 • basisVector a) x = 2 * dot (basisVector a) x := by
          rw [dot_comm, hdot_two, dot_comm]
        rw [hd]
        module
      rw [hneg, hpoint]
      exact hunit_maps a

open Set

/-- Reflections in the standard type `D` roots preserve the type `D` root set. -/
public lemma typeDRoot_reflection_mapsTo (n : ℕ) :
    ∀ r ∈ typeDRoots n,
      MapsTo (fun x => x - dot r x • r) (typeDRoots n) (typeDRoots n) := by
  classical
  have hdot_add (r x y : Vec n) : dot r (x + y) = dot r x + dot r y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  have hdot_smul (r x : Vec n) (s : ℝ) : dot r (s • x) = s * dot r x := by
    simp [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdot_neg (r x : Vec n) : dot r (-x) = -dot r x := by
    calc
      dot r (-x) = dot r ((-1 : ℝ) • x) := by simp
      _ = (-1 : ℝ) * dot r x := hdot_smul r x (-1)
      _ = -dot r x := by ring
  have hdot_left_neg (r x : Vec n) : dot (-r) x = -dot r x := by
    rw [dot_comm, hdot_neg, dot_comm]
  have hreflect_neg (r x : Vec n) :
      x - dot (-r) x • (-r) = x - dot r x • r := by
    rw [hdot_left_neg]
    module
  have hreflect_neg_fun (r : Vec n) :
      (fun x => x - dot (-r) x • (-r)) = (fun x => x - dot r x • r) := by
    funext x
    exact hreflect_neg r x
  have hreflect_decomp (r x y : Vec n) (s t : ℝ) :
      (s • x + t • y) - dot r (s • x + t • y) • r =
        s • (x - dot r x • r) + t • (y - dot r y • r) := by
    rw [hdot_add, hdot_smul, hdot_smul]
    module
  have hsum_basis (a b c : Fin n) (hab : a ≠ b) :
      basisVector c - dot (basisVector a + basisVector b) (basisVector c) •
          (basisVector a + basisVector b) =
        (if c = a then (-1 : ℝ) else if c = b then -1 else 1) •
          basisVector (Equiv.swap a b c) := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply, hab, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst c
        simp [dot, basisVector, Pi.single_apply, hab.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        simp only [if_neg hca, if_neg hcb, one_smul]
        ext j
        simp [dot, basisVector, Pi.single_apply, hca, hcb]
  have hdiff_basis (a b c : Fin n) (hab : a ≠ b) :
      basisVector c - dot (basisVector a - basisVector b) (basisVector c) •
          (basisVector a - basisVector b) =
        basisVector (Equiv.swap a b c) := by
    by_cases hca : c = a
    · subst c
      simp [dot, basisVector, Pi.single_apply, hab, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst c
        simp [dot, basisVector, Pi.single_apply, hab.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        ext j
        simp [dot, basisVector, Pi.single_apply, hca, hcb]
  have hsum_maps (a b : Fin n) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a + basisVector b) x •
        (basisVector a + basisVector b)) (typeDRoots n) (typeDRoots n) := by
    intro x hx
    rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
    change (s • basisVector c + t • basisVector d) -
      dot (basisVector a + basisVector b) (s • basisVector c + t • basisVector d) •
        (basisVector a + basisVector b) ∈ pairRoots n
    rw [hreflect_decomp, hsum_basis a b c hab, hsum_basis a b d hab]
    let εc : ℝ := if c = a then -1 else if c = b then -1 else 1
    let εd : ℝ := if d = a then -1 else if d = b then -1 else 1
    refine ⟨Equiv.swap a b c, Equiv.swap a b d, ?_, s * εc, t * εd, ?_, ?_, ?_⟩
    · exact fun h => hcd ((Equiv.swap a b).injective h)
    · have hεc : εc = -1 ∨ εc = 1 := by
        dsimp [εc]
        by_cases hca : c = a <;> by_cases hcb : c = b <;> simp [hca, hcb]
      rcases hs with hs | hs <;> rcases hεc with hεc | hεc <;>
        subst s <;> rw [hεc] <;> norm_num
    · have hεd : εd = -1 ∨ εd = 1 := by
        dsimp [εd]
        by_cases hda : d = a <;> by_cases hdb : d = b <;> simp [hda, hdb]
      rcases ht with ht | ht <;> rcases hεd with hεd | hεd <;>
        subst t <;> rw [hεd] <;> norm_num
    · dsimp [εc, εd]
      by_cases hca : c = a <;> by_cases hcb : c = b <;>
        by_cases hda : d = a <;> by_cases hdb : d = b <;> simp [hca, hcb, hda, hdb]
  have hdiff_maps (a b : Fin n) (hab : a ≠ b) :
      MapsTo (fun x => x - dot (basisVector a - basisVector b) x •
        (basisVector a - basisVector b)) (typeDRoots n) (typeDRoots n) := by
    intro x hx
    rcases hx with ⟨c, d, hcd, s, t, hs, ht, rfl⟩
    change (s • basisVector c + t • basisVector d) -
      dot (basisVector a - basisVector b) (s • basisVector c + t • basisVector d) •
        (basisVector a - basisVector b) ∈ pairRoots n
    rw [hreflect_decomp, hdiff_basis a b c hab, hdiff_basis a b d hab]
    exact ⟨Equiv.swap a b c, Equiv.swap a b d,
      fun h => hcd ((Equiv.swap a b).injective h), s, t, hs, ht, rfl⟩
  intro r hr
  rcases hr with ⟨a, b, hab, s, t, hs, ht, rfl⟩
  rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
  · simp only [one_smul, neg_smul]
    have hfun := hreflect_neg_fun (basisVector a + basisVector b)
    rw [show -basisVector a + -basisVector b = -(basisVector a + basisVector b) by module]
    rw [hfun]
    exact hsum_maps a b hab
  · simp only [one_smul, neg_smul]
    have hfun := hreflect_neg_fun (basisVector a - basisVector b)
    rw [show -basisVector a + basisVector b = -(basisVector a - basisVector b) by module]
    rw [hfun]
    exact hdiff_maps a b hab
  · simp only [one_smul, neg_smul]
    exact hdiff_maps a b hab
  · simp only [one_smul]
    exact hsum_maps a b hab

@[expose] public noncomputable def typeDCorootEmbedding (m : ℕ) :
    TypeDRootIndex (m + 2) ↪ Module.Dual ℝ (typeDRootSpan (m + 2)) :=
  ⟨typeDRootFunctional (m + 2), typeDRootFunctional_injective m⟩

open Set

public noncomputable def typeASimpleRootIndex (m : ℕ) (i : Fin m) : TypeARootIndex m :=
  ⟨(i.castSucc, i.succ), by
    intro h
    have := congrArg Fin.val h
    simp at this⟩

/-- Endpoint coordinates of the standard type-A simple root index. -/
public lemma typeASimpleRootIndex_pair (m : ℕ) (i : Fin m) :
    (typeASimpleRootIndex m i).1.1 = i.castSucc ∧
      (typeASimpleRootIndex m i).1.2 = i.succ := by
  simp [typeASimpleRootIndex]

public lemma typeASimpleRootIndex_injective (m : ℕ) : Function.Injective (typeASimpleRootIndex m) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun r : TypeARootIndex m => r.1.1.val) h

private lemma dot_basisVector_right {n : ℕ} (x : Vec n) (j : Fin n) :
    dot x (basisVector j) = x j := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private noncomputable def prefixVector (m : ℕ) (i : Fin m) : Vec (m + 1) :=
  fun k => if k.val ≤ i.val then 1 else 0

private noncomputable def prefixFunctional (m : ℕ) (i : Fin m) : typeARootSpan m →ₗ[ℝ] ℝ where
  toFun x := dot (prefixVector m i) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change prefixVector m i k * (c * (x : Vec (m + 1)) k) =
      c * (prefixVector m i k * (x : Vec (m + 1)) k)
    ring

private lemma prefix_simple (m : ℕ) (i j : Fin m) :
    prefixFunctional m i (typeARootInSpan m (typeASimpleRootIndex m j)) = if i = j then 1 else 0 := by
  classical
  rw [show typeARootInSpan m (typeASimpleRootIndex m j) =
      ⟨typeARootEmbedding m (typeASimpleRootIndex m j),
        Submodule.subset_span (Set.mem_range_self _)⟩ by
    apply Subtype.ext
    exact typeARootInSpan_val m _]
  change dot (prefixVector m i) (typeARootEmbedding m (typeASimpleRootIndex m j)) = _
  rw [typeARootEmbedding_apply]
  simp only [typeASimpleRootIndex]
  rw [show dot (prefixVector m i) (basisVector j.castSucc - basisVector j.succ) =
    dot (prefixVector m i) (basisVector j.castSucc) -
      dot (prefixVector m i) (basisVector j.succ) by
      simp [dot, mul_sub, Finset.sum_sub_distrib]]
  rw [dot_basisVector_right, dot_basisVector_right]
  simp only [prefixVector, Fin.val_castSucc, Fin.val_succ]
  by_cases h : i = j
  · subst j
    simp
  · by_cases hji : j.val ≤ i.val
    · have hsucc : j.val + 1 ≤ i.val := by omega
      simp [hji, hsucc, h]
    · have hs : ¬j.val + 1 ≤ i.val := by omega
      simp [hji, hs, h]

private lemma typeASimpleRoots_linearIndependent (m : ℕ) : LinearIndependent ℝ (fun i : Fin m =>
    (typeARootPairing m).root (typeASimpleRootIndex m i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (prefixFunctional m i) hg
  simp only [map_sum, map_smul, map_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [typeARootPairing_root, prefix_simple] using h
  · intro j hj hji
    rw [typeARootPairing_root, prefix_simple]
    simp [hji.symm]
  · simp

public lemma typeARootPairing_linearIndepOn_simpleRoots (m : ℕ) : LinearIndepOn ℝ (typeARootPairing m).root (Set.range (typeASimpleRootIndex m)) := by
  rw [linearIndepOn_range_iff (typeASimpleRootIndex_injective m)]
  simpa [Function.comp_def] using typeASimpleRoots_linearIndependent m

private noncomputable def simpleClosure (m : ℕ) : AddSubmonoid (typeARootSpan m) :=
  AddSubmonoid.closure ((typeARootPairing m).root '' Set.range (typeASimpleRootIndex m))

private lemma simple_mem (m : ℕ) (i : Fin m) :
    (typeARootPairing m).root (typeASimpleRootIndex m i) ∈ simpleClosure m := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

private lemma positive_aux (m : ℕ) (a b : Fin (m + 1)) (hab : a.val < b.val) :
    (typeARootPairing m).root ⟨(a, b), Fin.ne_of_lt hab⟩ ∈ simpleClosure m := by
  by_cases hone : b.val = a.val + 1
  · let i : Fin m := ⟨a.val, by omega⟩
    have hidx : (⟨(a, b), Fin.ne_of_lt hab⟩ : TypeARootIndex m) = typeASimpleRootIndex m i := by
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        simpa [i, typeASimpleRootIndex] using hone
    rw [hidx]
    exact simple_mem m i
  · let c : Fin (m + 1) := ⟨b.val - 1, by omega⟩
    let i : Fin m := ⟨b.val - 1, by omega⟩
    have hcval : c.val = b.val - 1 := rfl
    have hac : a.val < c.val := by rw [hcval]; omega
    have hcb : c.val < b.val := by rw [hcval]; omega
    have hleft := positive_aux m a c hac
    have hright : (typeARootPairing m).root
        (⟨(c, b), Fin.ne_of_lt hcb⟩ : TypeARootIndex m) ∈ simpleClosure m := by
      have hidx : (⟨(c, b), Fin.ne_of_lt hcb⟩ : TypeARootIndex m) = typeASimpleRootIndex m i := by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          rfl
        · apply Fin.ext
          simp [i, typeASimpleRootIndex]
          omega
      rw [hidx]
      exact simple_mem m i
    have hadd := AddSubmonoid.add_mem (simpleClosure m) hleft hright
    convert hadd using 1
    apply Subtype.ext
    simp only [typeARootPairing_root, typeARootInSpan_val, typeARootEmbedding_apply,
      Submodule.coe_add]
    module
termination_by b.val
decreasing_by omega

public lemma typeARootPairing_root_mem_or_neg_mem_simpleClosure (m : ℕ)
    (r : TypeARootIndex m) :
    (typeARootPairing m).root r ∈
        AddSubmonoid.closure ((typeARootPairing m).root '' Set.range (typeASimpleRootIndex m)) ∨
      -(typeARootPairing m).root r ∈
        AddSubmonoid.closure ((typeARootPairing m).root '' Set.range (typeASimpleRootIndex m)) := by
  rcases lt_or_gt_of_ne r.2 with hab | hba
  · exact Or.inl (positive_aux m r.1.1 r.1.2 hab)
  · right
    change -(typeARootPairing m).root r ∈ simpleClosure m
    have hpos := positive_aux m r.1.2 r.1.1 hba
    convert hpos using 1
    apply Subtype.ext
    simp only [typeARootPairing_root, typeARootInSpan_val, typeARootEmbedding_apply,
      Submodule.coe_neg]
    module

/-- The standard type `A_m` base, supported on the adjacent coordinate roots
`e_i - e_{i+1}`. -/
public noncomputable def typeARootPairing_base (m : ℕ) : (typeARootPairing m).Base :=
  RootPairing.Base.mk' (typeARootPairing m) (Set.range (typeASimpleRootIndex m))
    (typeARootPairing_linearIndepOn_simpleRoots m)
    (typeARootPairing_root_mem_or_neg_mem_simpleClosure m)

public lemma typeARootPairing_base_support (m : ℕ) :
    ((typeARootPairing_base m).support : Set (TypeARootIndex m)) =
      Set.range (typeASimpleRootIndex m) := by
  simp [typeARootPairing_base, RootPairing.Base.mk']

/-- The standard numbering of the adjacent simple roots in the type `A_m` base. -/
public noncomputable def typeARootPairing_baseEquiv (m : ℕ) :
    Fin m ≃ (typeARootPairing_base m).support :=
  (Equiv.ofInjective (typeASimpleRootIndex m) (typeASimpleRootIndex_injective m)).trans
    (Equiv.setCongr (typeARootPairing_base_support m).symm)

@[simp]
public lemma typeARootPairing_baseEquiv_val (m : ℕ) (i : Fin m) :
    (typeARootPairing_baseEquiv m i : TypeARootIndex m) = typeASimpleRootIndex m i := by
  rfl

public lemma typeARootEmbedding_simpleRoot (m : ℕ) (i : Fin m) :
    typeARootEmbedding m (typeASimpleRootIndex m i) = typeASimpleRoot m i := by
  rw [typeARootEmbedding_apply]
  rfl

public lemma typeARootPairing_simpleRoot_val (m : ℕ) (i : Fin m) :
    ((typeARootPairing m).root (typeASimpleRootIndex m i) : Vec (m + 1)) =
      typeASimpleRoot m i := by
  rw [typeARootPairing_root, typeARootInSpan_val]
  exact typeARootEmbedding_simpleRoot m i

open Set

private lemma dot_add_right_B {n : ℕ} (x y z : Vec n) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private lemma dot_smul_right_B {n : ℕ} (x y : Vec n) (c : ℝ) :
    dot x (c • y) = c * dot x y := by
  simp [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma dot_add_left_B {n : ℕ} (x y z : Vec n) :
    dot (x + y) z = dot x z + dot y z := by
  rw [dot_comm, dot_add_right_B, dot_comm z x, dot_comm z y]

private lemma dot_smul_left_B {n : ℕ} (x y : Vec n) (c : ℝ) :
    dot (c • x) y = c * dot x y := by
  rw [dot_comm, dot_smul_right_B, dot_comm y x]

private lemma dot_basisVector_basisVector_B {n : ℕ} (i j : Fin n) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma dot_basisVector_right_B {n : ℕ} (x : Vec n) (i : Fin n) :
    dot x (basisVector i) = x i := by
  classical
  simp [dot, basisVector, Pi.single_apply]

@[expose] public noncomputable def typeBRootSpan (n : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (range (fun r : TypeBRootIndex n =>
    (typeBRootEmbedding n r : Vec n)))

@[expose] public noncomputable def typeBRootInSpan (n : ℕ) : TypeBRootIndex n ↪ typeBRootSpan n where
  toFun r := ⟨(typeBRootEmbedding n r : Vec n),
    by
      change (typeBRootEmbedding n r : Vec n) ∈
        Submodule.span ℝ (range (fun s : TypeBRootIndex n =>
          (typeBRootEmbedding n s : Vec n)))
      exact Submodule.subset_span (mem_range_self r)⟩
  inj' := by
    intro r s h
    have hv : (typeBRootEmbedding n r : Vec n) =
        (typeBRootEmbedding n s : Vec n) :=
      congrArg (fun x : typeBRootSpan n => (x : Vec n)) h
    have he : typeBRootEmbedding n r = typeBRootEmbedding n s := Subtype.ext hv
    exact typeBRootEmbedding_injective n he

@[simp] public lemma typeBRootInSpan_val (n : ℕ) (r : TypeBRootIndex n) :
    (typeBRootInSpan n r : Vec n) = (typeBRootEmbedding n r : Vec n) := by
  simp [typeBRootInSpan]

public noncomputable def typeBRootDotFunctional (n : ℕ) (r : TypeBRootIndex n) :
    Module.Dual ℝ (typeBRootSpan n) where
  toFun x := dot (typeBRootEmbedding n r : Vec n) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (typeBRootEmbedding n r : Vec n) i * (c * (x : Vec n) i) =
      c * ((typeBRootEmbedding n r : Vec n) i * (x : Vec n) i)
    ring

@[expose] public noncomputable def typeBRootFunctional (n : ℕ) (r : TypeBRootIndex n) :
    Module.Dual ℝ (typeBRootSpan n) :=
  match r with
  | .inl _ => typeBRootDotFunctional n r
  | .inr _ => (2 : ℝ) • typeBRootDotFunctional n r

public noncomputable def typeBCorootVector (n : ℕ) : TypeBRootIndex n → Vec n
  | .inl r => typeBRootEmbedding n (.inl r)
  | .inr r => (2 : ℝ) • (typeBRootEmbedding n (.inr r) : Vec n)

public lemma typeBRootFunctional_apply (n : ℕ) (r : TypeBRootIndex n)
    (x : typeBRootSpan n) :
    typeBRootFunctional n r x = dot (typeBCorootVector n r) x.1 := by
  cases r with
  | inl r => rfl
  | inr r =>
      change (2 : ℝ) * dot (typeBRootEmbedding n (.inr r) : Vec n) x.1 =
        dot ((2 : ℝ) • (typeBRootEmbedding n (.inr r) : Vec n)) x.1
      rw [dot_smul_left_B]

public lemma typeBRootInSpan_coroot_eval_apply (n : ℕ) (r s : TypeBRootIndex n) :
    Module.Dual.eval ℝ (typeBRootSpan n) (typeBRootInSpan n r)
      (typeBRootFunctional n s) =
      (match s with
      | .inl _ => dot (typeBRootEmbedding n s : Vec n) (typeBRootEmbedding n r : Vec n)
      | .inr _ => 2 * dot (typeBRootEmbedding n s : Vec n) (typeBRootEmbedding n r : Vec n)) := by
  cases s <;>
    simp [Module.Dual.eval_apply, typeBRootFunctional, typeBRootDotFunctional,
      typeBRootInSpan] <;> rfl

public lemma typeBRootInSpan_coroot_eval (n : ℕ) (r : TypeBRootIndex n) :
    Module.Dual.eval ℝ (typeBRootSpan n) (typeBRootInSpan n r)
      (typeBRootFunctional n r) = 2 := by
  classical
  cases r with
  | inl r =>
      rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
      rw [typeBRootInSpan_coroot_eval_apply]
      change dot (s.1 • basisVector i + t.1 • basisVector j)
        (s.1 • basisVector i + t.1 • basisVector j) = 2
      rcases s.2 with hs | hs <;> rcases t.2 with ht | ht <;>
        rw [hs, ht, dot_add_left_B, dot_smul_left_B, dot_smul_left_B,
          dot_add_right_B, dot_add_right_B, dot_smul_right_B, dot_smul_right_B,
          dot_smul_right_B, dot_smul_right_B] <;>
        simp [dot_basisVector_basisVector_B, hij.ne, hij.ne'] <;> norm_num
  | inr r =>
      rw [typeBRootInSpan_coroot_eval_apply]
      rcases r with ⟨i, b⟩
      cases b <;> simp [typeBRootEmbedding, typeBRootVector, dot, basisVector, Pi.single_apply]

public lemma typeBRootInSpan_span_eq_top (n : ℕ) :
    Submodule.span ℝ (range (typeBRootInSpan n)) = ⊤ := by
  apply top_unique
  intro x hx
  refine Submodule.span_induction
    (p := fun y hy => (⟨y, hy⟩ : typeBRootSpan n) ∈
      Submodule.span ℝ (range (typeBRootInSpan n))) ?_ ?_ ?_ ?_ x.property
  · intro y hy
    obtain ⟨r, rfl⟩ := hy
    exact Submodule.subset_span (mem_range_self r)
  · exact Submodule.zero_mem _
  · intro y z hy hz hym hzm
    exact Submodule.add_mem _ hym hzm
  · intro c y hy hym
    exact Submodule.smul_mem _ c hym

private lemma typeBCorootVector_pair_ne_unit (n : ℕ)
    (r : TypeBPairRootIndex n) (s : Fin n × Bool) :
    typeBCorootVector n (.inl r) ≠ typeBCorootVector n (.inr s) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  rcases s with ⟨k, c⟩
  intro h
  have hi := congrFun h i
  have ha : a.1 = -1 ∨ a.1 = 1 := by
    rcases a.2 with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by simpa only [Set.mem_singleton_iff] using ha)
  by_cases hik : i = k
  · subst k
    rcases ha with ha | ha <;> cases c <;>
      norm_num [typeBCorootVector, typeBRootEmbedding, typeBRootVector,
        basisVector, Pi.single_apply, hij.ne, ha] at hi
  · rcases ha with ha | ha <;> cases c <;>
      norm_num [typeBCorootVector, typeBRootEmbedding, typeBRootVector,
        basisVector, Pi.single_apply, hij.ne, hik, ha] at hi

private lemma typeBCorootVector_injective (n : ℕ) :
    Function.Injective (typeBCorootVector n) := by
  intro r s h
  cases r with
  | inl r =>
      cases s with
      | inl s =>
          apply typeBRootEmbedding_injective n
          apply Subtype.ext
          exact h
      | inr s =>
          exact False.elim (typeBCorootVector_pair_ne_unit n r s h)
  | inr r =>
      cases s with
      | inl s =>
          exact False.elim (typeBCorootVector_pair_ne_unit n s r h.symm)
      | inr s =>
          apply typeBRootEmbedding_injective n
          apply Subtype.ext
          have h' : (2 : ℝ) • (typeBRootEmbedding n (.inr r) : Vec n) =
              (2 : ℝ) • (typeBRootEmbedding n (.inr s) : Vec n) := h
          exact (isUnit_iff_ne_zero.mpr (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp h'

public lemma typeBRootFunctional_injective (n : ℕ) :
    Function.Injective (typeBRootFunctional n) := by
  intro r s h
  apply typeBCorootVector_injective n
  funext i
  have heval := LinearMap.congr_fun h
    (typeBRootInSpan n (Sum.inr (i, false) : TypeBRootIndex n))
  rw [typeBRootFunctional_apply, typeBRootFunctional_apply] at heval
  simpa [typeBRootInSpan, typeBRootEmbedding, typeBRootVector,
    dot_basisVector_right_B] using heval

@[expose] public noncomputable def typeBCorootEmbedding (n : ℕ) :
    TypeBRootIndex n ↪ Module.Dual ℝ (typeBRootSpan n) :=
  ⟨typeBRootFunctional n, typeBRootFunctional_injective n⟩

private lemma typeBRootEmbedding_inl_mem_pairRoots (n : ℕ) (r : TypeBPairRootIndex n) :
    (typeBRootEmbedding n (.inl r) : Vec n) ∈ pairRoots n := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  exact ⟨i, j, hij.ne, s.1, t.1, s.2, t.2, rfl⟩

private lemma typeBRootEmbedding_inr_mem_signedUnitRoots (n : ℕ) (r : Fin n × Bool) :
    (typeBRootEmbedding n (.inr r) : Vec n) ∈ signedUnitRoots n := by
  rcases r with ⟨i, b⟩
  refine ⟨i, ?_⟩
  cases b <;> simp [typeBRootEmbedding, typeBRootVector]

public lemma typeBRootInSpan_reflection_mapsTo (n : ℕ) (r : TypeBRootIndex n) :
    MapsTo
      (Module.preReflection (typeBRootInSpan n r)
        ((Module.Dual.eval ℝ (typeBRootSpan n)).flip (typeBCorootEmbedding n r)))
      (range (typeBRootInSpan n)) (range (typeBRootInSpan n)) := by
  rintro _ ⟨s, rfl⟩
  rcases typeBRoot_reflection_mapsTo n with ⟨hpair, hunit⟩
  cases r with
  | inl r =>
      have hy := hpair (typeBRootEmbedding n (.inl r) : Vec n)
        (typeBRootEmbedding_inl_mem_pairRoots n r)
        (typeBRootEmbedding n s).property
      let y : typeBRoots n := ⟨
        (typeBRootEmbedding n s : Vec n) -
          dot (typeBRootEmbedding n (.inl r) : Vec n)
            (typeBRootEmbedding n s : Vec n) •
              (typeBRootEmbedding n (.inl r) : Vec n), hy⟩
      obtain ⟨t, ht⟩ := typeBRootEmbedding_surjective n y
      refine ⟨t, ?_⟩
      have htval := congrArg (fun z : typeBRoots n => (z : Vec n)) ht
      dsimp [y] at htval
      apply Subtype.ext
      change (typeBRootEmbedding n t : Vec n) =
        (typeBRootEmbedding n s : Vec n) -
          dot (typeBRootEmbedding n (.inl r) : Vec n)
            (typeBRootEmbedding n s : Vec n) •
              (typeBRootEmbedding n (.inl r) : Vec n)
      exact htval
  | inr r =>
      have hy := hunit (typeBRootEmbedding n (.inr r) : Vec n)
        (typeBRootEmbedding_inr_mem_signedUnitRoots n r)
        (typeBRootEmbedding n s).property
      let y : typeBRoots n := ⟨
        (typeBRootEmbedding n s : Vec n) -
          (2 * dot (typeBRootEmbedding n (.inr r) : Vec n)
            (typeBRootEmbedding n s : Vec n)) •
              (typeBRootEmbedding n (.inr r) : Vec n), hy⟩
      obtain ⟨t, ht⟩ := typeBRootEmbedding_surjective n y
      refine ⟨t, ?_⟩
      have htval := congrArg (fun z : typeBRoots n => (z : Vec n)) ht
      dsimp [y] at htval
      apply Subtype.ext
      change (typeBRootEmbedding n t : Vec n) =
        (typeBRootEmbedding n s : Vec n) -
          (2 * dot (typeBRootEmbedding n (.inr r) : Vec n)
            (typeBRootEmbedding n s : Vec n)) •
              (typeBRootEmbedding n (.inr r) : Vec n)
      exact htval

open Set

private lemma dot_add_right_C {n : ℕ} (x y z : Vec n) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private lemma dot_smul_right_C {n : ℕ} (x y : Vec n) (c : ℝ) :
    dot x (c • y) = c * dot x y := by
  simp [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma dot_add_left_C {n : ℕ} (x y z : Vec n) :
    dot (x + y) z = dot x z + dot y z := by
  rw [dot_comm, dot_add_right_C, dot_comm z x, dot_comm z y]

private lemma dot_smul_left_C {n : ℕ} (x y : Vec n) (c : ℝ) :
    dot (c • x) y = c * dot x y := by
  rw [dot_comm, dot_smul_right_C, dot_comm y x]

private lemma dot_basisVector_basisVector_CPairing {n : ℕ} (i j : Fin n) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma dot_basisVector_right_C {n : ℕ} (x : Vec n) (i : Fin n) :
    dot x (basisVector i) = x i := by
  classical
  simp [dot, basisVector, Pi.single_apply]

@[expose] public noncomputable def typeCRootSpan (n : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (range (fun r : TypeCRootIndex n =>
    (typeCRootEmbedding n r : Vec n)))

@[expose] public noncomputable def typeCRootInSpan (n : ℕ) : TypeCRootIndex n ↪ typeCRootSpan n where
  toFun r := ⟨(typeCRootEmbedding n r : Vec n),
    by
      change (typeCRootEmbedding n r : Vec n) ∈
        Submodule.span ℝ (range (fun s : TypeCRootIndex n =>
          (typeCRootEmbedding n s : Vec n)))
      exact Submodule.subset_span (mem_range_self r)⟩
  inj' := by
    intro r s h
    have hv : (typeCRootEmbedding n r : Vec n) =
        (typeCRootEmbedding n s : Vec n) :=
      congrArg (fun x : typeCRootSpan n => (x : Vec n)) h
    have he : typeCRootEmbedding n r = typeCRootEmbedding n s := Subtype.ext hv
    exact typeCRootEmbedding_injective n he

@[simp] public lemma typeCRootInSpan_val (n : ℕ) (r : TypeCRootIndex n) :
    (typeCRootInSpan n r : Vec n) = (typeCRootEmbedding n r : Vec n) := by
  simp [typeCRootInSpan]

public noncomputable def typeCRootDotFunctional (n : ℕ) (r : TypeCRootIndex n) :
    Module.Dual ℝ (typeCRootSpan n) where
  toFun x := dot (typeCRootEmbedding n r : Vec n) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (typeCRootEmbedding n r : Vec n) i * (c * (x : Vec n) i) =
      c * ((typeCRootEmbedding n r : Vec n) i * (x : Vec n) i)
    ring

@[expose] public noncomputable def typeCRootFunctional (n : ℕ) (r : TypeCRootIndex n) :
    Module.Dual ℝ (typeCRootSpan n) :=
  match r with
  | .inl _ => typeCRootDotFunctional n r
  | .inr _ => (1 / 2 : ℝ) • typeCRootDotFunctional n r

public noncomputable def typeCCorootVector (n : ℕ) : TypeCRootIndex n → Vec n
  | .inl r => typeCRootEmbedding n (.inl r)
  | .inr r => (1 / 2 : ℝ) • (typeCRootEmbedding n (.inr r) : Vec n)

public lemma typeCRootFunctional_apply (n : ℕ) (r : TypeCRootIndex n)
    (x : typeCRootSpan n) :
    typeCRootFunctional n r x = dot (typeCCorootVector n r) x.1 := by
  cases r with
  | inl r => rfl
  | inr r =>
      change (1 / 2 : ℝ) * dot (typeCRootEmbedding n (.inr r) : Vec n) x.1 =
        dot ((1 / 2 : ℝ) • (typeCRootEmbedding n (.inr r) : Vec n)) x.1
      rw [dot_smul_left_C]

public lemma typeCRootInSpan_coroot_eval_apply (n : ℕ) (r s : TypeCRootIndex n) :
    Module.Dual.eval ℝ (typeCRootSpan n) (typeCRootInSpan n r)
      (typeCRootFunctional n s) =
      (match s with
      | .inl _ => dot (typeCRootEmbedding n s : Vec n) (typeCRootEmbedding n r : Vec n)
      | .inr _ => (1 / 2 : ℝ) * dot (typeCRootEmbedding n s : Vec n) (typeCRootEmbedding n r : Vec n)) := by
  cases s <;>
    simp [Module.Dual.eval_apply, typeCRootFunctional, typeCRootDotFunctional,
      typeCRootInSpan] <;> rfl

public lemma typeCRootInSpan_coroot_eval (n : ℕ) (r : TypeCRootIndex n) :
    Module.Dual.eval ℝ (typeCRootSpan n) (typeCRootInSpan n r)
      (typeCRootFunctional n r) = 2 := by
  classical
  cases r with
  | inl r =>
      rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
      rw [typeCRootInSpan_coroot_eval_apply]
      change dot (s.1 • basisVector i + t.1 • basisVector j)
        (s.1 • basisVector i + t.1 • basisVector j) = 2
      rcases s.2 with hs | hs <;> rcases t.2 with ht | ht <;>
        rw [hs, ht, dot_add_left_C, dot_smul_left_C, dot_smul_left_C,
          dot_add_right_C, dot_add_right_C, dot_smul_right_C, dot_smul_right_C,
          dot_smul_right_C, dot_smul_right_C] <;>
        simp [dot_basisVector_basisVector_CPairing, hij.ne, hij.ne'] <;> norm_num
  | inr r =>
      rw [typeCRootInSpan_coroot_eval_apply]
      rcases r with ⟨i, b⟩
      cases b <;> simp [typeCRootEmbedding, typeCRootVector, dot, basisVector, Pi.single_apply]

public lemma typeCRootInSpan_span_eq_top (n : ℕ) :
    Submodule.span ℝ (range (typeCRootInSpan n)) = ⊤ := by
  apply top_unique
  intro x hx
  refine Submodule.span_induction
    (p := fun y hy => (⟨y, hy⟩ : typeCRootSpan n) ∈
      Submodule.span ℝ (range (typeCRootInSpan n))) ?_ ?_ ?_ ?_ x.property
  · intro y hy
    obtain ⟨r, rfl⟩ := hy
    exact Submodule.subset_span (mem_range_self r)
  · exact Submodule.zero_mem _
  · intro y z hy hz hym hzm
    exact Submodule.add_mem _ hym hzm
  · intro c y hy hym
    exact Submodule.smul_mem _ c hym

private lemma typeCCorootVector_pair_ne_unit (n : ℕ)
    (r : TypeCPairRootIndex n) (s : Fin n × Bool) :
    typeCCorootVector n (.inl r) ≠ typeCCorootVector n (.inr s) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  rcases s with ⟨k, c⟩
  intro h
  have hi := congrFun h i
  have ha : a.1 = -1 ∨ a.1 = 1 := by
    rcases a.2 with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by simpa only [Set.mem_singleton_iff] using ha)
  by_cases hik : i = k
  · subst k
    have hj := congrFun h j
    have hb : b.1 = -1 ∨ b.1 = 1 := by
      rcases b.2 with hb | hb
      · exact Or.inl hb
      · exact Or.inr (by simpa only [Set.mem_singleton_iff] using hb)
    rcases hb with hb | hb <;> cases c <;>
      norm_num [typeCCorootVector, typeCRootEmbedding, typeCRootVector,
        basisVector, Pi.single_apply, hij.ne', hb] at hj
  · rcases ha with ha | ha <;> cases c <;>
      norm_num [typeCCorootVector, typeCRootEmbedding, typeCRootVector,
        basisVector, Pi.single_apply, hij.ne, hik, ha] at hi

private lemma typeCCorootVector_injective (n : ℕ) :
    Function.Injective (typeCCorootVector n) := by
  intro r s h
  cases r with
  | inl r =>
      cases s with
      | inl s =>
          apply typeCRootEmbedding_injective n
          apply Subtype.ext
          exact h
      | inr s =>
          exact False.elim (typeCCorootVector_pair_ne_unit n r s h)
  | inr r =>
      cases s with
      | inl s =>
          exact False.elim (typeCCorootVector_pair_ne_unit n s r h.symm)
      | inr s =>
          apply typeCRootEmbedding_injective n
          apply Subtype.ext
          have h' : (1 / 2 : ℝ) • (typeCRootEmbedding n (.inr r) : Vec n) =
              (1 / 2 : ℝ) • (typeCRootEmbedding n (.inr s) : Vec n) := h
          exact (isUnit_iff_ne_zero.mpr (show (1 / 2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp h'

public lemma typeCRootFunctional_injective (n : ℕ) :
    Function.Injective (typeCRootFunctional n) := by
  intro r s h
  apply typeCCorootVector_injective n
  funext i
  have hi : basisVector i ∈ typeCRootSpan n := by
    change basisVector i ∈ Submodule.span ℝ (range (fun q : TypeCRootIndex n =>
      (typeCRootEmbedding n q : Vec n)))
    rw [typeCRootEmbedding_span_eq_top]
    exact Submodule.mem_top
  have heval := LinearMap.congr_fun h (⟨basisVector i, hi⟩ : typeCRootSpan n)
  rw [typeCRootFunctional_apply, typeCRootFunctional_apply] at heval
  simpa [dot_basisVector_right_C] using heval

@[expose] public noncomputable def typeCCorootEmbedding (n : ℕ) :
    TypeCRootIndex n ↪ Module.Dual ℝ (typeCRootSpan n) :=
  ⟨typeCRootFunctional n, typeCRootFunctional_injective n⟩

private lemma typeCRootEmbedding_inl_mem_pairRoots (n : ℕ) (r : TypeCPairRootIndex n) :
    (typeCRootEmbedding n (.inl r) : Vec n) ∈ pairRoots n := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  exact ⟨i, j, hij.ne, s.1, t.1, s.2, t.2, rfl⟩

private lemma typeCRootEmbedding_inr_mem_signedDoubleUnitRoots (n : ℕ) (r : Fin n × Bool) :
    (typeCRootEmbedding n (.inr r) : Vec n) ∈ signedDoubleUnitRoots n := by
  rcases r with ⟨i, b⟩
  refine ⟨i, ?_⟩
  cases b <;> simp [typeCRootEmbedding, typeCRootVector]

public lemma typeCRootInSpan_reflection_mapsTo (n : ℕ) (r : TypeCRootIndex n) :
    MapsTo
      (Module.preReflection (typeCRootInSpan n r)
        ((Module.Dual.eval ℝ (typeCRootSpan n)).flip (typeCCorootEmbedding n r)))
      (range (typeCRootInSpan n)) (range (typeCRootInSpan n)) := by
  rintro _ ⟨s, rfl⟩
  rcases typeCRoot_reflection_mapsTo n with ⟨hpair, hunit⟩
  cases r with
  | inl r =>
      have hy := hpair (typeCRootEmbedding n (.inl r) : Vec n)
        (typeCRootEmbedding_inl_mem_pairRoots n r)
        (typeCRootEmbedding n s).property
      let y : typeCRoots n := ⟨
        (typeCRootEmbedding n s : Vec n) -
          dot (typeCRootEmbedding n (.inl r) : Vec n)
            (typeCRootEmbedding n s : Vec n) •
              (typeCRootEmbedding n (.inl r) : Vec n), hy⟩
      obtain ⟨t, ht⟩ := typeCRootEmbedding_surjective n y
      refine ⟨t, ?_⟩
      have htval := congrArg (fun z : typeCRoots n => (z : Vec n)) ht
      dsimp [y] at htval
      apply Subtype.ext
      change (typeCRootEmbedding n t : Vec n) =
        (typeCRootEmbedding n s : Vec n) -
          dot (typeCRootEmbedding n (.inl r) : Vec n)
            (typeCRootEmbedding n s : Vec n) •
              (typeCRootEmbedding n (.inl r) : Vec n)
      exact htval
  | inr r =>
      have hy := hunit (typeCRootEmbedding n (.inr r) : Vec n)
        (typeCRootEmbedding_inr_mem_signedDoubleUnitRoots n r)
        (typeCRootEmbedding n s).property
      let y : typeCRoots n := ⟨
        (typeCRootEmbedding n s : Vec n) -
          ((1 / 2 : ℝ) * dot (typeCRootEmbedding n (.inr r) : Vec n)
            (typeCRootEmbedding n s : Vec n)) •
              (typeCRootEmbedding n (.inr r) : Vec n), hy⟩
      obtain ⟨t, ht⟩ := typeCRootEmbedding_surjective n y
      refine ⟨t, ?_⟩
      have htval := congrArg (fun z : typeCRoots n => (z : Vec n)) ht
      dsimp [y] at htval
      apply Subtype.ext
      change (typeCRootEmbedding n t : Vec n) =
        (typeCRootEmbedding n s : Vec n) -
          ((1 / 2 : ℝ) * dot (typeCRootEmbedding n (.inr r) : Vec n)
            (typeCRootEmbedding n s : Vec n)) •
              (typeCRootEmbedding n (.inr r) : Vec n)
      exact htval

open Set

/-- The pre-reflection defined by a canonical type `D` root preserves the
canonical indexed roots inside their span. -/
public lemma typeDRootInSpan_preReflection_mapsTo (n : ℕ) (r : TypeDRootIndex n) :
    MapsTo
      (Module.preReflection (typeDRootInSpan n r)
        ((Module.Dual.eval ℝ (typeDRootSpan n)).flip (typeDRootFunctional n r)))
      (range (typeDRootInSpan n)) (range (typeDRootInSpan n)) := by
  rintro _ ⟨s, rfl⟩
  have hy := typeDRoot_reflection_mapsTo n
    (typeDRootEmbedding n r : Vec n) (typeDRootEmbedding n r).property
    (typeDRootEmbedding n s).property
  let y : typeDRoots n := ⟨
    (typeDRootEmbedding n s : Vec n) -
      dot (typeDRootEmbedding n r : Vec n)
        (typeDRootEmbedding n s : Vec n) •
          (typeDRootEmbedding n r : Vec n), hy⟩
  obtain ⟨t, ht⟩ := typeDRootEmbedding_surjective n y
  refine ⟨t, ?_⟩
  have htval := congrArg (fun z : typeDRoots n => (z : Vec n)) ht
  dsimp [y] at htval
  apply Subtype.ext
  simpa [Module.preReflection_apply, typeDRootInSpan, typeDRootFunctional,
    typeDRootDotFunctional] using htval

/-- The standard type `A_m` path Cartan matrix. -/
@[expose]
public def typeACartanMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => if i = j then 2 else if i.succ = j.castSucc then -1
    else if j.succ = i.castSucc then -1 else 0

/-- The Cartan matrix of the standard adjacent-root base is the type `A_m` path matrix. -/
public lemma typeARootPairing_base_cartanMatrix (m : ℕ) (i j : Fin m) :
    (typeARootPairing_base m).cartanMatrix
        (typeARootPairing_baseEquiv m i) (typeARootPairing_baseEquiv m j) =
      typeACartanMatrix m i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeARootPairing_pairing]
  simp only [typeARootPairing_baseEquiv_val]
  rw [typeARootEmbedding_simpleRoot, typeARootEmbedding_simpleRoot]
  rw [typeASimpleRoot_dot_typeASimpleRoot]
  simp only [typeACartanMatrix]
  split <;> norm_num

open Set

/-- The concrete coordinate root pairing of type `B_n`, with long roots using
their dot-product coroots and short roots using twice their dot-product coroots. -/
@[expose] public noncomputable def typeBRootPairing (n : ℕ) :
    RootPairing (TypeBRootIndex n) ℝ (typeBRootSpan n) (Module.Dual ℝ (typeBRootSpan n)) :=
  RootPairing.mk'' (Module.Dual.eval ℝ (typeBRootSpan n)) (typeBRootInSpan n)
    (typeBCorootEmbedding n) (typeBRootInSpan_coroot_eval n)
    (typeBRootInSpan_reflection_mapsTo n) (typeBRootInSpan_span_eq_top n)

@[simp] public lemma typeBRootPairing_root (n : ℕ) (r : TypeBRootIndex n) :
    (typeBRootPairing n).root r = typeBRootInSpan n r := rfl

@[simp] public lemma typeBRootPairing_pairing (n : ℕ) (r s : TypeBRootIndex n) :
    (typeBRootPairing n).pairing r s =
      (match s with
      | .inl _ => dot (typeBRootEmbedding n s : Vec n) (typeBRootEmbedding n r : Vec n)
      | .inr _ => 2 * dot (typeBRootEmbedding n s : Vec n) (typeBRootEmbedding n r : Vec n)) := by
  change Module.Dual.eval ℝ (typeBRootSpan n) (typeBRootInSpan n r)
    (typeBCorootEmbedding n s) = _
  exact typeBRootInSpan_coroot_eval_apply n r s

open Set

/-- The concrete coordinate root pairing of type `C_n`, with pair roots using
their dot-product coroots and double-unit roots using half their dot-product coroots. -/
@[expose] public noncomputable def typeCRootPairing (n : ℕ) :
    RootPairing (TypeCRootIndex n) ℝ (typeCRootSpan n) (Module.Dual ℝ (typeCRootSpan n)) :=
  RootPairing.mk'' (Module.Dual.eval ℝ (typeCRootSpan n)) (typeCRootInSpan n)
    (typeCCorootEmbedding n) (typeCRootInSpan_coroot_eval n)
    (typeCRootInSpan_reflection_mapsTo n) (typeCRootInSpan_span_eq_top n)

@[simp] public lemma typeCRootPairing_root (n : ℕ) (r : TypeCRootIndex n) :
    (typeCRootPairing n).root r = typeCRootInSpan n r := rfl

@[simp] public lemma typeCRootPairing_pairing (n : ℕ) (r s : TypeCRootIndex n) :
    (typeCRootPairing n).pairing r s =
      (match s with
      | .inl _ => dot (typeCRootEmbedding n s : Vec n) (typeCRootEmbedding n r : Vec n)
      | .inr _ => (1 / 2 : ℝ) * dot (typeCRootEmbedding n s : Vec n)
          (typeCRootEmbedding n r : Vec n)) := by
  change Module.Dual.eval ℝ (typeCRootSpan n) (typeCRootInSpan n r)
    (typeCCorootEmbedding n s) = _
  exact typeCRootInSpan_coroot_eval_apply n r s

open Set

/-- The pre-reflection defined by the injective Type D coroot embedding preserves
canonical indexed roots in their coordinate span. -/
public lemma typeDRootInSpan_reflection_mapsTo
    (m : ℕ) (r : TypeDRootIndex (m + 2)) :
    MapsTo
      (Module.preReflection (typeDRootInSpan (m + 2) r)
        ((Module.Dual.eval ℝ (typeDRootSpan (m + 2))).flip
          (typeDCorootEmbedding m r)))
      (range (typeDRootInSpan (m + 2))) (range (typeDRootInSpan (m + 2))) := by
  simpa [typeDCorootEmbedding] using
    typeDRootInSpan_preReflection_mapsTo (m + 2) r

open SimpleGraph

/-- A path-numbered Cartan matrix with simple bonds is the standard type-A
Cartan matrix in that numbering. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_pathGraph_eq_typeACartanMatrix_of_simple_bonds
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ)
    (hdiag : ∀ i, A i i = 2)
    {n : ℕ} (e : Fin n ≃ κ)
    (hpath : ∀ i j,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
        (pathGraph n).Adj i j)
    (hsimple : ∀ {i j : Fin n}, (pathGraph n).Adj i j →
      A (e i) (e j) = -1 ∧ A (e j) (e i) = -1) :
    ∀ i j, A (e i) (e j) = typeACartanMatrix n i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeACartanMatrix] using hdiag (e i)
  by_cases hforward : i.succ = j.castSucc
  · rw [typeACartanMatrix, if_neg hij, if_pos hforward]
    have hadj : (pathGraph n).Adj i j := by
      rw [pathGraph_adj]
      exact Or.inl (by simpa using congrArg Fin.val hforward)
    exact (hsimple hadj).1
  by_cases hreverse : j.succ = i.castSucc
  · rw [typeACartanMatrix, if_neg hij, if_neg hforward, if_pos hreverse]
    have hadj : (pathGraph n).Adj i j := by
      rw [pathGraph_adj]
      exact Or.inr (by simpa using congrArg Fin.val hreverse)
    exact (hsimple hadj).1
  rw [typeACartanMatrix, if_neg hij, if_neg hforward, if_neg hreverse]
  by_contra hne
  have hsupp :
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) := by
    rw [SimpleGraph.fromRel_adj]
    exact ⟨e.injective.ne hij, Or.inl hne⟩
  have hadj := (hpath i j).mp hsupp
  rw [pathGraph_adj] at hadj
  rcases hadj with hadj | hadj
  · apply hforward
    exact Fin.ext hadj
  · apply hreverse
    exact Fin.ext hadj

/-- A reduced crystallographic root system whose based Cartan matrix is the standard type `A_m`
path matrix is equivalent to the concrete coordinate type `A_m` root pairing.

This is GLS3, Theorem 1.8.7. -/
public theorem _root_.Theory.AlgebraicGroup.typeA_rootPairing_equiv
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (m : ℕ) (e : Fin m ≃ b.support)
    (he : ∀ i j, b.cartanMatrix (e i) (e j) = typeACartanMatrix m i j) :
    Nonempty (P.Equiv (typeARootPairing m)) := by
  apply rootPairing_equiv_of_cartanMatrix b (typeARootPairing_base m)
    (e.symm.trans (typeARootPairing_baseEquiv m))
  intro i j
  change (typeARootPairing_base m).cartanMatrix
      (typeARootPairing_baseEquiv m (e.symm i))
      (typeARootPairing_baseEquiv m (e.symm j)) = b.cartanMatrix i j
  rw [typeARootPairing_base_cartanMatrix]
  simpa using (he (e.symm i) (e.symm j)).symm

open Set

private lemma typeBRootPairing_pairing_eq_intCast
    (n : ℕ) (r s : TypeBRootIndex n) :
    ∃ z : ℤ, (z : ℝ) = (typeBRootPairing n).pairing r s := by
  let signInt : ({-1, 1} : Set ℝ) → ℤ := fun u => if u.1 = -1 then -1 else 1
  have signInt_cast (u : ({-1, 1} : Set ℝ)) : (signInt u : ℝ) = u.1 := by
    dsimp [signInt]
    by_cases h : u.1 = -1
    · rw [if_pos h, h]
      norm_num
    · rw [if_neg h]
      have hu : u.1 = 1 := by
        rcases u.2 with hu | hu
        · exact (h hu).elim
        · simpa using hu
      rw [hu]
      norm_num
  let rootIntCoordinate : TypeBRootIndex n → Fin n → ℤ := fun q =>
    match q with
    | .inl ⟨⟨⟨i, j⟩, _⟩, u, v⟩ => fun a =>
        signInt u * (if a = i then 1 else 0) +
          signInt v * (if a = j then 1 else 0)
    | .inr ⟨i, false⟩ => fun a => if a = i then 1 else 0
    | .inr ⟨i, true⟩ => fun a => if a = i then -1 else 0
  have root_apply_eq_intCast (q : TypeBRootIndex n) (a : Fin n) :
      (typeBRootEmbedding n q : Vec n) a = (rootIntCoordinate q a : ℝ) := by
    cases q with
    | inl q =>
        rcases q with ⟨⟨⟨i, j⟩, _⟩, u, v⟩
        change (u.1 • basisVector i + v.1 • basisVector j : Vec n) a = _
        rw [← signInt_cast u, ← signInt_cast v]
        simp [rootIntCoordinate, basisVector, Pi.single_apply]
    | inr q =>
        rcases q with ⟨i, b⟩
        cases b
        · change basisVector i a = _
          simp [rootIntCoordinate, basisVector, Pi.single_apply]
        · change (-basisVector i : Vec n) a = _
          by_cases h : a = i <;>
            simp [rootIntCoordinate, basisVector, h]
  have dot_eq_intCast (q t : TypeBRootIndex n) :
      dot (typeBRootEmbedding n t : Vec n) (typeBRootEmbedding n q : Vec n) =
        ((∑ a, rootIntCoordinate t a * rootIntCoordinate q a : ℤ) : ℝ) := by
    simp [dot, root_apply_eq_intCast]
  rw [typeBRootPairing_pairing]
  cases s with
  | inl s =>
      refine ⟨∑ a, rootIntCoordinate (.inl s) a * rootIntCoordinate r a, ?_⟩
      exact (dot_eq_intCast r (.inl s)).symm
  | inr s =>
      refine ⟨2 * ∑ a, rootIntCoordinate (.inr s) a * rootIntCoordinate r a, ?_⟩
      rw [Int.cast_mul, Int.cast_ofNat]
      congr 1
      exact (dot_eq_intCast r (.inr s)).symm

public instance typeBRootPairing_isCrystallographic (n : ℕ) :
    (typeBRootPairing n).IsCrystallographic := by
  constructor
  exact typeBRootPairing_pairing_eq_intCast n

open Set

private noncomputable def typeBSignInt (s : ({-1, 1} : Set ℝ)) : ℤ :=
  if s.1 = -1 then -1 else 1

private lemma typeBSignInt_cast (s : ({-1, 1} : Set ℝ)) :
    (typeBSignInt s : ℝ) = s.1 := by
  unfold typeBSignInt
  by_cases h : s.1 = -1
  · rw [if_pos h, h]
    norm_num
  · rw [if_neg h]
    have hs : s.1 = 1 := by
      rcases s.2 with hs | hs
      · exact (h hs).elim
      · simpa using hs
    rw [hs]
    norm_num

private noncomputable def typeBRootIntCoordinate (n : ℕ) :
    TypeBRootIndex n → Fin n → ℤ
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩ => fun a =>
      typeBSignInt s * (if a = i then 1 else 0) +
        typeBSignInt t * (if a = j then 1 else 0)
  | .inr ⟨i, false⟩ => fun a => if a = i then 1 else 0
  | .inr ⟨i, true⟩ => fun a => if a = i then -1 else 0

private lemma typeBRootEmbedding_apply_eq_intCast
    (n : ℕ) (r : TypeBRootIndex n) (a : Fin n) :
    (typeBRootEmbedding n r : Vec n) a = (typeBRootIntCoordinate n r a : ℝ) := by
  cases r with
  | inl r =>
      rcases r with ⟨⟨⟨i, j⟩, _⟩, s, t⟩
      change (s.1 • basisVector i + t.1 • basisVector j : Vec n) a = _
      rw [← typeBSignInt_cast s, ← typeBSignInt_cast t]
      simp [typeBRootIntCoordinate, basisVector, Pi.single_apply]
  | inr r =>
      rcases r with ⟨i, b⟩
      cases b
      · change basisVector i a = _
        simp [typeBRootIntCoordinate, basisVector, Pi.single_apply]
      · change (-basisVector i : Vec n) a = _
        by_cases h : a = i <;>
          simp [typeBRootIntCoordinate, basisVector, h]

private lemma typeBRootEmbedding_dot_eq_intCast
    (n : ℕ) (r s : TypeBRootIndex n) :
    dot (typeBRootEmbedding n s : Vec n) (typeBRootEmbedding n r : Vec n) =
      ((∑ a, typeBRootIntCoordinate n s a * typeBRootIntCoordinate n r a : ℤ) : ℝ) := by
  simp [dot, typeBRootEmbedding_apply_eq_intCast]

public instance typeBRootPairing_isRootSystem (n : ℕ) :
    (typeBRootPairing n).IsRootSystem := by
  apply RootPairing.isRootSystem_mk''
  intro r s
  change ∃ z : ℤ, (z : ℝ) =
    Module.Dual.eval ℝ (typeBRootSpan n) (typeBRootInSpan n r)
      (typeBRootFunctional n s)
  rw [typeBRootInSpan_coroot_eval_apply]
  cases s with
  | inl s =>
      refine ⟨∑ a, typeBRootIntCoordinate n (.inl s) a *
        typeBRootIntCoordinate n r a, ?_⟩
      exact (typeBRootEmbedding_dot_eq_intCast n r (.inl s)).symm
  | inr s =>
      refine ⟨2 * ∑ a, typeBRootIntCoordinate n (.inr s) a *
        typeBRootIntCoordinate n r a, ?_⟩
      rw [Int.cast_mul, Int.cast_ofNat]
      congr 1
      exact (typeBRootEmbedding_dot_eq_intCast n r (.inr s)).symm

@[expose] public def typeBCartanMatrix (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  fun i j => if i = j then 2 else if i.val + 1 = j.val then
    if j = Fin.last (m + 1) then -2 else -1
  else if j.val + 1 = i.val then -1 else 0

public lemma typeBRootPairing_simpleIndex_pairing (m : ℕ) (i j : Fin (m + 2)) :
    (typeBRootPairing (m + 2)).pairing (typeBSimpleRootIndex m i)
        (typeBSimpleRootIndex m j) =
      algebraMap ℤ ℝ (typeBCartanMatrix m i j) := by
  rw [typeBRootPairing_pairing]
  rw [typeBRootEmbedding_typeBSimpleRootIndex,
    typeBRootEmbedding_typeBSimpleRootIndex]
  by_cases hj : j.val < m + 1
  · have hjlast : j ≠ Fin.last (m + 1) := by
      intro hlast
      subst j
      simp at hj
    simp [typeBSimpleRootIndex, hj]
    rw [dot_comm]
    have hpair := typeBSimpleRoot_pairing m i j
    simp only [if_neg hjlast] at hpair
    rw [hpair]
    simp [typeBCartanMatrix, hjlast]
  · have hjlast : j = Fin.last (m + 1) := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst j
    simp [typeBSimpleRootIndex]
    rw [dot_comm]
    have hpair := typeBSimpleRoot_pairing m i (Fin.last (m + 1))
    simp at hpair
    convert hpair using 1
    simp [typeBCartanMatrix]

open Set

private lemma typeCRootPairing_pairing_eq_intCast
    (n : ℕ) (r s : TypeCRootIndex n) :
    ∃ z : ℤ, (z : ℝ) = (typeCRootPairing n).pairing r s := by
  let signInt : ({-1, 1} : Set ℝ) → ℤ := fun u => if u.1 = -1 then -1 else 1
  have signInt_cast (u : ({-1, 1} : Set ℝ)) : (signInt u : ℝ) = u.1 := by
    dsimp [signInt]
    by_cases h : u.1 = -1
    · rw [if_pos h, h]
      norm_num
    · rw [if_neg h]
      have hu : u.1 = 1 := by
        rcases u.2 with hu | hu
        · exact (h hu).elim
        · simpa using hu
      rw [hu]
      norm_num
  let rootIntCoordinate : TypeCRootIndex n → Fin n → ℤ := fun q =>
    match q with
    | .inl ⟨⟨⟨i, j⟩, _⟩, u, v⟩ => fun a =>
        signInt u * (if a = i then 1 else 0) +
          signInt v * (if a = j then 1 else 0)
    | .inr ⟨i, false⟩ => fun a => if a = i then 2 else 0
    | .inr ⟨i, true⟩ => fun a => if a = i then -2 else 0
  have root_apply_eq_intCast (q : TypeCRootIndex n) (a : Fin n) :
      (typeCRootEmbedding n q : Vec n) a = (rootIntCoordinate q a : ℝ) := by
    cases q with
    | inl q =>
        rcases q with ⟨⟨⟨i, j⟩, _⟩, u, v⟩
        change (u.1 • basisVector i + v.1 • basisVector j : Vec n) a = _
        rw [← signInt_cast u, ← signInt_cast v]
        simp [rootIntCoordinate, basisVector, Pi.single_apply]
    | inr q =>
        rcases q with ⟨i, b⟩
        cases b
        · change (2 • basisVector i : Vec n) a = _
          by_cases h : a = i <;>
            simp [rootIntCoordinate, basisVector, h]
        · change (-2 • basisVector i : Vec n) a = _
          by_cases h : a = i <;>
            simp [rootIntCoordinate, basisVector, h]
  have dot_eq_intCast (q t : TypeCRootIndex n) :
      dot (typeCRootEmbedding n t : Vec n) (typeCRootEmbedding n q : Vec n) =
        ((∑ a, rootIntCoordinate t a * rootIntCoordinate q a : ℤ) : ℝ) := by
    simp [dot, root_apply_eq_intCast]
  rw [typeCRootPairing_pairing]
  cases s with
  | inl s =>
      refine ⟨∑ a, rootIntCoordinate (.inl s) a * rootIntCoordinate r a, ?_⟩
      exact (dot_eq_intCast r (.inl s)).symm
  | inr s =>
      rcases s with ⟨i, b⟩
      cases b
      · refine ⟨rootIntCoordinate r i, ?_⟩
        rw [show (typeCRootEmbedding n (.inr (i, false)) : Vec n) =
          2 • basisVector i by rfl]
        simp [dot, basisVector, Pi.single_apply, root_apply_eq_intCast]
      · refine ⟨-rootIntCoordinate r i, ?_⟩
        rw [show (typeCRootEmbedding n (.inr (i, true)) : Vec n) =
          -2 • basisVector i by rfl]
        simp [dot, basisVector, Pi.single_apply, root_apply_eq_intCast]

public instance typeCRootPairing_isCrystallographic (n : ℕ) :
    (typeCRootPairing n).IsCrystallographic := by
  constructor
  exact typeCRootPairing_pairing_eq_intCast n

public lemma typeCRootPairing_simpleIndex_pairing (m : ℕ) (i j : Fin (m + 1)) :
    (typeCRootPairing (m + 1)).pairing (typeCSimpleRootIndex m i)
        (typeCSimpleRootIndex m j) =
      algebraMap ℤ ℝ (typeCCartanMatrix m i j) := by
  rw [typeCRootPairing_pairing]
  rw [typeCRootEmbedding_typeCSimpleRootIndex,
    typeCRootEmbedding_typeCSimpleRootIndex]
  by_cases hj : j.val < m
  · have hjlast : j ≠ Fin.last m := by
      intro hlast
      subst j
      simp at hj
    simp [typeCSimpleRootIndex, hj]
    rw [dot_comm]
    have hpair := typeCSimpleRoot_pairing m i j
    simp only [if_neg hjlast] at hpair
    rw [hpair]
    simp [typeCCartanMatrix]
  · have hjlast : j = Fin.last m := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst j
    simp [typeCSimpleRootIndex]
    rw [dot_comm]
    have hpair := typeCSimpleRoot_pairing m i (Fin.last m)
    simp at hpair
    convert hpair using 1
    simp [typeCCartanMatrix]

/-- The concrete coordinate root pairing of type `D_{m+2}`. -/
@[expose] public noncomputable def typeDRootPairing (m : ℕ) :
    RootPairing (TypeDRootIndex (m + 2)) ℝ (typeDRootSpan (m + 2))
      (Module.Dual ℝ (typeDRootSpan (m + 2))) :=
  RootPairing.mk'' (Module.Dual.eval ℝ (typeDRootSpan (m + 2)))
    (typeDRootInSpan (m + 2)) (typeDCorootEmbedding m)
    (typeDRootInSpan_coroot_eval (m + 2))
    (typeDRootInSpan_reflection_mapsTo m)
    (typeDRootInSpan_span_eq_top (m + 2))

open Set

private noncomputable def typeBSignIntSupport (s : ({-1, 1} : Set ℝ)) : ℤ :=
  if s.1 = -1 then -1 else 1

private lemma typeBSignIntSupport_cast (s : ({-1, 1} : Set ℝ)) :
    (typeBSignIntSupport s : ℝ) = s.1 := by
  unfold typeBSignIntSupport
  by_cases h : s.1 = -1
  · rw [if_pos h, h]
    norm_num
  · rw [if_neg h]
    have hs : s.1 = 1 := by
      rcases s.2 with hs | hs
      · exact (h hs).elim
      · simpa using hs
    rw [hs]
    norm_num

private noncomputable def typeBRootIntCoordinateSupport (n : ℕ) :
    TypeBRootIndex n → Fin n → ℤ
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩ => fun a =>
      typeBSignIntSupport s * (if a = i then 1 else 0) +
        typeBSignIntSupport t * (if a = j then 1 else 0)
  | .inr ⟨i, false⟩ => fun a => if a = i then 1 else 0
  | .inr ⟨i, true⟩ => fun a => if a = i then -1 else 0

private lemma typeBRootEmbedding_apply_eq_intCast_support
    (n : ℕ) (r : TypeBRootIndex n) (a : Fin n) :
    (typeBRootEmbedding n r : Vec n) a =
      (typeBRootIntCoordinateSupport n r a : ℝ) := by
  cases r with
  | inl r =>
      rcases r with ⟨⟨⟨i, j⟩, _⟩, s, t⟩
      change (s.1 • basisVector i + t.1 • basisVector j : Vec n) a = _
      rw [← typeBSignIntSupport_cast s, ← typeBSignIntSupport_cast t]
      simp [typeBRootIntCoordinateSupport, basisVector, Pi.single_apply]
  | inr r =>
      rcases r with ⟨i, b⟩
      cases b
      · change basisVector i a = _
        simp [typeBRootIntCoordinateSupport, basisVector, Pi.single_apply]
      · change (-basisVector i : Vec n) a = _
        by_cases h : a = i <;>
          simp [typeBRootIntCoordinateSupport, basisVector, h]

private lemma typeBRootEmbedding_dot_eq_intCast_support
    (n : ℕ) (r s : TypeBRootIndex n) :
    dot (typeBRootEmbedding n s : Vec n) (typeBRootEmbedding n r : Vec n) =
      ((∑ a, typeBRootIntCoordinateSupport n s a *
        typeBRootIntCoordinateSupport n r a : ℤ) : ℝ) := by
  simp [dot, typeBRootEmbedding_apply_eq_intCast_support]

private lemma typeBRootPairing_pairing_isInt_support
    (n : ℕ) (r s : TypeBRootIndex n) :
    ∃ z : ℤ, (z : ℝ) = (typeBRootPairing n).pairing r s := by
  rw [typeBRootPairing_pairing]
  cases s with
  | inl s =>
      refine ⟨∑ a, typeBRootIntCoordinateSupport n (.inl s) a *
        typeBRootIntCoordinateSupport n r a, ?_⟩
      exact (typeBRootEmbedding_dot_eq_intCast_support n r (.inl s)).symm
  | inr s =>
      refine ⟨2 * ∑ a, typeBRootIntCoordinateSupport n (.inr s) a *
        typeBRootIntCoordinateSupport n r a, ?_⟩
      rw [Int.cast_mul, Int.cast_ofNat]
      congr 1
      exact (typeBRootEmbedding_dot_eq_intCast_support n r (.inr s)).symm

private lemma dot_smul_self_BSupport {n : ℕ} (c : ℝ) (x : Vec n) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma typeBRootEmbedding_dot_self_support
    (n : ℕ) (r : TypeBRootIndex n) :
    dot (typeBRootEmbedding n r : Vec n) (typeBRootEmbedding n r : Vec n) =
      match r with
      | .inl _ => 2
      | .inr _ => 1 := by
  have h := (typeBRootPairing n).pairing_same r
  rw [typeBRootPairing_pairing] at h
  cases r with
  | inl r => exact h
  | inr r => norm_num at h ⊢; exact h

private lemma int_sq_ne_two_BSupport (z : ℤ) : z ^ 2 ≠ 2 := by
  intro h
  have hlo : (-2 : ℤ) < z := by nlinarith [sq_nonneg (z + 2)]
  have hhi : z < 2 := by nlinarith [sq_nonneg (z - 2)]
  interval_cases z <;> norm_num at h

private lemma int_sq_ne_eight_BSupport (z : ℤ) : z ^ 2 ≠ 8 := by
  intro h
  have hlo : (-3 : ℤ) < z := by nlinarith [sq_nonneg (z + 3)]
  have hhi : z < 3 := by nlinarith [sq_nonneg (z - 3)]
  interval_cases z <;> norm_num at h

public instance typeBRootPairing_isReduced (n : ℕ) :
    (typeBRootPairing n).IsReduced := by
  constructor
  intro r s hdep
  have hsmul := (typeBRootPairing n).pairing_smul_root_eq_of_not_linearIndependent hdep
  have hvec := congrArg Subtype.val hsmul
  simp only [typeBRootPairing_root] at hvec
  change (typeBRootPairing n).pairing s r • (typeBRootEmbedding n r : Vec n) =
    (2 : ℝ) • (typeBRootEmbedding n s : Vec n) at hvec
  have hnorm := congrArg (fun x : Vec n => dot x x) hvec
  rw [dot_smul_self_BSupport, dot_smul_self_BSupport,
    typeBRootEmbedding_dot_self_support, typeBRootEmbedding_dot_self_support] at hnorm
  obtain ⟨z, hz⟩ := typeBRootPairing_pairing_isInt_support n s r
  cases r with
  | inl r =>
      cases s with
      | inl s =>
          have hc : (typeBRootPairing n).pairing (.inl s) (.inl r) = 2 ∨
              (typeBRootPairing n).pairing (.inl s) (.inl r) = -2 := by
            apply eq_or_eq_neg_of_sq_eq_sq
            norm_num at hnorm ⊢
            nlinarith
          rcases hc with hc | hc
          · left
            rw [hc] at hsmul
            exact (isUnit_iff_ne_zero.mpr
              (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
          · right
            rw [hc] at hsmul
            have hs : (2 : ℝ) • (-(typeBRootPairing n).root (.inl r)) =
                (2 : ℝ) • (typeBRootPairing n).root (.inl s) := by
              rw [smul_neg, ← neg_smul]
              exact hsmul
            have hneg : -(typeBRootPairing n).root (.inl r) =
                (typeBRootPairing n).root (.inl s) :=
              (isUnit_iff_ne_zero.mpr
                (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hs
            exact neg_eq_iff_eq_neg.mp hneg
      | inr s =>
          exfalso
          dsimp only at hnorm
          norm_num only at hnorm
          rw [← hz] at hnorm
          have hnormInt : z ^ 2 * 2 = 4 := by
            exact_mod_cast hnorm
          have hzsq : z ^ 2 = 2 := by
            nlinarith
          exact int_sq_ne_two_BSupport z hzsq
  | inr r =>
      cases s with
      | inl s =>
          exfalso
          dsimp only at hnorm
          norm_num only at hnorm
          rw [← hz] at hnorm
          have hnormInt : z ^ 2 * 1 = 8 := by
            exact_mod_cast hnorm
          have hzsq : z ^ 2 = 8 := by
            nlinarith
          exact int_sq_ne_eight_BSupport z hzsq
      | inr s =>
          have hc : (typeBRootPairing n).pairing (.inr s) (.inr r) = 2 ∨
              (typeBRootPairing n).pairing (.inr s) (.inr r) = -2 := by
            apply eq_or_eq_neg_of_sq_eq_sq
            norm_num at hnorm ⊢
            nlinarith
          rcases hc with hc | hc
          · left
            rw [hc] at hsmul
            exact (isUnit_iff_ne_zero.mpr
              (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
          · right
            rw [hc] at hsmul
            have hs : (2 : ℝ) • (-(typeBRootPairing n).root (.inr r)) =
                (2 : ℝ) • (typeBRootPairing n).root (.inr s) := by
              rw [smul_neg, ← neg_smul]
              exact hsmul
            have hneg : -(typeBRootPairing n).root (.inr r) =
                (typeBRootPairing n).root (.inr s) :=
              (isUnit_iff_ne_zero.mpr
                (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hs
            exact neg_eq_iff_eq_neg.mp hneg

/-- A path-numbered matrix with one terminal directed double bond is the
standard type `B` Cartan matrix.  The hypotheses expose only matrix entries
and carry no classification conclusion. -/
public lemma _root_.Theory.AlgebraicGroup.cartan_pathGraph_eq_typeBCartanMatrix_of_terminal_heavy_bond
    {κ : Type*} (A : Matrix κ κ ℤ) {m : ℕ} (e : Fin (m + 2) ≃ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hforward : ∀ {i j : Fin (m + 2)}, i.val + 1 = j.val →
      A (e i) (e j) = if j = Fin.last (m + 1) then -2 else -1)
    (hreverse : ∀ {i j : Fin (m + 2)}, j.val + 1 = i.val →
      A (e i) (e j) = -1)
    (hzero : ∀ {i j : Fin (m + 2)}, i ≠ j → i.val + 1 ≠ j.val →
      j.val + 1 ≠ i.val → A (e i) (e j) = 0) :
    ∀ i j, A (e i) (e j) = typeBCartanMatrix m i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [typeBCartanMatrix] using hdiag i
  by_cases hforward' : i.val + 1 = j.val
  · rw [typeBCartanMatrix, if_neg hij, if_pos hforward']
    exact hforward hforward'
  by_cases hreverse' : j.val + 1 = i.val
  · rw [typeBCartanMatrix, if_neg hij, if_neg hforward', if_pos hreverse']
    exact hreverse hreverse'
  rw [typeBCartanMatrix, if_neg hij, if_neg hforward', if_neg hreverse']
  exact hzero hij hforward' hreverse'

public instance typeCRootPairing_isRootSystem (n : ℕ) :
    (typeCRootPairing n).IsRootSystem := by
  apply RootPairing.isRootSystem_mk''
  exact (typeCRootPairing_isCrystallographic n).exists_value

private lemma dot_smul_self_DSupport {n : ℕ} (c : ℝ) (x : Vec n) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The concrete type `D` root pairing is reduced. -/
public instance typeDRootPairing_isReduced (m : ℕ) :
    (typeDRootPairing m).IsReduced := by
  constructor
  intro r s hdep
  have hsmul := (typeDRootPairing m).pairing_smul_root_eq_of_not_linearIndependent hdep
  have hvec := congrArg Subtype.val hsmul
  change (typeDRootPairing m).pairing s r •
      (typeDRootEmbedding (m + 2) r : Vec (m + 2)) =
    (2 : ℝ) • (typeDRootEmbedding (m + 2) s : Vec (m + 2)) at hvec
  have hself (q : TypeDRootIndex (m + 2)) :
      dot (typeDRootEmbedding (m + 2) q : Vec (m + 2))
        (typeDRootEmbedding (m + 2) q : Vec (m + 2)) = 2 := by
    have h := typeDRootInSpan_coroot_eval (m + 2) q
    change dot (typeDRootEmbedding (m + 2) q : Vec (m + 2))
      (typeDRootEmbedding (m + 2) q : Vec (m + 2)) = 2 at h
    exact h
  have hnorm := congrArg (fun x : Vec (m + 2) => dot x x) hvec
  rw [dot_smul_self_DSupport, dot_smul_self_DSupport, hself, hself] at hnorm
  have hc : (typeDRootPairing m).pairing s r = 2 ∨
      (typeDRootPairing m).pairing s r = -2 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    norm_num at hnorm ⊢
    nlinarith
  rcases hc with hc | hc
  · left
    rw [hc] at hsmul
    exact (isUnit_iff_ne_zero.mpr
      (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
  · right
    rw [hc] at hsmul
    have hs : (2 : ℝ) • (-(typeDRootPairing m).root r) =
        (2 : ℝ) • (typeDRootPairing m).root s := by
      rw [smul_neg, ← neg_smul]
      exact hsmul
    have hneg : -(typeDRootPairing m).root r =
        (typeDRootPairing m).root s :=
      (isUnit_iff_ne_zero.mpr
        (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hs
    exact neg_eq_iff_eq_neg.mp hneg

@[simp] public lemma typeDRootPairing_pairing (m : ℕ)
    (r s : TypeDRootIndex (m + 2)) :
    (typeDRootPairing m).pairing r s =
      dot (typeDRootEmbedding (m + 2) s : Vec (m + 2))
        (typeDRootEmbedding (m + 2) r : Vec (m + 2)) := by
  change Module.Dual.eval ℝ (typeDRootSpan (m + 2))
    (typeDRootInSpan (m + 2) r) (typeDCorootEmbedding m s) = _
  exact typeDRootInSpan_coroot_eval_apply (m + 2) r s

@[simp] public lemma typeDRootPairing_root
    (m : ℕ) (r : TypeDRootIndex (m + 2)) :
    (typeDRootPairing m).root r = typeDRootInSpan (m + 2) r := rfl

open Set

public lemma typeBSimpleRootIndex_injective (m : ℕ) :
    Function.Injective (typeBSimpleRootIndex m) := by
  intro i j h
  by_cases hi : i.val < m + 1 <;> by_cases hj : j.val < m + 1
  · simp [typeBSimpleRootIndex, hi, hj] at h
    exact h.1
  · simp [typeBSimpleRootIndex, hi, hj] at h
  · simp [typeBSimpleRootIndex, hi, hj] at h
  · simp [typeBSimpleRootIndex, hi, hj] at h
    exact h

private lemma dot_basisVector_right_BBase {n : ℕ} (x : Vec n) (j : Fin n) :
    dot x (basisVector j) = x j := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private noncomputable def prefixVector_BBase (m : ℕ) (i : Fin (m + 2)) : Vec (m + 2) :=
  fun k => if k.val ≤ i.val then 1 else 0

private noncomputable def prefixFunctional_BBase (m : ℕ) (i : Fin (m + 2)) :
    typeBRootSpan (m + 2) →ₗ[ℝ] ℝ where
  toFun x := dot (prefixVector_BBase m i) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change prefixVector_BBase m i k * (c * (x : Vec (m + 2)) k) =
      c * (prefixVector_BBase m i k * (x : Vec (m + 2)) k)
    ring

private lemma prefix_simple_BBase (m : ℕ) (i j : Fin (m + 2)) :
    prefixFunctional_BBase m i (typeBRootInSpan (m + 2) (typeBSimpleRootIndex m j)) =
      if i = j then 1 else 0 := by
  rw [show typeBRootInSpan (m + 2) (typeBSimpleRootIndex m j) =
      ⟨typeBRootEmbedding (m + 2) (typeBSimpleRootIndex m j),
        Submodule.subset_span (Set.mem_range_self _)⟩ by
    apply Subtype.ext
    exact typeBRootInSpan_val (m + 2) _]
  change dot (prefixVector_BBase m i)
    (typeBRootEmbedding (m + 2) (typeBSimpleRootIndex m j) : Vec (m + 2)) = _
  rw [typeBRootEmbedding_typeBSimpleRootIndex]
  by_cases hj : j.val < m + 1
  · rw [show typeBSimpleRoot m j =
        basisVector j - basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩ by
      simp [typeBSimpleRoot, hj]]
    rw [show dot (prefixVector_BBase m i)
          (basisVector j - basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩) =
        dot (prefixVector_BBase m i) (basisVector j) -
          dot (prefixVector_BBase m i) (basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩) by
      simp [dot, mul_sub, Finset.sum_sub_distrib]]
    rw [dot_basisVector_right_BBase, dot_basisVector_right_BBase]
    simp only [prefixVector_BBase]
    by_cases h : i = j
    · subst j
      simp
    · by_cases hji : j.val ≤ i.val
      · have hsucc : j.val + 1 ≤ i.val := by omega
        simp [hji, hsucc, h]
      · have hs : ¬j.val + 1 ≤ i.val := by omega
        simp [hji, hs, h]
  · have hjlast : j.val = m + 1 := by omega
    rw [show typeBSimpleRoot m j = basisVector j by simp [typeBSimpleRoot, hj]]
    rw [dot_basisVector_right_BBase]
    simp only [prefixVector_BBase]
    by_cases h : i = j
    · subst j
      simp
    · have hiless : i.val < j.val := by omega
      simp [not_le.mpr hiless, h]

private lemma typeBSimpleRoots_linearIndependent (m : ℕ) :
    LinearIndependent ℝ (fun i : Fin (m + 2) =>
      (typeBRootPairing (m + 2)).root (typeBSimpleRootIndex m i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (prefixFunctional_BBase m i) hg
  simp only [map_sum, map_smul, map_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [typeBRootPairing_root, prefix_simple_BBase] using h
  · intro j hj hji
    rw [typeBRootPairing_root, prefix_simple_BBase]
    simp [hji.symm]
  · simp

public lemma typeBRootPairing_linearIndepOn_simpleRoots (m : ℕ) :
    LinearIndepOn ℝ (typeBRootPairing (m + 2)).root
      (Set.range (typeBSimpleRootIndex m)) := by
  rw [linearIndepOn_range_iff (typeBSimpleRootIndex_injective m)]
  simpa [Function.comp_def] using typeBSimpleRoots_linearIndependent m

private noncomputable def simpleClosure_BBase (m : ℕ) : AddSubmonoid (typeBRootSpan (m + 2)) :=
  AddSubmonoid.closure
    ((typeBRootPairing (m + 2)).root '' Set.range (typeBSimpleRootIndex m))

private lemma simple_mem_BBase (m : ℕ) (i : Fin (m + 2)) :
    (typeBRootPairing (m + 2)).root (typeBSimpleRootIndex m i) ∈ simpleClosure_BBase m := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

private noncomputable def positiveDifferenceIndex_BBase (m : ℕ) (a b : Fin (m + 2))
    (hab : a < b) : TypeBRootIndex (m + 2) :=
  .inl ⟨⟨(a, b), hab⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩

private noncomputable def positiveSumIndex_BBase (m : ℕ) (a b : Fin (m + 2))
    (hab : a < b) : TypeBRootIndex (m + 2) :=
  .inl ⟨⟨(a, b), hab⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

private lemma positiveDifference_mem_BBase (m : ℕ) (a b : Fin (m + 2)) (hab : a < b) :
    (typeBRootPairing (m + 2)).root (positiveDifferenceIndex_BBase m a b hab) ∈
      simpleClosure_BBase m := by
  by_cases hone : b.val = a.val + 1
  · have ha : a.val < m + 1 := by omega
    have hidx : positiveDifferenceIndex_BBase m a b hab = typeBSimpleRootIndex m a := by
      simp [positiveDifferenceIndex_BBase, typeBSimpleRootIndex, ha]
      exact Fin.ext hone
    rw [hidx]
    exact simple_mem_BBase m a
  · let c : Fin (m + 2) := ⟨b.val - 1, by omega⟩
    have hcval : c.val = b.val - 1 := rfl
    have hac : a < c := by rw [Fin.lt_def, hcval]; omega
    have hcb : c < b := by rw [Fin.lt_def, hcval]; omega
    have hleft := positiveDifference_mem_BBase m a c hac
    have hc : c.val < m + 1 := by rw [hcval]; omega
    have hidx : positiveDifferenceIndex_BBase m c b hcb = typeBSimpleRootIndex m c := by
      simp [positiveDifferenceIndex_BBase, typeBSimpleRootIndex, hc]
      apply Fin.ext
      change b.val = c.val + 1
      rw [hcval]
      omega
    have hright : (typeBRootPairing (m + 2)).root
        (positiveDifferenceIndex_BBase m c b hcb) ∈ simpleClosure_BBase m := by
      rw [hidx]
      exact simple_mem_BBase m c
    have hadd := AddSubmonoid.add_mem (simpleClosure_BBase m) hleft hright
    convert hadd using 1
    apply Subtype.ext
    simp [positiveDifferenceIndex_BBase, typeBRootPairing_root, typeBRootInSpan_val,
      typeBRootEmbedding, typeBRootVector]
termination_by b.val
decreasing_by omega

private lemma positiveUnit_mem_BBase (m : ℕ) (a : Fin (m + 2)) :
    (typeBRootPairing (m + 2)).root (.inr (a, false)) ∈ simpleClosure_BBase m := by
  let last : Fin (m + 2) := Fin.last (m + 1)
  by_cases ha : a = last
  · subst a
    have hidx : (Sum.inr (last, false) : TypeBRootIndex (m + 2)) =
        typeBSimpleRootIndex m last := by
      simp [typeBSimpleRootIndex, last]
    rw [hidx]
    exact simple_mem_BBase m last
  · have halt : a < last := lt_of_le_of_ne (Fin.le_last a) ha
    have hdiff := positiveDifference_mem_BBase m a last halt
    have hlast := simple_mem_BBase m last
    have hadd := AddSubmonoid.add_mem (simpleClosure_BBase m) hdiff hlast
    convert hadd using 1
    apply Subtype.ext
    simp [positiveDifferenceIndex_BBase, typeBRootPairing_root, typeBRootInSpan_val,
      typeBRootEmbedding, typeBRootVector, typeBSimpleRootIndex, last]

private lemma positiveSum_mem_BBase (m : ℕ) (a b : Fin (m + 2)) (hab : a < b) :
    (typeBRootPairing (m + 2)).root (positiveSumIndex_BBase m a b hab) ∈ simpleClosure_BBase m := by
  have hdiff := positiveDifference_mem_BBase m a b hab
  have hunit := positiveUnit_mem_BBase m b
  have hdouble := AddSubmonoid.nsmul_mem (simpleClosure_BBase m) hunit 2
  have hadd := AddSubmonoid.add_mem (simpleClosure_BBase m) hdiff hdouble
  convert hadd using 1
  apply Subtype.ext
  simp [positiveSumIndex_BBase, positiveDifferenceIndex_BBase, typeBRootPairing_root,
    typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector, two_nsmul]

public lemma typeBRootPairing_root_mem_or_neg_mem_simpleClosure (m : ℕ)
    (r : TypeBRootIndex (m + 2)) :
    (typeBRootPairing (m + 2)).root r ∈
        AddSubmonoid.closure
          ((typeBRootPairing (m + 2)).root '' Set.range (typeBSimpleRootIndex m)) ∨
      -(typeBRootPairing (m + 2)).root r ∈
        AddSubmonoid.closure
          ((typeBRootPairing (m + 2)).root '' Set.range (typeBSimpleRootIndex m)) := by
  change (typeBRootPairing (m + 2)).root r ∈ simpleClosure_BBase m ∨
    -(typeBRootPairing (m + 2)).root r ∈ simpleClosure_BBase m
  rcases r with r | ⟨i, sign⟩
  · rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    have hs := s.property
    change s.1 = -1 ∨ s.1 = 1 at hs
    have ht := t.property
    change t.1 = -1 ∨ t.1 = 1 at ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · right
      have h := positiveSum_mem_BBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveSumIndex_BBase, typeBRootPairing_root, typeBRootInSpan_val,
        typeBRootEmbedding, typeBRootVector, hs, ht, add_comm]
    · right
      have h := positiveDifference_mem_BBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveDifferenceIndex_BBase, typeBRootPairing_root, typeBRootInSpan_val,
        typeBRootEmbedding, typeBRootVector, hs, ht, add_comm]
    · left
      have h := positiveDifference_mem_BBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveDifferenceIndex_BBase, typeBRootPairing_root, typeBRootInSpan_val,
        typeBRootEmbedding, typeBRootVector, hs, ht]
    · left
      have h := positiveSum_mem_BBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveSumIndex_BBase, typeBRootPairing_root, typeBRootInSpan_val,
        typeBRootEmbedding, typeBRootVector, hs, ht]
  · cases sign
    · left
      exact positiveUnit_mem_BBase m i
    · right
      have h := positiveUnit_mem_BBase m i
      convert h using 1
      apply Subtype.ext
      simp [typeBRootPairing_root, typeBRootInSpan_val, typeBRootEmbedding,
        typeBRootVector]

/-- The standard type `B_{m+2}` base, supported on adjacent differences and
the final positive coordinate root. -/
public noncomputable def typeBRootPairing_base (m : ℕ) :
    (typeBRootPairing (m + 2)).Base :=
  RootPairing.Base.mk' (typeBRootPairing (m + 2)) (Set.range (typeBSimpleRootIndex m))
    (typeBRootPairing_linearIndepOn_simpleRoots m)
    (typeBRootPairing_root_mem_or_neg_mem_simpleClosure m)

public lemma typeBRootPairing_base_support (m : ℕ) :
    ((typeBRootPairing_base m).support : Set (TypeBRootIndex (m + 2))) =
      Set.range (typeBSimpleRootIndex m) := by
  simp [typeBRootPairing_base, RootPairing.Base.mk']

public noncomputable def typeBRootPairing_baseEquiv (m : ℕ) :
    Fin (m + 2) ≃ (typeBRootPairing_base m).support :=
  (Equiv.ofInjective (typeBSimpleRootIndex m) (typeBSimpleRootIndex_injective m)).trans
    (Equiv.setCongr (typeBRootPairing_base_support m).symm)

@[simp]
public lemma typeBRootPairing_baseEquiv_val (m : ℕ) (i : Fin (m + 2)) :
    (typeBRootPairing_baseEquiv m i : TypeBRootIndex (m + 2)) =
      typeBSimpleRootIndex m i := by
  rfl

public lemma typeBRootPairing_simpleRoot_val (m : ℕ) (i : Fin (m + 2)) :
    ((typeBRootPairing (m + 2)).root (typeBSimpleRootIndex m i) : Vec (m + 2)) =
      typeBSimpleRoot m i := by
  rw [typeBRootPairing_root, typeBRootInSpan_val]
  exact typeBRootEmbedding_typeBSimpleRootIndex m i

open Set

private lemma dot_smul_self_CSupport {n : ℕ} (c : ℝ) (x : Vec n) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma typeCRootEmbedding_dot_self_support
    (n : ℕ) (r : TypeCRootIndex n) :
    dot (typeCRootEmbedding n r : Vec n) (typeCRootEmbedding n r : Vec n) =
      match r with
      | .inl _ => 2
      | .inr _ => 4 := by
  have h := (typeCRootPairing n).pairing_same r
  rw [typeCRootPairing_pairing] at h
  cases r with
  | inl r => exact h
  | inr r =>
      norm_num at h ⊢
      nlinarith

private lemma int_sq_ne_two_CSupport (z : ℤ) : z ^ 2 ≠ 2 := by
  intro h
  have hlo : (-2 : ℤ) < z := by nlinarith [sq_nonneg (z + 2)]
  have hhi : z < 2 := by nlinarith [sq_nonneg (z - 2)]
  interval_cases z <;> norm_num at h

private lemma int_sq_ne_eight_CSupport (z : ℤ) : z ^ 2 ≠ 8 := by
  intro h
  have hlo : (-3 : ℤ) < z := by nlinarith [sq_nonneg (z + 3)]
  have hhi : z < 3 := by nlinarith [sq_nonneg (z - 3)]
  interval_cases z <;> norm_num at h

public instance typeCRootPairing_isReduced (n : ℕ) :
    (typeCRootPairing n).IsReduced := by
  constructor
  intro r s hdep
  have hsmul := (typeCRootPairing n).pairing_smul_root_eq_of_not_linearIndependent hdep
  have hvec := congrArg Subtype.val hsmul
  simp only [typeCRootPairing_root] at hvec
  change (typeCRootPairing n).pairing s r • (typeCRootEmbedding n r : Vec n) =
    (2 : ℝ) • (typeCRootEmbedding n s : Vec n) at hvec
  have hnorm := congrArg (fun x : Vec n => dot x x) hvec
  rw [dot_smul_self_CSupport, dot_smul_self_CSupport,
    typeCRootEmbedding_dot_self_support, typeCRootEmbedding_dot_self_support] at hnorm
  obtain ⟨z, hz⟩ := (typeCRootPairing_isCrystallographic n).exists_value s r
  cases r with
  | inl r =>
      cases s with
      | inl s =>
          have hc : (typeCRootPairing n).pairing (.inl s) (.inl r) = 2 ∨
              (typeCRootPairing n).pairing (.inl s) (.inl r) = -2 := by
            apply eq_or_eq_neg_of_sq_eq_sq
            norm_num at hnorm ⊢
            nlinarith
          rcases hc with hc | hc
          · left
            rw [hc] at hsmul
            exact (isUnit_iff_ne_zero.mpr
              (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
          · right
            rw [hc] at hsmul
            have hs : (2 : ℝ) • (-(typeCRootPairing n).root (.inl r)) =
                (2 : ℝ) • (typeCRootPairing n).root (.inl s) := by
              rw [smul_neg, ← neg_smul]
              exact hsmul
            have hneg : -(typeCRootPairing n).root (.inl r) =
                (typeCRootPairing n).root (.inl s) :=
              (isUnit_iff_ne_zero.mpr
                (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hs
            exact neg_eq_iff_eq_neg.mp hneg
      | inr s =>
          exfalso
          dsimp only at hnorm
          norm_num only at hnorm
          rw [← hz] at hnorm
          change (z : ℝ) ^ 2 * 2 = 16 at hnorm
          have hzsqReal : (z : ℝ) ^ 2 = 8 := by
            nlinarith
          have hzsq : z ^ 2 = 8 := by
            exact_mod_cast hzsqReal
          exact int_sq_ne_eight_CSupport z hzsq
  | inr r =>
      cases s with
      | inl s =>
          exfalso
          dsimp only at hnorm
          norm_num only at hnorm
          rw [← hz] at hnorm
          change (z : ℝ) ^ 2 * 4 = 8 at hnorm
          have hzsqReal : (z : ℝ) ^ 2 = 2 := by
            nlinarith
          have hzsq : z ^ 2 = 2 := by
            exact_mod_cast hzsqReal
          exact int_sq_ne_two_CSupport z hzsq
      | inr s =>
          have hc : (typeCRootPairing n).pairing (.inr s) (.inr r) = 2 ∨
              (typeCRootPairing n).pairing (.inr s) (.inr r) = -2 := by
            apply eq_or_eq_neg_of_sq_eq_sq
            norm_num at hnorm ⊢
            nlinarith
          rcases hc with hc | hc
          · left
            rw [hc] at hsmul
            exact (isUnit_iff_ne_zero.mpr
              (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
          · right
            rw [hc] at hsmul
            have hs : (2 : ℝ) • (-(typeCRootPairing n).root (.inr r)) =
                (2 : ℝ) • (typeCRootPairing n).root (.inr s) := by
              rw [smul_neg, ← neg_smul]
              exact hsmul
            have hneg : -(typeCRootPairing n).root (.inr r) =
                (typeCRootPairing n).root (.inr s) :=
              (isUnit_iff_ne_zero.mpr
                (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hs
            exact neg_eq_iff_eq_neg.mp hneg

open Set

private lemma typeDRootPairing_pairing_eq_intCast
    (m : ℕ) (r s : TypeDRootIndex (m + 2)) :
    ∃ z : ℤ, (z : ℝ) = (typeDRootPairing m).pairing r s := by
  let signInt : ({-1, 1} : Set ℝ) → ℤ := fun u => if u.1 = -1 then -1 else 1
  have signInt_cast (u : ({-1, 1} : Set ℝ)) : (signInt u : ℝ) = u.1 := by
    dsimp [signInt]
    by_cases h : u.1 = -1
    · rw [if_pos h, h]
      norm_num
    · rw [if_neg h]
      have hu : u.1 = 1 := by
        rcases u.2 with hu | hu
        · exact (h hu).elim
        · simpa using hu
      rw [hu]
      norm_num
  let rootIntCoordinate : TypeDRootIndex (m + 2) → Fin (m + 2) → ℤ := fun q =>
    match q with
    | ⟨⟨⟨i, j⟩, _⟩, u, v⟩ => fun a =>
        signInt u * (if a = i then 1 else 0) +
          signInt v * (if a = j then 1 else 0)
  have root_apply_eq_intCast (q : TypeDRootIndex (m + 2)) (a : Fin (m + 2)) :
      (typeDRootEmbedding (m + 2) q : Vec (m + 2)) a =
        (rootIntCoordinate q a : ℝ) := by
    rcases q with ⟨⟨⟨i, j⟩, _⟩, u, v⟩
    change (u.1 • basisVector i + v.1 • basisVector j : Vec (m + 2)) a = _
    rw [← signInt_cast u, ← signInt_cast v]
    simp [rootIntCoordinate, basisVector, Pi.single_apply]
  have dot_eq_intCast (q t : TypeDRootIndex (m + 2)) :
      dot (typeDRootEmbedding (m + 2) t : Vec (m + 2))
          (typeDRootEmbedding (m + 2) q : Vec (m + 2)) =
        ((∑ a, rootIntCoordinate t a * rootIntCoordinate q a : ℤ) : ℝ) := by
    simp [dot, root_apply_eq_intCast]
  rw [typeDRootPairing_pairing]
  refine ⟨∑ a, rootIntCoordinate s a * rootIntCoordinate r a, ?_⟩
  exact (dot_eq_intCast r s).symm

public instance typeDRootPairing_isCrystallographic (m : ℕ) :
    (typeDRootPairing m).IsCrystallographic := by
  constructor
  exact typeDRootPairing_pairing_eq_intCast m

private noncomputable def typeDRootSignInt (s : ({-1, 1} : Set ℝ)) : ℤ :=
  if s.1 = -1 then -1 else 1

private lemma typeDRootSignInt_cast (s : ({-1, 1} : Set ℝ)) :
    (typeDRootSignInt s : ℝ) = s.1 := by
  unfold typeDRootSignInt
  by_cases h : s.1 = -1
  · rw [if_pos h, h]
    norm_num
  · rw [if_neg h]
    have hs : s.1 = 1 := by
      rcases s.2 with hs | hs
      · exact (h hs).elim
      · simpa using hs
    rw [hs]
    norm_num

private noncomputable def typeDRootIntCoordinate (n : ℕ) :
    TypeDRootIndex n → Fin n → ℤ
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩ => fun a =>
      typeDRootSignInt s * (if a = i then 1 else 0) +
        typeDRootSignInt t * (if a = j then 1 else 0)

private lemma typeDRootEmbedding_apply_eq_intCast
    (n : ℕ) (r : TypeDRootIndex n) (a : Fin n) :
    (typeDRootEmbedding n r : Vec n) a =
      (typeDRootIntCoordinate n r a : ℝ) := by
  rcases r with ⟨⟨⟨i, j⟩, _⟩, s, t⟩
  change (s.1 • basisVector i + t.1 • basisVector j : Vec n) a = _
  rw [← typeDRootSignInt_cast s, ← typeDRootSignInt_cast t]
  simp [typeDRootIntCoordinate, basisVector, Pi.single_apply]

private lemma typeDRootEmbedding_dot_eq_intCast
    (n : ℕ) (r s : TypeDRootIndex n) :
    dot (typeDRootEmbedding n s : Vec n) (typeDRootEmbedding n r : Vec n) =
      ((∑ a, typeDRootIntCoordinate n s a * typeDRootIntCoordinate n r a : ℤ) : ℝ) := by
  simp [dot, typeDRootEmbedding_apply_eq_intCast]

public instance typeDRootPairing_isRootSystem (n : ℕ) :
    (typeDRootPairing n).IsRootSystem := by
  apply RootPairing.isRootSystem_mk''
  intro r s
  change ∃ z : ℤ, (z : ℝ) =
    Module.Dual.eval ℝ (typeDRootSpan (n + 2)) (typeDRootInSpan (n + 2) r)
      (typeDRootFunctional (n + 2) s)
  rw [typeDRootInSpan_coroot_eval_apply]
  refine ⟨∑ a, typeDRootIntCoordinate (n + 2) s a *
      typeDRootIntCoordinate (n + 2) r a, ?_⟩
  exact (typeDRootEmbedding_dot_eq_intCast (n + 2) r s).symm

/-- The canonical type `D` simple indices have the standard Cartan matrix under
the concrete root pairing. -/
public lemma typeDRootPairing_simpleIndex_pairing
    (m : ℕ) (i j : Fin (m + 2)) :
    (typeDRootPairing m).pairing (typeDSimpleRootIndex m i)
        (typeDSimpleRootIndex m j) = typeDCartanMatrix m i j := by
  rw [typeDRootPairing_pairing]
  exact typeDRootEmbedding_simpleIndex_pairing m i j

@[simp] public lemma typeDRootPairing_root_val (m : ℕ)
    (r : TypeDRootIndex (m + 2)) :
    ((typeDRootPairing m).root r : Vec (m + 2)) =
      (typeDRootEmbedding (m + 2) r : Vec (m + 2)) := by
  rw [typeDRootPairing_root, typeDRootInSpan_val]

public lemma typeDRootPairing_simpleRoot_val (m : ℕ) (i : Fin (m + 2)) :
    ((typeDRootPairing m).root (typeDSimpleRootIndex m i) : Vec (m + 2)) =
      typeDSimpleRoot m i := by
  rw [typeDRootPairing_root, typeDRootInSpan_val]
  exact typeDRootEmbedding_typeDSimpleRootIndex m i

/-- The Cartan matrix of the standard type `B` base is the oriented type `B` path matrix. -/
public lemma typeBRootPairing_base_cartanMatrix (m : ℕ) (i j : Fin (m + 2)) :
    (typeBRootPairing_base m).cartanMatrix
        (typeBRootPairing_baseEquiv m i) (typeBRootPairing_baseEquiv m j) =
      typeBCartanMatrix m i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeBRootPairing_baseEquiv_val, typeBRootPairing_baseEquiv_val]
  exact typeBRootPairing_simpleIndex_pairing m i j

open Set

public lemma typeCSimpleRootIndex_injective (m : ℕ) :
    Function.Injective (typeCSimpleRootIndex m) := by
  intro i j h
  by_cases hi : i.val < m <;> by_cases hj : j.val < m
  · simp [typeCSimpleRootIndex, hi, hj] at h
    exact h.1
  · simp [typeCSimpleRootIndex, hi, hj] at h
  · simp [typeCSimpleRootIndex, hi, hj] at h
  · simp [typeCSimpleRootIndex, hi, hj] at h
    exact h

private lemma dot_basisVector_right_CBase {n : ℕ} (x : Vec n) (j : Fin n) :
    dot x (basisVector j) = x j := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private noncomputable def prefixVector_CBase (m : ℕ) (i : Fin (m + 1)) : Vec (m + 1) :=
  fun k => if i = Fin.last m then 1 / 2 else if k.val ≤ i.val then 1 else 0

private noncomputable def prefixFunctional_CBase (m : ℕ) (i : Fin (m + 1)) :
    typeCRootSpan (m + 1) →ₗ[ℝ] ℝ where
  toFun x := dot (prefixVector_CBase m i) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change prefixVector_CBase m i k * (c * (x : Vec (m + 1)) k) =
      c * (prefixVector_CBase m i k * (x : Vec (m + 1)) k)
    ring

private lemma prefix_simple_CBase (m : ℕ) (i j : Fin (m + 1)) :
    prefixFunctional_CBase m i (typeCRootInSpan (m + 1) (typeCSimpleRootIndex m j)) =
      if i = j then 1 else 0 := by
  rw [show typeCRootInSpan (m + 1) (typeCSimpleRootIndex m j) =
      ⟨typeCRootEmbedding (m + 1) (typeCSimpleRootIndex m j),
        Submodule.subset_span (Set.mem_range_self _)⟩ by
    apply Subtype.ext
    exact typeCRootInSpan_val (m + 1) _]
  change dot (prefixVector_CBase m i)
    (typeCRootEmbedding (m + 1) (typeCSimpleRootIndex m j) : Vec (m + 1)) = _
  rw [typeCRootEmbedding_typeCSimpleRootIndex]
  by_cases hj : j.val < m
  · rw [show typeCSimpleRoot m j =
        basisVector j - basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩ by
      simp [typeCSimpleRoot, hj]]
    rw [show dot (prefixVector_CBase m i)
          (basisVector j - basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩) =
        dot (prefixVector_CBase m i) (basisVector j) -
          dot (prefixVector_CBase m i) (basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩) by
      simp [dot, mul_sub, Finset.sum_sub_distrib]]
    rw [dot_basisVector_right_CBase, dot_basisVector_right_CBase]
    simp only [prefixVector_CBase]
    by_cases hilast : i = Fin.last m
    · subst i
      have hne : Fin.last m ≠ j := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_last] at hval
        omega
      simp [hne]
    · by_cases h : i = j
      · subst j
        simp [hilast]
      · by_cases hji : j.val ≤ i.val
        · have hsucc : j.val + 1 ≤ i.val := by omega
          simp [hilast, hji, hsucc, h]
        · have hs : ¬j.val + 1 ≤ i.val := by omega
          simp [hilast, hji, hs, h]
  · have hjlast : j = Fin.last m := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst j
    rw [show typeCSimpleRoot m (Fin.last m) = 2 • basisVector (Fin.last m) by
      simp [typeCSimpleRoot]]
    rw [show dot (prefixVector_CBase m i) (2 • basisVector (Fin.last m)) =
        2 * dot (prefixVector_CBase m i) (basisVector (Fin.last m)) by
      simp only [dot]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Pi.smul_apply]
      ring]
    rw [dot_basisVector_right_CBase]
    by_cases hilast : i = Fin.last m
    · simp [prefixVector_CBase, hilast]
    · have hlt : i.val < m := by
        have hle := i.isLt
        omega
      simp [prefixVector_CBase, hilast, hlt]

private lemma typeCSimpleRoots_linearIndependent (m : ℕ) :
    LinearIndependent ℝ (fun i : Fin (m + 1) =>
      (typeCRootPairing (m + 1)).root (typeCSimpleRootIndex m i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (prefixFunctional_CBase m i) hg
  simp only [map_sum, map_smul, map_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [typeCRootPairing_root, prefix_simple_CBase] using h
  · intro j hj hji
    rw [typeCRootPairing_root, prefix_simple_CBase]
    simp [hji.symm]
  · simp

public lemma typeCRootPairing_linearIndepOn_simpleRoots (m : ℕ) :
    LinearIndepOn ℝ (typeCRootPairing (m + 1)).root
      (Set.range (typeCSimpleRootIndex m)) := by
  rw [linearIndepOn_range_iff (typeCSimpleRootIndex_injective m)]
  simpa [Function.comp_def] using typeCSimpleRoots_linearIndependent m

private noncomputable def simpleClosure_CBase (m : ℕ) : AddSubmonoid (typeCRootSpan (m + 1)) :=
  AddSubmonoid.closure
    ((typeCRootPairing (m + 1)).root '' Set.range (typeCSimpleRootIndex m))

private lemma simple_mem_CBase (m : ℕ) (i : Fin (m + 1)) :
    (typeCRootPairing (m + 1)).root (typeCSimpleRootIndex m i) ∈ simpleClosure_CBase m := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

private noncomputable def positiveDifferenceIndex_CBase (m : ℕ) (a b : Fin (m + 1))
    (hab : a < b) : TypeCRootIndex (m + 1) :=
  .inl ⟨⟨(a, b), hab⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩

private noncomputable def positiveSumIndex_CBase (m : ℕ) (a b : Fin (m + 1))
    (hab : a < b) : TypeCRootIndex (m + 1) :=
  .inl ⟨⟨(a, b), hab⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

private lemma positiveDifference_mem_CBase (m : ℕ) (a b : Fin (m + 1)) (hab : a < b) :
    (typeCRootPairing (m + 1)).root (positiveDifferenceIndex_CBase m a b hab) ∈
      simpleClosure_CBase m := by
  by_cases hone : b.val = a.val + 1
  · have ha : a.val < m := by omega
    have hidx : positiveDifferenceIndex_CBase m a b hab = typeCSimpleRootIndex m a := by
      simp [positiveDifferenceIndex_CBase, typeCSimpleRootIndex, ha]
      exact Fin.ext hone
    rw [hidx]
    exact simple_mem_CBase m a
  · let c : Fin (m + 1) := ⟨b.val - 1, by omega⟩
    have hcval : c.val = b.val - 1 := rfl
    have hac : a < c := by rw [Fin.lt_def, hcval]; omega
    have hcb : c < b := by rw [Fin.lt_def, hcval]; omega
    have hleft := positiveDifference_mem_CBase m a c hac
    have hc : c.val < m := by rw [hcval]; omega
    have hidx : positiveDifferenceIndex_CBase m c b hcb = typeCSimpleRootIndex m c := by
      simp [positiveDifferenceIndex_CBase, typeCSimpleRootIndex, hc]
      apply Fin.ext
      change b.val = c.val + 1
      rw [hcval]
      omega
    have hright : (typeCRootPairing (m + 1)).root
        (positiveDifferenceIndex_CBase m c b hcb) ∈ simpleClosure_CBase m := by
      rw [hidx]
      exact simple_mem_CBase m c
    have hadd := AddSubmonoid.add_mem (simpleClosure_CBase m) hleft hright
    convert hadd using 1
    apply Subtype.ext
    simp [positiveDifferenceIndex_CBase, typeCRootPairing_root, typeCRootInSpan_val,
      typeCRootEmbedding, typeCRootVector]
termination_by b.val
decreasing_by omega

private lemma positiveDouble_mem_CBase (m : ℕ) (a : Fin (m + 1)) :
    (typeCRootPairing (m + 1)).root (.inr (a, false)) ∈ simpleClosure_CBase m := by
  let last : Fin (m + 1) := Fin.last m
  by_cases ha : a = last
  · subst a
    have hidx : (Sum.inr (last, false) : TypeCRootIndex (m + 1)) =
        typeCSimpleRootIndex m last := by
      simp [typeCSimpleRootIndex, last]
    rw [hidx]
    exact simple_mem_CBase m last
  · have halt : a < last := lt_of_le_of_ne (Fin.le_last a) ha
    have halast : a ≠ Fin.last m := by simpa [last] using ha
    have hdiff := positiveDifference_mem_CBase m a last halt
    have htwice := AddSubmonoid.nsmul_mem (simpleClosure_CBase m) hdiff 2
    have hlast := simple_mem_CBase m last
    have hadd := AddSubmonoid.add_mem (simpleClosure_CBase m) htwice hlast
    convert hadd using 1
    apply Subtype.ext
    ext k
    simp [positiveDifferenceIndex_CBase, typeCRootPairing_root, typeCRootInSpan_val,
      typeCRootEmbedding, typeCRootVector, typeCSimpleRootIndex, last, two_nsmul,
      basisVector, Pi.single_apply]
    by_cases hka : k = a <;> by_cases hkl : k = Fin.last m <;>
      simp [hka, hkl, halast, halast.symm] <;> norm_num

private lemma positiveSum_mem_CBase (m : ℕ) (a b : Fin (m + 1)) (hab : a < b) :
    (typeCRootPairing (m + 1)).root (positiveSumIndex_CBase m a b hab) ∈ simpleClosure_CBase m := by
  have hdiff := positiveDifference_mem_CBase m a b hab
  have hdouble := positiveDouble_mem_CBase m b
  have hadd := AddSubmonoid.add_mem (simpleClosure_CBase m) hdiff hdouble
  convert hadd using 1
  apply Subtype.ext
  ext k
  have habne : a ≠ b := ne_of_lt hab
  simp [positiveSumIndex_CBase, positiveDifferenceIndex_CBase, typeCRootPairing_root,
    typeCRootInSpan_val, typeCRootEmbedding, typeCRootVector, basisVector,
    Pi.single_apply]
  by_cases hka : k = a <;> by_cases hkb : k = b
  all_goals simp [hka, hkb, habne, habne.symm] <;> norm_num

public lemma typeCRootPairing_root_mem_or_neg_mem_simpleClosure (m : ℕ)
    (r : TypeCRootIndex (m + 1)) :
    (typeCRootPairing (m + 1)).root r ∈
        AddSubmonoid.closure
          ((typeCRootPairing (m + 1)).root '' Set.range (typeCSimpleRootIndex m)) ∨
      -(typeCRootPairing (m + 1)).root r ∈
        AddSubmonoid.closure
          ((typeCRootPairing (m + 1)).root '' Set.range (typeCSimpleRootIndex m)) := by
  change (typeCRootPairing (m + 1)).root r ∈ simpleClosure_CBase m ∨
    -(typeCRootPairing (m + 1)).root r ∈ simpleClosure_CBase m
  rcases r with r | ⟨i, sign⟩
  · rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    have hs := s.property
    change s.1 = -1 ∨ s.1 = 1 at hs
    have ht := t.property
    change t.1 = -1 ∨ t.1 = 1 at ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · right
      have h := positiveSum_mem_CBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveSumIndex_CBase, typeCRootPairing_root, typeCRootInSpan_val,
        typeCRootEmbedding, typeCRootVector, hs, ht, add_comm]
    · right
      have h := positiveDifference_mem_CBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveDifferenceIndex_CBase, typeCRootPairing_root, typeCRootInSpan_val,
        typeCRootEmbedding, typeCRootVector, hs, ht, add_comm]
    · left
      have h := positiveDifference_mem_CBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveDifferenceIndex_CBase, typeCRootPairing_root, typeCRootInSpan_val,
        typeCRootEmbedding, typeCRootVector, hs, ht]
    · left
      have h := positiveSum_mem_CBase m i j hij
      convert h using 1
      apply Subtype.ext
      simp [positiveSumIndex_CBase, typeCRootPairing_root, typeCRootInSpan_val,
        typeCRootEmbedding, typeCRootVector, hs, ht]
  · cases sign
    · left
      exact positiveDouble_mem_CBase m i
    · right
      have h := positiveDouble_mem_CBase m i
      convert h using 1
      apply Subtype.ext
      simp [typeCRootPairing_root, typeCRootInSpan_val, typeCRootEmbedding,
        typeCRootVector]

/-- The standard type `C_{m+1}` base, supported on adjacent differences and
the final positive double-coordinate root. -/
public noncomputable def typeCRootPairing_base (m : ℕ) :
    (typeCRootPairing (m + 1)).Base :=
  RootPairing.Base.mk' (typeCRootPairing (m + 1)) (Set.range (typeCSimpleRootIndex m))
    (typeCRootPairing_linearIndepOn_simpleRoots m)
    (typeCRootPairing_root_mem_or_neg_mem_simpleClosure m)

public lemma typeCRootPairing_base_support (m : ℕ) :
    ((typeCRootPairing_base m).support : Set (TypeCRootIndex (m + 1))) =
      Set.range (typeCSimpleRootIndex m) := by
  simp [typeCRootPairing_base, RootPairing.Base.mk']

public noncomputable def typeCRootPairing_baseEquiv (m : ℕ) :
    Fin (m + 1) ≃ (typeCRootPairing_base m).support :=
  (Equiv.ofInjective (typeCSimpleRootIndex m) (typeCSimpleRootIndex_injective m)).trans
    (Equiv.setCongr (typeCRootPairing_base_support m).symm)

@[simp]
public lemma typeCRootPairing_baseEquiv_val (m : ℕ) (i : Fin (m + 1)) :
    (typeCRootPairing_baseEquiv m i : TypeCRootIndex (m + 1)) =
      typeCSimpleRootIndex m i := by
  rfl

public lemma typeCRootPairing_simpleRoot_val (m : ℕ) (i : Fin (m + 1)) :
    ((typeCRootPairing (m + 1)).root (typeCSimpleRootIndex m i) : Vec (m + 1)) =
      typeCSimpleRoot m i := by
  rw [typeCRootPairing_root, typeCRootInSpan_val]
  exact typeCRootEmbedding_typeCSimpleRootIndex m i

open Set

public lemma typeDSimpleRootIndex_injective (m : ℕ) :
    Function.Injective (typeDSimpleRootIndex m) := by
  intro i j h
  by_cases hi : i.val < m + 1 <;> by_cases hj : j.val < m + 1
  · simp [typeDSimpleRootIndex, hi, hj] at h
    exact h.1
  · simp [typeDSimpleRootIndex, hi, hj] at h
    norm_num at h
  · simp [typeDSimpleRootIndex, hi, hj] at h
    norm_num at h
  · apply Fin.ext
    omega

private lemma dot_basisVector_right_DBase {n : ℕ} (x : Vec n) (j : Fin n) :
    dot x (basisVector j) = x j := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private noncomputable def dualVector (m : ℕ) (i : Fin (m + 2)) : Vec (m + 2) :=
  fun k =>
    if i.val < m then
      if k.val ≤ i.val then 1 else 0
    else if i.val = m then
      if k.val ≤ m then 1 / 2 else -1 / 2
    else
      1 / 2

private noncomputable def dualFunctional (m : ℕ) (i : Fin (m + 2)) :
    typeDRootSpan (m + 2) →ₗ[ℝ] ℝ where
  toFun x := dot (dualVector m i) x.1
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change dualVector m i k * (c * (x : Vec (m + 2)) k) =
      c * (dualVector m i k * (x : Vec (m + 2)) k)
    ring

private lemma dual_simple (m : ℕ) (i j : Fin (m + 2)) :
    dualFunctional m i (typeDRootInSpan (m + 2) (typeDSimpleRootIndex m j)) =
      if i = j then 1 else 0 := by
  rw [show typeDRootInSpan (m + 2) (typeDSimpleRootIndex m j) =
      ⟨typeDRootEmbedding (m + 2) (typeDSimpleRootIndex m j),
        Submodule.subset_span (Set.mem_range_self _)⟩ by
    apply Subtype.ext
    exact typeDRootInSpan_val (m + 2) _]
  change dot (dualVector m i)
    (typeDRootEmbedding (m + 2) (typeDSimpleRootIndex m j) : Vec (m + 2)) = _
  rw [typeDRootEmbedding_typeDSimpleRootIndex]
  by_cases hj : j.val < m + 1
  · rw [show typeDSimpleRoot m j =
        basisVector j - basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩ by
      simp [typeDSimpleRoot, hj]]
    rw [show dot (dualVector m i)
          (basisVector j - basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩) =
        dot (dualVector m i) (basisVector j) -
          dot (dualVector m i) (basisVector ⟨j.val + 1, Nat.succ_lt_succ hj⟩) by
      simp [dot, mul_sub, Finset.sum_sub_distrib]]
    rw [dot_basisVector_right_DBase, dot_basisVector_right_DBase]
    simp only [dualVector]
    by_cases hi : i.val < m
    · by_cases h : i = j
      · subst j
        simp [hi]
      · by_cases hji : j.val ≤ i.val
        · have hsucc : j.val + 1 ≤ i.val := by omega
          simp [hi, hji, hsucc, h]
        · have hs : ¬j.val + 1 ≤ i.val := by omega
          simp [hi, hji, hs, h]
    · by_cases him : i.val = m
      · by_cases h : i = j
        · subst j
          simp [him]
          norm_num
        · have hji : j.val < m ∨ j.val = m := by omega
          rcases hji with hji | hji
          · have hjle : j.val ≤ m := by omega
            simp [him, hji, hjle, h]
          · have hij : i = j := Fin.ext (him.trans hji.symm)
            exact (h hij).elim
      · have hilast : i.val = m + 1 := by omega
        have hne : i ≠ j := by
          intro hij
          have := congrArg Fin.val hij
          omega
        simp [hilast, hne]
  · have hjlast : j.val = m + 1 := by omega
    rw [show typeDSimpleRoot m j =
        basisVector ⟨m, by omega⟩ + basisVector ⟨m + 1, by omega⟩ by
      simp [typeDSimpleRoot, hj]]
    rw [show dot (dualVector m i)
          (basisVector ⟨m, by omega⟩ + basisVector ⟨m + 1, by omega⟩) =
        dot (dualVector m i) (basisVector ⟨m, by omega⟩) +
          dot (dualVector m i) (basisVector ⟨m + 1, by omega⟩) by
      simp [dot, mul_add, Finset.sum_add_distrib]]
    rw [dot_basisVector_right_DBase, dot_basisVector_right_DBase]
    by_cases hi : i.val < m
    · have hne : i ≠ j := by
        intro hij
        have := congrArg Fin.val hij
        omega
      have hmnot : ¬m ≤ i.val := by omega
      have hm1not : ¬m + 1 ≤ i.val := by omega
      simp [dualVector, hi, hmnot, hm1not, hne]
    · by_cases him : i.val = m
      · have hne : i ≠ j := by
          intro hij
          have := congrArg Fin.val hij
          omega
        simp [dualVector, him, hne]
        norm_num
      · have hilast : i = j := by
          apply Fin.ext
          omega
        subst j
        simp [dualVector, hi, him]
        norm_num

private lemma typeDSimpleRoots_linearIndependent (m : ℕ) :
    LinearIndependent ℝ (fun i : Fin (m + 2) =>
      (typeDRootPairing m).root (typeDSimpleRootIndex m i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (dualFunctional m i) hg
  simp only [map_sum, map_smul, map_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [typeDRootPairing_root, dual_simple] using h
  · intro j hj hji
    rw [typeDRootPairing_root, dual_simple]
    simp [hji.symm]
  · simp

public lemma typeDRootPairing_linearIndepOn_simpleRoots (m : ℕ) :
    LinearIndepOn ℝ (typeDRootPairing m).root
      (Set.range (typeDSimpleRootIndex m)) := by
  rw [linearIndepOn_range_iff (typeDSimpleRootIndex_injective m)]
  simpa [Function.comp_def] using typeDSimpleRoots_linearIndependent m

private noncomputable def simpleClosure_DBase (m : ℕ) : AddSubmonoid (typeDRootSpan (m + 2)) :=
  AddSubmonoid.closure
    ((typeDRootPairing m).root '' Set.range (typeDSimpleRootIndex m))

private lemma simple_mem_DBase (m : ℕ) (i : Fin (m + 2)) :
    (typeDRootPairing m).root (typeDSimpleRootIndex m i) ∈ simpleClosure_DBase m := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

private noncomputable def positiveDifferenceIndex_DBase (m : ℕ) (a b : Fin (m + 2))
    (hab : a < b) : TypeDRootIndex (m + 2) :=
  ⟨⟨(a, b), hab⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩

private noncomputable def positiveSumIndex_DBase (m : ℕ) (a b : Fin (m + 2))
    (hab : a < b) : TypeDRootIndex (m + 2) :=
  ⟨⟨(a, b), hab⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

private lemma positiveDifference_mem_DBase (m : ℕ) (a b : Fin (m + 2)) (hab : a < b) :
    (typeDRootPairing m).root (positiveDifferenceIndex_DBase m a b hab) ∈
      simpleClosure_DBase m := by
  by_cases hone : b.val = a.val + 1
  · have ha : a.val < m + 1 := by omega
    have hidx : positiveDifferenceIndex_DBase m a b hab = typeDSimpleRootIndex m a := by
      simp [positiveDifferenceIndex_DBase, typeDSimpleRootIndex, ha]
      exact Fin.ext hone
    rw [hidx]
    exact simple_mem_DBase m a
  · let c : Fin (m + 2) := ⟨b.val - 1, by omega⟩
    have hcval : c.val = b.val - 1 := rfl
    have hac : a < c := by rw [Fin.lt_def, hcval]; omega
    have hcb : c < b := by rw [Fin.lt_def, hcval]; omega
    have hleft := positiveDifference_mem_DBase m a c hac
    have hc : c.val < m + 1 := by rw [hcval]; omega
    have hidx : positiveDifferenceIndex_DBase m c b hcb = typeDSimpleRootIndex m c := by
      simp [positiveDifferenceIndex_DBase, typeDSimpleRootIndex, hc]
      apply Fin.ext
      change b.val = c.val + 1
      rw [hcval]
      omega
    have hright : (typeDRootPairing m).root
        (positiveDifferenceIndex_DBase m c b hcb) ∈ simpleClosure_DBase m := by
      rw [hidx]
      exact simple_mem_DBase m c
    have hadd := AddSubmonoid.add_mem (simpleClosure_DBase m) hleft hright
    convert hadd using 1
    apply Subtype.ext
    simp [positiveDifferenceIndex_DBase, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding, typeDRootVector]
termination_by b.val
decreasing_by omega

private lemma terminalPositiveSum_mem (m : ℕ) (a : Fin (m + 2))
    (ha : a < Fin.last (m + 1)) :
    (typeDRootPairing m).root
        (positiveSumIndex_DBase m a (Fin.last (m + 1)) ha) ∈ simpleClosure_DBase m := by
  let forkLeft : Fin (m + 2) := ⟨m, by omega⟩
  let last : Fin (m + 2) := Fin.last (m + 1)
  have hlast : last = ⟨m + 1, by omega⟩ := by
    apply Fin.ext
    simp [last]
  by_cases hafork : a = forkLeft
  · have hidx : positiveSumIndex_DBase m a last ha =
        typeDSimpleRootIndex m last := by
      simp [positiveSumIndex_DBase, typeDSimpleRootIndex, forkLeft, last, hafork]
      exact hlast
    rw [hidx]
    exact simple_mem_DBase m last
  · have haforklt : a < forkLeft := by
      rw [Fin.lt_def]
      change a.val < m
      have hale : a.val ≤ m := by
        have haval : a.val < m + 1 := by
          simpa [last] using (Fin.lt_def.mp ha)
        omega
      have hneval : a.val ≠ m := by
        intro h
        apply hafork
        exact Fin.ext h
      omega
    have hdiff := positiveDifference_mem_DBase m a forkLeft haforklt
    have hfork := simple_mem_DBase m last
    have hadd := AddSubmonoid.add_mem (simpleClosure_DBase m) hdiff hfork
    convert hadd using 1
    apply Subtype.ext
    simp [positiveSumIndex_DBase, positiveDifferenceIndex_DBase, typeDRootPairing_root,
      typeDRootInSpan_val, typeDRootEmbedding, typeDRootVector,
      typeDSimpleRootIndex, forkLeft, last]
    exact congrArg basisVector hlast

private lemma positiveSum_mem_DBase (m : ℕ) (a b : Fin (m + 2)) (hab : a < b) :
    (typeDRootPairing m).root (positiveSumIndex_DBase m a b hab) ∈ simpleClosure_DBase m := by
  let last : Fin (m + 2) := Fin.last (m + 1)
  by_cases hblast : b = last
  · subst b
    exact terminalPositiveSum_mem m a hab
  · have hblastlt : b < last := lt_of_le_of_ne (Fin.le_last b) hblast
    have hdiffAB := positiveDifference_mem_DBase m a b hab
    have hdiffBLast := positiveDifference_mem_DBase m b last hblastlt
    have hsumBLast := terminalPositiveSum_mem m b hblastlt
    have hadd := AddSubmonoid.add_mem (simpleClosure_DBase m)
      (AddSubmonoid.add_mem (simpleClosure_DBase m) hdiffAB hdiffBLast) hsumBLast
    convert hadd using 1
    apply Subtype.ext
    simp [positiveSumIndex_DBase, positiveDifferenceIndex_DBase, typeDRootPairing_root,
      typeDRootInSpan_val, typeDRootEmbedding, typeDRootVector, last]
    module

public lemma typeDRootPairing_root_mem_or_neg_mem_simpleClosure (m : ℕ)
    (r : TypeDRootIndex (m + 2)) :
    (typeDRootPairing m).root r ∈
        AddSubmonoid.closure
          ((typeDRootPairing m).root '' Set.range (typeDSimpleRootIndex m)) ∨
      -(typeDRootPairing m).root r ∈
        AddSubmonoid.closure
          ((typeDRootPairing m).root '' Set.range (typeDSimpleRootIndex m)) := by
  change (typeDRootPairing m).root r ∈ simpleClosure_DBase m ∨
    -(typeDRootPairing m).root r ∈ simpleClosure_DBase m
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  have hs := s.property
  change s.1 = -1 ∨ s.1 = 1 at hs
  have ht := t.property
  change t.1 = -1 ∨ t.1 = 1 at ht
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · right
    have h := positiveSum_mem_DBase m i j hij
    convert h using 1
    apply Subtype.ext
    simp [positiveSumIndex_DBase, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding, typeDRootVector, hs, ht, add_comm]
  · right
    have h := positiveDifference_mem_DBase m i j hij
    convert h using 1
    apply Subtype.ext
    simp [positiveDifferenceIndex_DBase, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding, typeDRootVector, hs, ht, add_comm]
  · left
    have h := positiveDifference_mem_DBase m i j hij
    convert h using 1
    apply Subtype.ext
    simp [positiveDifferenceIndex_DBase, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding, typeDRootVector, hs, ht]
  · left
    have h := positiveSum_mem_DBase m i j hij
    convert h using 1
    apply Subtype.ext
    simp [positiveSumIndex_DBase, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding, typeDRootVector, hs, ht]

/-- The standard type `D_{m+2}` base, supported on adjacent differences and
the final fork root. -/
@[expose] public noncomputable def typeDRootPairing_base (m : ℕ) :
    (typeDRootPairing m).Base :=
  RootPairing.Base.mk' (typeDRootPairing m) (Set.range (typeDSimpleRootIndex m))
    (typeDRootPairing_linearIndepOn_simpleRoots m)
    (typeDRootPairing_root_mem_or_neg_mem_simpleClosure m)

/-! Remark 1.8.8: concrete coordinate models are provided by the standard
root-pairing constructions used below. -/
/-- A reduced crystallographic root system whose based Cartan matrix is the standard type `B_{m+2}`
path matrix is equivalent to the concrete coordinate type `B_{m+2}` root pairing. -/
public theorem _root_.Theory.AlgebraicGroup.typeB_rootPairing_equiv
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (m : ℕ) (e : Fin (m + 2) ≃ b.support)
    (he : ∀ i j, b.cartanMatrix (e i) (e j) = typeBCartanMatrix m i j) :
    Nonempty (P.Equiv (typeBRootPairing (m + 2))) := by
  apply rootPairing_equiv_of_cartanMatrix b (typeBRootPairing_base m)
    (e.symm.trans (typeBRootPairing_baseEquiv m))
  intro i j
  change (typeBRootPairing_base m).cartanMatrix
      (typeBRootPairing_baseEquiv m (e.symm i))
      (typeBRootPairing_baseEquiv m (e.symm j)) = b.cartanMatrix i j
  rw [typeBRootPairing_base_cartanMatrix]
  simpa using (he (e.symm i) (e.symm j)).symm

/-- The Cartan matrix of the standard type `C` base is the oriented type `C` path matrix. -/
public lemma typeCRootPairing_base_cartanMatrix (m : ℕ) (i j : Fin (m + 1)) :
    (typeCRootPairing_base m).cartanMatrix
        (typeCRootPairing_baseEquiv m i) (typeCRootPairing_baseEquiv m j) =
      typeCCartanMatrix m i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeCRootPairing_baseEquiv_val, typeCRootPairing_baseEquiv_val]
  exact typeCRootPairing_simpleIndex_pairing m i j

public lemma typeDRootPairing_base_support (m : ℕ) :
    ((typeDRootPairing_base m).support : Set (TypeDRootIndex (m + 2))) =
      Set.range (typeDSimpleRootIndex m) := by
  simp [typeDRootPairing_base, RootPairing.Base.mk']

/-- A reduced crystallographic root system whose based Cartan matrix is the standard type `C_{m+1}`
path matrix is equivalent to the concrete coordinate type `C_{m+1}` root pairing.

This is GLS3, Theorem 1.8.7. -/
public theorem _root_.Theory.AlgebraicGroup.typeC_rootPairing_equiv
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (m : ℕ) (e : Fin (m + 1) ≃ b.support)
    (he : ∀ i j, b.cartanMatrix (e i) (e j) = typeCCartanMatrix m i j) :
    Nonempty (P.Equiv (typeCRootPairing (m + 1))) := by
  apply rootPairing_equiv_of_cartanMatrix b (typeCRootPairing_base m)
    (e.symm.trans (typeCRootPairing_baseEquiv m))
  intro i j
  change (typeCRootPairing_base m).cartanMatrix
      (typeCRootPairing_baseEquiv m (e.symm i))
      (typeCRootPairing_baseEquiv m (e.symm j)) = b.cartanMatrix i j
  rw [typeCRootPairing_base_cartanMatrix]
  simpa using (he (e.symm i) (e.symm j)).symm

/-- The standard Type D simple-root indices identify the support of its base. -/
@[expose] public noncomputable def typeDRootPairing_baseEquiv (m : ℕ) :
    Fin (m + 2) ≃ (typeDRootPairing_base m).support :=
  (Equiv.ofInjective (typeDSimpleRootIndex m)
      (typeDSimpleRootIndex_injective m)).trans
    (Equiv.setCongr (typeDRootPairing_base_support m).symm)

@[simp] public lemma typeDRootPairing_baseEquiv_val
    (m : ℕ) (i : Fin (m + 2)) :
    (typeDRootPairing_baseEquiv m i : TypeDRootIndex (m + 2)) =
      typeDSimpleRootIndex m i := by
  rfl

/-- The Cartan matrix of the standard type `D` base is the type `D` matrix. -/
public lemma typeDRootPairing_base_cartanMatrix (m : ℕ) (i j : Fin (m + 2)) :
    (typeDRootPairing_base m).cartanMatrix
        (typeDRootPairing_baseEquiv m i) (typeDRootPairing_baseEquiv m j) =
      typeDCartanMatrix m i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  have hi : (((typeDRootPairing_baseEquiv m i : (typeDRootPairing_base m).support) :
      TypeDRootIndex (m + 2))) = typeDSimpleRootIndex m i := by
    rw [typeDRootPairing_baseEquiv]
    simp only [Equiv.trans_apply]
    change ((Equiv.setCongr (typeDRootPairing_base_support m).symm
      (⟨typeDSimpleRootIndex m i, _⟩)) : TypeDRootIndex (m + 2)) = _
    rfl
  have hj : (((typeDRootPairing_baseEquiv m j : (typeDRootPairing_base m).support) :
      TypeDRootIndex (m + 2))) = typeDSimpleRootIndex m j := by
    rw [typeDRootPairing_baseEquiv]
    simp only [Equiv.trans_apply]
    change ((Equiv.setCongr (typeDRootPairing_base_support m).symm
      (⟨typeDSimpleRootIndex m j, _⟩)) : TypeDRootIndex (m + 2)) = _
    rfl
  rw [hi, hj]
  exact typeDRootPairing_simpleIndex_pairing m i j

/-- A reduced crystallographic root system whose based Cartan matrix is the standard type `D_{m+2}`
matrix is equivalent to the concrete coordinate type `D_{m+2}` root pairing.

This is GLS3, Theorem 1.8.7. -/
public theorem _root_.Theory.AlgebraicGroup.typeD_rootPairing_equiv
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (m : ℕ) (e : Fin (m + 2) ≃ b.support)
    (he : ∀ i j, b.cartanMatrix (e i) (e j) = typeDCartanMatrix m i j) :
    Nonempty (P.Equiv (typeDRootPairing m)) := by
  apply rootPairing_equiv_of_cartanMatrix b (typeDRootPairing_base m)
    (e.symm.trans (typeDRootPairing_baseEquiv m))
  intro i j
  change (typeDRootPairing_base m).cartanMatrix
      (typeDRootPairing_baseEquiv m (e.symm i))
      (typeDRootPairing_baseEquiv m (e.symm j)) = b.cartanMatrix i j
  rw [typeDRootPairing_base_cartanMatrix]
  simpa using (he (e.symm i) (e.symm j)).symm

end StandardRootSystem

end Theory.AlgebraicGroup
