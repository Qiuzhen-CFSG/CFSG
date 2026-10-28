module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
public import Theory.AlgebraicGroup.RootSystems.Coordinate

/-! Spin and half-spin weight indices. -/

namespace Theory.AlgebraicGroup

open StandardRootSystem

/-- Independent labels for the even half-spin weight basis in rank `m + 1`. -/
@[expose]
public def EvenHalfSpinIndex (m : ℕ) := Fin m → Bool

/-- Independent labels for the odd half-spin weight basis in rank `m + 1`. -/
@[expose]
public def OddHalfSpinIndex (m : ℕ) := Fin m → Bool

/-- Labels for all spin weights in rank `m`. -/
@[expose]
public def SpinIndex (m : ℕ) := Fin m → Bool

public instance (m : ℕ) : Fintype (EvenHalfSpinIndex m) := by
  change Fintype (Fin m → Bool)
  infer_instance

public instance (m : ℕ) : Fintype (OddHalfSpinIndex m) := by
  change Fintype (Fin m → Bool)
  infer_instance

public instance (m : ℕ) : Fintype (SpinIndex m) := by
  change Fintype (Fin m → Bool)
  infer_instance

/-- Extend a sign string by the unique first sign making the number of
negative signs even. -/
@[expose]
public noncomputable def evenSignExtension {m : ℕ} (tail : EvenHalfSpinIndex m) :
    Fin (m + 1) → Bool := by
  classical
  exact if evenNegative tail then Fin.cons true tail else Fin.cons false tail

/-- Extend a sign string by the unique first sign making the number of
negative signs odd. -/
@[expose]
public noncomputable def oddSignExtension {m : ℕ} (tail : OddHalfSpinIndex m) :
    Fin (m + 1) → Bool := by
  classical
  exact if evenNegative tail then Fin.cons false tail else Fin.cons true tail

public lemma evenNegative_cons_true {m : ℕ} (tail : Fin m → Bool) :
    evenNegative (Fin.cons true tail) ↔ evenNegative tail := by
  simp only [evenNegative, Fin.card_filter_univ_succ']
  simp

public lemma evenNegative_cons_false {m : ℕ} (tail : Fin m → Bool) :
    evenNegative (Fin.cons false tail) ↔ ¬ evenNegative tail := by
  simp only [evenNegative, Fin.card_filter_univ_succ']
  simp [parity_simps]

public lemma evenNegative_evenSignExtension {m : ℕ}
    (tail : EvenHalfSpinIndex m) : evenNegative (evenSignExtension tail) := by
  by_cases h : evenNegative tail
  · rw [evenSignExtension, if_pos h]
    exact (evenNegative_cons_true tail).mpr h
  · rw [evenSignExtension, if_neg h]
    exact (evenNegative_cons_false tail).mpr h

public lemma not_evenNegative_oddSignExtension {m : ℕ}
    (tail : OddHalfSpinIndex m) : ¬ evenNegative (oddSignExtension tail) := by
  by_cases h : evenNegative tail
  · rw [oddSignExtension, if_pos h]
    intro hA
    exact absurd h ((evenNegative_cons_false tail).mp hA)
  · rw [oddSignExtension, if_neg h]
    intro hA
    exact absurd ((evenNegative_cons_true tail).mp hA) h

public lemma evenSignExtension_injective {m : ℕ} :
    Function.Injective (evenSignExtension (m := m)) := by
  intro left right h
  change @Eq (Fin m → Bool) left right
  have htail (ε : EvenHalfSpinIndex m) :
      ∀ j : Fin m, evenSignExtension ε (Fin.succ j) = ε j := by
    intro j
    simp only [evenSignExtension]
    by_cases h : evenNegative ε
    · simp [h]
      exact congrFun (Fin.cons_comp_succ true (ε : Fin m → Bool)) j
    · simp [h]
      exact congrFun (Fin.cons_comp_succ false (ε : Fin m → Bool)) j
  funext i
  have hsi := congrFun h (Fin.succ i)
  rw [htail left i, htail right i] at hsi
  exact hsi

public lemma oddSignExtension_injective {m : ℕ} :
    Function.Injective (oddSignExtension (m := m)) := by
  intro left right h
  change @Eq (Fin m → Bool) left right
  have htail (ε : OddHalfSpinIndex m) :
      ∀ j : Fin m, oddSignExtension ε (Fin.succ j) = ε j := by
    intro j
    simp only [oddSignExtension]
    by_cases h : evenNegative ε
    · simp [h]
      exact congrFun (Fin.cons_comp_succ false (ε : Fin m → Bool)) j
    · simp [h]
      exact congrFun (Fin.cons_comp_succ true (ε : Fin m → Bool)) j
  funext i
  have hsi := congrFun h (Fin.succ i)
  rw [htail left i, htail right i] at hsi
  exact hsi

public lemma halfSignVector_injective {m : ℕ} :
    Function.Injective (halfSignVector (n := m)) := by
  intro left right h
  funext i
  have hi := congrFun h i
  cases hleft : left i <;> cases hright : right i <;>
    simp [halfSignVector, hleft, hright] at hi ⊢ <;> norm_num at hi

public lemma signExtension_range_union (m : ℕ) :
    Set.range (evenSignExtension (m := m)) ∪
      Set.range (oddSignExtension (m := m)) = Set.univ := by
  ext signs
  simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  by_cases htail : evenNegative (Fin.tail signs)
  · cases hhead : signs 0 with
    | false =>
        right
        refine ⟨Fin.tail signs, ?_⟩
        simpa [oddSignExtension, htail, hhead] using Fin.cons_self_tail signs
    | true =>
        left
        refine ⟨Fin.tail signs, ?_⟩
        simpa [evenSignExtension, htail, hhead] using Fin.cons_self_tail signs
  · cases hhead : signs 0 with
    | false =>
        left
        refine ⟨Fin.tail signs, ?_⟩
        simpa [evenSignExtension, htail, hhead] using Fin.cons_self_tail signs
    | true =>
        right
        refine ⟨Fin.tail signs, ?_⟩
        simpa [oddSignExtension, htail, hhead] using Fin.cons_self_tail signs

/-- The standard weights indexed by even sign strings in rank `m + 1`. -/
@[expose]
public noncomputable def evenHalfSpinWeight
    {m : ℕ} (index : EvenHalfSpinIndex m) : Vec (m + 1) :=
  halfSignVector (evenSignExtension index)

/-- The standard weights indexed by odd sign strings in rank `m + 1`. -/
@[expose]
public noncomputable def oddHalfSpinWeight
    {m : ℕ} (index : OddHalfSpinIndex m) : Vec (m + 1) :=
  halfSignVector (oddSignExtension index)

end Theory.AlgebraicGroup
