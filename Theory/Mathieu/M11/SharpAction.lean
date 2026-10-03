module

public import Theory.GroupTheory.SharpTransitivity
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Index

/-!
# Cardinal constraints on sharply four-transitive actions of degree eleven

Sharp transitivity identifies the group with the ordered four-tuples, giving
order 7920. The 462 five-subsets cannot form one orbit, since an orbit's size
divides the group order. This is the counting obstruction used in constructing
the invariant Witt design in Jordan's degree-eleven theorem (Hall, *The Theory
of Groups*, Theorem 5.8.1; cited by Wong (1964), p. 108).
-/

namespace Sporadic.Mathieu

open scoped Pointwise

variable {G : Type*} [Group G] [MulAction G (Fin 11)]

/-- Sharp four-transitivity on eleven points forces the order 7920. -/
public theorem sharpFour_degreeEleven_card
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4) :
    Nat.card G = 7920 := by
  have hc := h.natCard_eq_descFactorial (Fin.castLEEmb (by decide : 4 ≤ 11))
  norm_num [Nat.descFactorial] at hc
  exact hc

/-- A sharply four-transitive degree-eleven action is not transitive on five-subsets. -/
public theorem sharpFour_degreeEleven_not_fiveHomogeneous
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4) :
    ¬ (∀ B : Finset (Fin 11), B.card = 5 →
      ∀ C : Finset (Fin 11), C.card = 5 → ∃ g : G, g • B = C) := by
  classical
  intro ht
  let B : Finset (Fin 11) := Finset.univ.map (Fin.castLEEmb (by decide : 5 ≤ 11))
  have hB : B.card = 5 := by simp [B]
  have horbit : MulAction.orbit G B =
      ((Finset.univ : Finset (Fin 11)).powersetCard 5 : Set (Finset (Fin 11))) := by
    ext C
    simp only [Finset.mem_coe, Finset.mem_powersetCard_univ]
    constructor
    · rintro ⟨g, rfl⟩
      simpa only [Finset.card_smul_finset] using hB
    · intro hC
      exact ht B hB C hC
  have hdvd := (MulAction.stabilizer G B).index_dvd_card
  rw [MulAction.index_stabilizer, horbit, Set.ncard_coe_finset,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    sharpFour_degreeEleven_card h] at hdvd
  norm_num [Nat.choose] at hdvd

end Sporadic.Mathieu
