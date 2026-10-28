module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Order.Fin.Basic
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Small alternating-group centralizers and restricted mixed-pair fibers

The sign map on a symmetric-group centralizer has an odd element, so its
kernel, the alternating-group centralizer, has half its order. An odd
commuting permutation also prevents splitting of the relevant symmetric
conjugacy classes in the alternating group. Finally, mixed-pair fibers are
identified with pairs in the two classes inside the target centralizer.

These are the structural ingredients for the finite counts used in
Aschbacher, “A 2-local characterization of M12”, Proposition 3.3, p.38.
-/

@[expose] public section

namespace alternatingGroup.EightNineInvolutionCounts
open Equiv Equiv.Perm Subgroup
abbrev A8 := alternatingGroup (Fin 8)
abbrev A9 := alternatingGroup (Fin 9)
def z8 : A8 := ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, by simp [mem_alternatingGroup, map_mul]⟩
def t8 : A8 := ⟨swap 0 1 * swap 2 3, by simp [mem_alternatingGroup, map_mul]⟩
def z9 : A9 := ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, by simp [mem_alternatingGroup, map_mul]⟩
def t9 : A9 := ⟨swap 0 1 * swap 2 3, by simp [mem_alternatingGroup, map_mul]⟩

variable {α : Type*} [Fintype α] [DecidableEq α]
theorem isConj_iff_of_odd_commuting (a b : alternatingGroup α)
    (s : Perm α) (hs : sign s = -1) (hc : Commute s (a : Perm α)) :
    IsConj a b ↔ (a : Perm α).cycleType = (b : Perm α).cycleType := by
  constructor
  · intro h
    exact isConj_iff_cycleType_eq.mp ((alternatingGroup α).subtype.map_isConj h)
  · intro h
    obtain ⟨p, hp⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr h)
    rcases Int.units_eq_one_or (sign p) with he | he
    · exact isConj_iff.mpr ⟨⟨p, mem_alternatingGroup.mpr he⟩, Subtype.ext hp⟩
    · refine isConj_iff.mpr ⟨⟨p * s, mem_alternatingGroup.mpr ?_⟩, Subtype.ext ?_⟩
      · rw [map_mul, he, hs]; decide
      · change p * s * (a : Perm α) * (p * s)⁻¹ = (b : Perm α)
        calc
          _ = p * (s * (a : Perm α) * s⁻¹) * p⁻¹ := by group
          _ = p * (a : Perm α) * p⁻¹ := by rw [hc.eq, mul_inv_cancel_right]
          _ = _ := hp

theorem two_mul_card_centralizer (a : alternatingGroup α)
    (s : Perm α) (hs : sign s = -1) (hsc : Commute s (a : Perm α)) :
    Nat.card (centralizer ({a} : Set (alternatingGroup α))) * 2 =
      Nat.card (centralizer ({(a : Perm α)} : Set (Perm α))) := by
  let C := centralizer ({(a : Perm α)} : Set (Perm α))
  let χ : C →* ℤˣ := sign.comp C.subtype
  have hχ : Function.Surjective χ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨⟨s, mem_centralizer_singleton_iff.mpr hsc.eq⟩, hs⟩
  have hi : χ.ker.index = 2 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hχ, Nat.card_congr topEquiv.toEquiv]
    simp [Nat.card_eq_fintype_card]
  let e : χ.ker ≃ centralizer ({a} : Set (alternatingGroup α)) := {
    toFun := fun x => ⟨⟨x.val.val, mem_alternatingGroup.mpr x.property⟩,
      mem_centralizer_singleton_iff.mpr (Subtype.ext
        (mem_centralizer_singleton_iff.mp x.val.property))⟩
    invFun := fun x => ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
      mem_alternatingGroup.mp x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hk := χ.ker.card_mul_index
  rw [hi, Nat.card_congr e] at hk
  exact hk

theorem card_centralizer_z8 : Nat.card (centralizer ({z8} : Set A8)) = 192 := by
  have hc := two_mul_card_centralizer z8 (swap 0 1) (by decide) (by change _ * _ = _ * _; decide)
  rw [nat_card_centralizer] at hc
  have ht : (z8 : Perm (Fin 8)).cycleType = {2,2,2,2} := by decide
  rw [ht] at hc
  norm_num [Nat.factorial] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hc

theorem card_centralizer_t9 : Nat.card (centralizer ({t9} : Set A9)) = 480 := by
  have hc := two_mul_card_centralizer t9 (swap 0 1) (by decide) (by change _ * _ = _ * _; decide)
  rw [nat_card_centralizer] at hc
  have ht : (t9 : Perm (Fin 9)).cycleType = {2,2} := by decide
  rw [ht] at hc
  norm_num [Nat.factorial] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hc
end alternatingGroup.EightNineInvolutionCounts

namespace alternatingGroup.EightNineInvolutionCounts
open Equiv Equiv.Perm Subgroup
open Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G]
abbrev CentralizerClass (z u : G) := {a : centralizer ({u} : Set G) // IsConj z (a : G)}
noncomputable def centralizerClassEquiv {m k : ℕ} (z u : G)
    (e : Fin m ≃ centralizer ({u} : Set G)) (s : Fin k → Fin m)
    (hs : Function.Injective s)
    (hc : ∀ j, IsConj z (e j : G) ↔ ∃ i, s i = j) :
    Fin k ≃ CentralizerClass z u := by
  let f : Fin k → CentralizerClass z u := fun i => ⟨e (s i), (hc _).mpr ⟨i, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact hs (e.injective (congrArg Subtype.val h))
  · intro a
    obtain ⟨i, hi⟩ := (hc (e.symm a.val)).mp (by simpa using a.property)
    exact ⟨i, Subtype.ext (by change e (s i) = a.val; rw [hi, e.apply_symm_apply])⟩

noncomputable def restrictedFiberEquiv [Finite G] (z v u : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v) :
    Fiber z v u ≃ {p : CentralizerClass z u × CentralizerClass v u //
      halfOrder (p.1.val : G) (p.2.val : G) = u} where
  toFun p := ⟨(⟨⟨p.val.1, (fiber_mem_centralizer hz hv hn p).1⟩, p.property.1⟩,
    ⟨⟨p.val.2, (fiber_mem_centralizer hz hv hn p).2⟩, p.property.2.1⟩), p.property.2.2⟩
  invFun p := ⟨((p.val.1.val : G), (p.val.2.val : G)), p.val.1.property,
    p.val.2.property, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem kappa_eq_card [Finite G] {r s : ℕ} (z v u : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (a : Fin r ≃ CentralizerClass z u) (b : Fin s ≃ CentralizerClass v u) :
    kappa z v u = Nat.card {p : Fin r × Fin s //
      halfOrder ((a p.1).val : G) ((b p.2).val : G) = u} := by
  rw [show kappa z v u = Nat.card (Fiber z v u) by
    simp only [kappa_def, Fiber, halfOrder_def]]
  have he := Equiv.subtypeEquiv (Equiv.prodCongr a b)
    (p := fun p : Fin r × Fin s => halfOrder ((a p.1).val : G) ((b p.2).val : G) = u)
    (q := fun p : CentralizerClass z u × CentralizerClass v u =>
      halfOrder (p.1.val : G) (p.2.val : G) = u) (fun _ => Iff.rfl)
  exact (Nat.card_congr (restrictedFiberEquiv z v u hz hv hn)).trans
    (Nat.card_congr he).symm

theorem z8_order : orderOf z8 = 2 := orderOf_eq_prime (by decide) (by decide)

theorem z8_cycleType : (z8 : Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by decide

theorem z8_isConj (a : A8) : IsConj z8 a ↔
    (a : Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  rw [isConj_iff_of_odd_commuting z8 a (swap 0 1) (by decide)
    (by change _ * _ = _ * _; decide), z8_cycleType, eq_comm]

theorem t8_order : orderOf t8 = 2 := orderOf_eq_prime (by decide) (by decide)

theorem t8_cycleType : (t8 : Perm (Fin 8)).cycleType = {2, 2} := by decide

theorem t8_isConj (a : A8) : IsConj t8 a ↔
    (a : Perm (Fin 8)).cycleType = {2, 2} := by
  rw [isConj_iff_of_odd_commuting t8 a (swap 0 1) (by decide)
    (by change _ * _ = _ * _; decide), t8_cycleType, eq_comm]

theorem z9_order : orderOf z9 = 2 := orderOf_eq_prime (by decide) (by decide)

theorem z9_cycleType : (z9 : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by decide

theorem z9_isConj (a : A9) : IsConj z9 a ↔
    (a : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  rw [isConj_iff_of_odd_commuting z9 a (swap 0 1) (by decide)
    (by change _ * _ = _ * _; decide), z9_cycleType, eq_comm]

theorem t9_order : orderOf t9 = 2 := orderOf_eq_prime (by decide) (by decide)

theorem t9_cycleType : (t9 : Perm (Fin 9)).cycleType = {2, 2} := by decide

theorem t9_isConj (a : A9) : IsConj t9 a ↔
    (a : Perm (Fin 9)).cycleType = {2, 2} := by
  rw [isConj_iff_of_odd_commuting t9 a (swap 0 1) (by decide)
    (by change _ * _ = _ * _; decide), t9_cycleType, eq_comm]

theorem z8_not_conjugate_t8 : ¬ IsConj z8 t8 := by
  rw [z8_isConj, t8_cycleType]
  decide

theorem z9_not_conjugate_t9 : ¬ IsConj z9 t9 := by
  rw [z9_isConj, t9_cycleType]
  decide

variable {α : Type*} [Fintype α] [DecidableEq α]
theorem halfOrder_eq_iff (a b u : alternatingGroup α) :
    halfOrder a b = u ↔ ((a : Perm α) * (b : Perm α)) ^
      (((a : Perm α) * (b : Perm α)).cycleType.lcm / 2) = (u : Perm α) := by
  rw [halfOrder_def, Subtype.ext_iff]
  rw [lcm_cycleType, ← Subgroup.coe_mul, Subgroup.orderOf_coe, Subgroup.coe_pow]
end alternatingGroup.EightNineInvolutionCounts

end
