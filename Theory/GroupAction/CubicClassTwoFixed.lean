module

public import Theory.GroupAction.Quotient
public import Theory.GroupTheory.ClassTwoCommutator

/-!
# Cubic fixed points in a group of class two

Let a three-group act coprimely on a finite solvable group P of class at
most two. For a fixed element t, the centralizer C_P(t) is normal and
invariant. If every fixed element commuted with t, coprime lifting would
make the quotient P/C_P(t) fixed-point-free. Orbit counting would then
force its order to be one modulo three.

In particular, a centralizer of index eight cannot contain every fixed
element. This is the odd-dimensional cubic-action obstruction in
Aschbacher–Smith, Lemma J.2.3(7), printed p.434 (combined manuscript of
1 March 2004). It uses the actual quotient action; the source application
supplies its index from the full commutator image.
-/

public section
open Subgroup

namespace Subgroup.ClassTwo
variable {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
    [MulDistribMulAction A P]

/-- A fixed element with centralizer index different from one modulo three
does not commute with all the fixed subgroup. -/
theorem exists_fixed_not_commute_of_index
    (hc : _root_.commutator P ≤ center P) (hA : IsPGroup 3 A)
    (hsolv : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (t : P) (ht : t ∈ FixedPoints.subgroup A P)
    (hi : (centralizer ({t} : Set P)).index % 3 ≠ 1) :
    ∃ x ∈ FixedPoints.subgroup A P, ¬ Commute t x := by
  classical
  by_contra! hn
  let C := centralizer ({t} : Set P)
  let _ : C.Normal := centralizer_normal hc t
  have hInv : IsInvariant A P C := by
    constructor
    intro a x
    change x ∈ centralizer ({t} : Set P) ↔ a • x ∈ centralizer ({t} : Set P)
    simp only [mem_centralizer_singleton_iff]
    have ht' : a • t = t := ht a
    constructor
    · intro hx
      simpa only [smul_mul', ht'] using congrArg (a • ·) hx
    · intro hx
      apply (MulDistribMulAction.toMulAut A P a).injective
      change a • (x * t) = a • (t * x)
      simpa only [smul_mul', ht'] using hx
  let _ : MulDistribMulAction A (P ⧸ C) := quotientMulDistribMulAction C hInv
  have hf : FixedPoints.subgroup A (P ⧸ C) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop C hInv]
    apply bot_unique
    rintro _ ⟨x, hx, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact mem_centralizer_singleton_iff.mpr (hn x hx).eq.symm
  have hmod := hA.card_modEq_card_fixedPoints (P ⧸ C)
  change Nat.card (P ⧸ C) % 3 =
    Nat.card (FixedPoints.subgroup A (P ⧸ C)) % 3 at hmod
  rw [hf, card_bot] at hmod
  exact hi hmod

end Subgroup.ClassTwo
