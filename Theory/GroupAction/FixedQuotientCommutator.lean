module

public import Theory.GroupAction.Lemmas
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# An invariant subgroup carrying the full fixed quotient

Let a group act by automorphisms on a finite abelian group `V`. If an
invariant subgroup `U` has the same quotient by its fixed points as `V`,
then `U C_V(A)=V` and `[V,A]≤U`. The numerical hypothesis is written after
clearing denominators, so it involves only finite group cardinalities.

Relative-index multiplicativity and the product formula give the covering
assertion. Decomposing each vector into a member of `U` and a fixed vector
then puts each action commutator in `U` by invariance.

This supplies the full-module containment used in Stellmacher (1.6),
journal p.18, under the numerical equality established in its bounded
exceptional case; see `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

public theorem commutatorAction_le_of_fixed_card_product_eq
    {A V : Type*} [Group A] [Group V] [Finite V] [IsMulCommutative V]
    [MulDistribMulAction A V]
    (U : Subgroup V) [IsInvariant A V U]
    (hcard : Nat.card U * Nat.card (FixedPoints.subgroup A V) =
      Nat.card V * Nat.card (U ⊓ FixedPoints.subgroup A V : Subgroup V)) :
    U ⊔ FixedPoints.subgroup A V = ⊤ ∧ commutatorAction A V ≤ U := by
  let C : Subgroup V := FixedPoints.subgroup A V
  let D : Subgroup V := U ⊔ C
  let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
  have hU : Nat.card (U ⊓ C : Subgroup V) * C.relIndex U = Nat.card U := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup V) (U ⊓ C) U bot_le inf_le_left
  have hD : Nat.card C * C.relIndex U = Nat.card D := by
    have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup V) C D bot_le le_sup_right
    simpa only [Subgroup.relIndex_bot_left, D, Subgroup.relIndex_sup_right] using h
  have hDcard : Nat.card D = Nat.card V := by
    apply Nat.eq_of_mul_eq_mul_right (m := Nat.card (U ⊓ C : Subgroup V)) Nat.card_pos
    calc
      Nat.card D * Nat.card (U ⊓ C : Subgroup V) =
          Nat.card U * Nat.card C := by rw [← hD, ← hU]; ac_rfl
      _ = Nat.card V * Nat.card (U ⊓ C : Subgroup V) := hcard
  have hcover : U ⊔ C = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    simpa using hDcard.symm.le
  refine ⟨hcover, ?_⟩
  rw [commutatorAction_eq_closure]
  refine (Subgroup.closure_le (K := U)).mpr ?_
  rintro z ⟨a, v, rfl⟩
  have hv : v ∈ U ⊔ C := by rw [hcover]; exact Subgroup.mem_top v
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hv
  have hac : a • c = c := (FixedPoints.mem_subgroup (M := A) (α := V) (a := c)).mp hc a
  have hau : a • u ∈ U := (IsInvariant.invariant (A := A) (G := V) (H := U) a u).1 hu
  have heq : (u * c)⁻¹ * (a • (u * c)) = u⁻¹ * (a • u) := by
    rw [mul_inv_rev, smul_mul', hac]
    calc
      c⁻¹ * u⁻¹ * (a • u * c) = (c⁻¹ * c) * (u⁻¹ * (a • u)) := by ac_rfl
      _ = u⁻¹ * (a • u) := by simp
  rw [heq]
  exact U.mul_mem (U.inv_mem hu) hau

