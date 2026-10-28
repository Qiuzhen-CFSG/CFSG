module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction.FixedSpace
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Bounding constant-displacement characters

The space of constant displacements embeds in the binary dual of the acting
elementary abelian group. Its dimension is therefore at most the group rank.
Together with the exact quotient correction, this supplies the transitive
exclusion on the deleted module in Aschbacher–Smith B.3.2(4), pp. 83–84.
-/

public section

namespace BinaryPermutation.QuotientFixedSpace

open Representation.BinaryOffender
open scoped IsMulCommutative

variable {Ω : Type*} [Fintype Ω]

theorem displacementRank_le_rank {A : Subgroup (Equiv.Perm Ω)}
    (hA : IsElementaryTwo A) (x : Ω) : displacementRank A x ≤ rank A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let R := LinearMap.range (displacement A x)
  let toChar (v : R) : Additive A →+ ZMod 2 :=
    { toFun := fun a => v.val a.toMul
      map_zero' := by
        obtain ⟨w, hw⟩ := v.property
        rw [← hw]
        change w.val x - w.val x = 0
        exact sub_self _
      map_add' := by
        intro a b
        obtain ⟨w, hw⟩ := v.property
        rw [← hw]
        exact displacement_mul A x w a.toMul b.toMul }
  let f : R →ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive A) :=
    { toFun := fun v => (toChar v).toZModLinearMap 2
      map_add' := by intros; ext a; rfl
      map_smul' := by intros; ext a; rfl }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    funext a
    exact congrArg (fun c : Module.Dual (ZMod 2) (Additive A) => c (Additive.ofMul a)) h
  have hbound := LinearMap.finrank_le_finrank_of_injective hf
  rw [Subspace.dual_finrank_eq] at hbound
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  rw [Nat.card_congr (Additive.toMul : Additive A ≃ A)] at hcard
  have hcard' : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hcard
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive A) = 2 ^ rank A := by
    rw [← hA.card_eq_two_pow_rank]
    exact hcard'.symm
  have hr := (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) hpow
  simpa only [hr, displacementRank, R] using hbound

end BinaryPermutation.QuotientFixedSpace
