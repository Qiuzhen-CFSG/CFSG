module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.Core
set_option backward.isDefEq.respectTransparency true
/-!
# Conjugacy transport of the actual kernel fixed masks

The kernel coordinate equivalence identifies the literal row action with
left conjugation. It therefore defines a permutation action on the bounded
masks. A general fixed-point bijection transports single-element fixed counts
across certified conjugacy, without requiring any subgroup to be normal.

Source: the ATLAS max1 words and pair labels in `Image.StarData`, with their
native action comparison in `SylowCore.Transport.Coordinates`.
-/
public noncomputable section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
open Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions
open SylowCore SylowCore.Transport SylowCore.FiniteBoundCertificate
open SylowCore.FiniteBoundCertificate.NormalWeights
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
private def move (p : StarGroup) (m : Fin 2048) : Fin 2048 :=
  ⟨starMask p m.val, starMask_lt _ _⟩
private theorem move_mul (p q : StarGroup) (m : Fin 2048) :
    move (p*q) m = move p (move q m) := by
  obtain ⟨g,rfl⟩ := starProjection_surjective matrixA_mul_self matrixB_pow_four p
  obtain ⟨h,rfl⟩ := starProjection_surjective matrixA_mul_self matrixB_pow_four q
  apply (maskEquiv matrixA_mul_self matrixB_pow_four).injective
  rw [← map_mul]
  calc
    _ = action matrixA_mul_self matrixB_pow_four (g*h)
        (maskEquiv matrixA_mul_self matrixB_pow_four m) := maskEquiv_starMask _ _ _ _
    _ = action matrixA_mul_self matrixB_pow_four g
        (action matrixA_mul_self matrixB_pow_four h (maskEquiv matrixA_mul_self matrixB_pow_four m)) := by
      rw [map_mul]; rfl
    _ = action matrixA_mul_self matrixB_pow_four g
        (maskEquiv matrixA_mul_self matrixB_pow_four (move (starProjection _ _ h) m)) := by
      rw [show maskEquiv _ _ (move (starProjection _ _ h) m) = _ from maskEquiv_starMask _ _ h m]
    _ = _ := (maskEquiv_starMask _ _ g (move (starProjection _ _ h) m)).symm
private theorem move_one (m : Fin 2048) : move 1 m = m := by
  apply (maskEquiv matrixA_mul_self matrixB_pow_four).injective
  have h := maskEquiv_starMask matrixA_mul_self matrixB_pow_four 1 m
  change maskEquiv _ _ ⟨starMask 1 m.val, starMask_lt _ _⟩ = _
  simpa only [map_one, Equiv.Perm.one_apply] using h
private def maskAction : StarGroup →* Equiv.Perm (Fin 2048) where
  toFun p := {
    toFun := move p
    invFun := move p⁻¹
    left_inv := fun m => by rw [← move_mul, inv_mul_cancel, move_one]
    right_inv := fun m => by rw [← move_mul, mul_inv_cancel, move_one] }
  map_one' := Equiv.ext move_one
  map_mul' p q := Equiv.ext (move_mul p q)

private theorem fixed_card_of_perm_eq {G X Y : Type*} [Group G]
    (f : G →* Equiv.Perm Y) (hf : Function.Injective f)
    (act : G →* Equiv.Perm X) (x q y : G)
    (h : ∀ p, f q (f x p) = f y (f q p)) :
    Nat.card {v : X // act x v = v} = Nat.card {v : X // act y v = v} := by
  have he : q*x=y*q := hf (by simp only [map_mul]; exact Equiv.ext h)
  have hc : y=q*x*q⁻¹ := by rw [he,mul_inv_cancel_right]
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (act q)
  intro v
  rw [hc]
  simp only [map_mul,map_inv,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  exact (act q).injective.eq_iff.symm

private theorem single_fixed_card (p : StarGroup) :
    Nat.card {m : Fin 2048 // starMask p m.val = m.val} =
      Nat.card {m : Fin 2048 // maskAction p m = m} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl (Fin 2048))
  intro m
  change (move p m).val = m.val ↔ move p m = m
  exact Fin.ext_iff.symm

attribute [local irreducible] maskAction
/-- Conjugacy preserves the exact single-element mask fixed space. No normality is used. -/
theorem single_fixed_conjugates (i q y : Index) (h : Conjugates i q y) :
    Nat.card {m : Fin 2048 // starMask (element i).val m.val = m.val} =
      Nat.card {m : Fin 2048 // starMask (element y).val m.val = m.val} := by
  rw [single_fixed_card, single_fixed_card]
  exact fixed_card_of_perm_eq StarGroup.subtype StarGroup.subtype_injective maskAction
    (element i).val (element q).val (element y).val h

/-- A whole-subgroup fixed mask satisfies the equation of each member. -/
theorem fixed_le_single (B : Subgroup sylowCandidate) (i : Index) (hi : element i ∈ B) :
    Nat.card (FixedMasks B) ≤
      Nat.card {m : Fin 2048 // starMask (element i).val m.val = m.val} := by
  exact Nat.card_le_card_of_injective (fun m : FixedMasks B =>
    (⟨m.val,m.property ⟨element i,hi⟩⟩ : {m : Fin 2048 // starMask (element i).val m.val = m.val}))
    (fun a b h => Subtype.ext (congrArg (fun z : {m : Fin 2048 // starMask (element i).val m.val = m.val} => z.val) h))
end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
