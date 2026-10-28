module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Second.Tables

/-!
# Checked orbit and transition maps at letter 13

Exhaustive Boolean checks certify the tree edges for the literal first generators,
separation of the root, and their bijective action on 3510 indices. Each check
covers 256 indices, and a balanced soundness theorem combines the blocks.
This establishes no stabilizer containment: the Schreier factors still need to
be shown to lie in the literal second subgroup.

Source application: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.SecondCertificate
set_option Elab.async false

private def orbitTest (n : Nat) : Bool :=
  let i := Fin.ofNat 3510 n
  decide ((i ≠ 0 → (parent i).val < i.val ∧
      signedApply (label i) (point (parent i)) = point i) ∧
    (point i = 13 → i = 0) ∧
    previous 0 (next 0 i) = i ∧ previous 1 (next 1 i) = i ∧
    point (next 0 i) = KernelUpperData.One0.forward (point i) ∧
    point (next 1 i) = KernelUpperData.One1.forward (point i))

private theorem block0 : checkPow orbitTest 0 8 = true := by decide +kernel

private theorem block1 : checkPow orbitTest 256 8 = true := by decide +kernel

private theorem block2 : checkPow orbitTest 512 8 = true := by decide +kernel

private theorem block3 : checkPow orbitTest 768 8 = true := by decide +kernel

private theorem block4 : checkPow orbitTest 1024 8 = true := by decide +kernel

private theorem block5 : checkPow orbitTest 1280 8 = true := by decide +kernel

private theorem block6 : checkPow orbitTest 1536 8 = true := by decide +kernel

private theorem block7 : checkPow orbitTest 1792 8 = true := by decide +kernel

private theorem block8 : checkPow orbitTest 2048 8 = true := by decide +kernel

private theorem block9 : checkPow orbitTest 2304 8 = true := by decide +kernel

private theorem block10 : checkPow orbitTest 2560 8 = true := by decide +kernel

private theorem block11 : checkPow orbitTest 2816 8 = true := by decide +kernel

private theorem block12 : checkPow orbitTest 3072 8 = true := by decide +kernel

private theorem block13 : checkPow orbitTest 3328 8 = true := by decide +kernel

private theorem block14 : checkPow orbitTest 3584 8 = true := by decide +kernel

private theorem block15 : checkPow orbitTest 3840 8 = true := by decide +kernel

private theorem checked : checkPow orbitTest 0 12 = true :=
  (checkPow_join orbitTest 11 0 (checkPow_join orbitTest 10 0 (checkPow_join orbitTest 9 0 (checkPow_join orbitTest 8 0 block0 block1) (checkPow_join orbitTest 8 512 block2 block3)) (checkPow_join orbitTest 9 1024 (checkPow_join orbitTest 8 1024 block4 block5) (checkPow_join orbitTest 8 1536 block6 block7))) (checkPow_join orbitTest 10 2048 (checkPow_join orbitTest 9 2048 (checkPow_join orbitTest 8 2048 block8 block9) (checkPow_join orbitTest 8 2560 block10 block11)) (checkPow_join orbitTest 9 3072 (checkPow_join orbitTest 8 3072 block12 block13) (checkPow_join orbitTest 8 3584 block14 block15))))

private theorem orbit_spec (i : Fin 3510) :
    (i ≠ 0 → (parent i).val < i.val ∧
      signedApply (label i) (point (parent i)) = point i) ∧
    (point i = 13 → i = 0) ∧
    previous 0 (next 0 i) = i ∧ previous 1 (next 1 i) = i ∧
    point (next 0 i) = KernelUpperData.One0.forward (point i) ∧
    point (next 1 i) = KernelUpperData.One1.forward (point i) := by
  have h := checkPow_sound orbitTest 12 0 checked i.val (Nat.zero_le _)
    (Nat.lt_trans i.isLt (by decide))
  have hi : Fin.ofNat 3510 i.val = i := by simp
  simpa only [orbitTest, hi, decide_eq_true_eq] using h

theorem point_zero : point 0 = 13 := by decide +kernel

theorem parent_lt (i : Fin 3510) (hi : i ≠ 0) : (parent i).val < i.val :=
  ((orbit_spec i).1 hi).1

theorem tree_edge (i : Fin 3510) (hi : i ≠ 0) :
    signedGenerator (label i) (point (parent i)) = point i := by
  rw [signedGenerator_apply]
  exact ((orbit_spec i).1 hi).2

theorem point_eq_base (i : Fin 3510) (hi : point i = 13) : i = 0 :=
  (orbit_spec i).2.1 hi

theorem previous_next (a : Fin 2) (i : Fin 3510) : previous a (next a i) = i := by
  fin_cases a
  · exact (orbit_spec i).2.2.1
  · exact (orbit_spec i).2.2.2.1

theorem next_point (a : Fin 2) (i : Fin 3510) :
    point (next a i) = KernelUpperData.firstGenerator a (point i) := by
  fin_cases a
  · exact (orbit_spec i).2.2.2.2.1
  · exact (orbit_spec i).2.2.2.2.2

/-- The two literal generators induce genuine bijections on the orbit indices. -/
def transition (a : Fin 2) : Equiv.Perm (Fin 3510) where
  toFun := next a
  invFun := previous a
  left_inv := previous_next a
  right_inv := (show Function.LeftInverse (previous a) (next a) from previous_next a).rightInverse_of_surjective
    (Finite.surjective_of_injective
      (show Function.LeftInverse (previous a) (next a) from previous_next a).injective)

@[simp] theorem transition_apply (a : Fin 2) (i : Fin 3510) :
    transition a i = next a i := rfl

end Sporadic.Fischer.Fi23.CentralizerSection.SecondCertificate
