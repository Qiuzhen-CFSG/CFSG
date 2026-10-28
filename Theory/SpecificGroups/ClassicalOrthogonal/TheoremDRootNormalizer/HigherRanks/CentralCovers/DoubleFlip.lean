module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks

/-!
# Double flips in the actual even orthogonal carriers

Three elementary root elements interchange two hyperbolic pairs. Its
commutator with a flip on one pair flips both pairs. Thus each double flip
lies in the full isometry commutator subgroup and in the Siegel-generated
subgroup. On diagonal tori it inverts either affected axis and centralizes
every other axis. A third hyperbolic pair consequently permits partial
inversion of any ordered pair of independent torus axes.

These are the concrete orthogonal partial inverters used in the central-cover
argument for Aschbacher--Smith A.2.18, printed p.40.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open scoped commutatorElement
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.DoubleFlip
variable {F : Type*} [Field F] [CharP F 2] {r : ℕ}

def pairSwap {i j : Fin r} (hij : i ≠ j) : O r F :=
  root (F := F) hij 1 * root (F := F) hij.symm 1 * root (F := F) hij 1

set_option linter.unusedSimpArgs false in
@[simp] theorem pairSwap_left {i j : Fin r} (hij : i ≠ j)
    (x : VectorD r F) (k : Fin r) :
    (pairSwap (F := F) hij).val x (.inl k) =
      if k = i then x (.inl j) else if k = j then x (.inl i) else x (.inl k) := by
  change (root (F := F) hij (1 : F)).val ((root (F := F) hij.symm 1).val ((root (F := F) hij 1).val x)) (.inl k) = _
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [root_apply_left, hi, hj, hij, hij.symm, CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_assoc, add_left_comm, add_comm]

set_option linter.unusedSimpArgs false in
@[simp] theorem pairSwap_right {i j : Fin r} (hij : i ≠ j)
    (x : VectorD r F) (k : Fin r) :
    (pairSwap (F := F) hij).val x (.inr k) =
      if k = i then x (.inr j) else if k = j then x (.inr i) else x (.inr k) := by
  change (root (F := F) hij (1 : F)).val ((root (F := F) hij.symm 1).val ((root (F := F) hij 1).val x)) (.inr k) = _
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [root_apply_right, hi, hj, hij, hij.symm, CharTwo.sub_eq_add, CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_assoc, add_left_comm, add_comm]

theorem pairSwap_sq {i j : Fin r} (hij : i ≠ j) :
    pairSwap (F := F) hij * pairSwap (F := F) hij = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl k =>
    change (pairSwap (F := F) hij).val ((pairSwap (F := F) hij).val x) (.inl k) = x (.inl k)
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all
  | inr k =>
    change (pairSwap (F := F) hij).val ((pairSwap (F := F) hij).val x) (.inr k) = x (.inr k)
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

@[simp] theorem pairSwap_inv {i j : Fin r} (hij : i ≠ j) :
    (pairSwap (F := F) hij)⁻¹ = pairSwap (F := F) hij :=
  inv_eq_of_mul_eq_one_right (pairSwap_sq hij)

omit [CharP F 2] in
theorem pairSwap_mem_elementary {i j : Fin r} (hij : i ≠ j) :
    pairSwap (F := F) hij ∈ elementarySubgroup (formD r F) :=
  (elementarySubgroup _).mul_mem ((elementarySubgroup _).mul_mem
    (root_mem_elementary hij 1) (root_mem_elementary hij.symm 1)) (root_mem_elementary hij 1)

theorem pairSwap_conj_flip {i j : Fin r} (hij : i ≠ j) :
    pairSwap (F := F) hij * flipOne (F := F) j * (pairSwap (F := F) hij)⁻¹ = flipOne (F := F) i := by
  rw [pairSwap_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl k =>
    change (pairSwap (F := F) hij).val ((flipOne (F := F) j).val ((pairSwap (F := F) hij).val x)) (.inl k) = _
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all
  | inr k =>
    change (pairSwap (F := F) hij).val ((flipOne (F := F) j).val ((pairSwap (F := F) hij).val x)) (.inr k) = _
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

theorem doubleFlip_commutator {i j : Fin r} (hij : i ≠ j) :
    flipOne (F := F) i * flipOne (F := F) j = ⁅pairSwap (F := F) hij,flipOne (F := F) j⁆ := by
  rw [commutatorElement_def, pairSwap_conj_flip,flipOne_inv]

theorem doubleFlip_mem_commutator {i j : Fin r} (hij : i ≠ j) :
    flipOne (F := F) i * flipOne (F := F) j ∈ commutator (O r F) := by
  rw [doubleFlip_commutator hij]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem doubleFlip_mem_elementary {i j : Fin r} (hij : i ≠ j) :
    flipOne (F := F) i * flipOne (F := F) j ∈ elementarySubgroup (formD r F) := by
  rw [doubleFlip_commutator hij,commutatorElement_def]
  rw [mul_assoc, mul_assoc, ← mul_assoc (flipOne (F := F) j)]
  exact (elementarySubgroup _).mul_mem (pairSwap_mem_elementary hij)
    (elementary_conj_mem _ _ _ ((elementarySubgroup _).inv_mem (pairSwap_mem_elementary hij)))


omit [CharP F 2] in
theorem flip_conj_diagonal (i : Fin r) (d : Fin r → Fˣ) :
    flipOne i * diagonal d * (flipOne i)⁻¹ =
      diagonal (fun k => if k = i then (d k)⁻¹ else d k) := by
  rw [flipOne_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl k =>
    change (flipOne (F := F) i).val ((diagonal d).val ((flipOne (F := F) i).val x)) (.inl k) = _
    by_cases h : k = i <;> simp [h]
  | inr k =>
    change (flipOne (F := F) i).val ((diagonal d).val ((flipOne (F := F) i).val x)) (.inr k) = _
    by_cases h : k = i <;> simp [h]

omit [CharP F 2] in
theorem flip_conj_single_self (i : Fin r) (t : Fˣ) :
    flipOne i * diagonal (Pi.mulSingle i t) * (flipOne i)⁻¹ =
      (diagonal (Pi.mulSingle i t))⁻¹ := by
  rw [flip_conj_diagonal]
  change diagonal _ = (diagonalHom (Pi.mulSingle i t))⁻¹
  rw [← map_inv]
  apply congrArg diagonal
  funext k
  by_cases h : k = i <;> simp [h]

omit [CharP F 2] in
theorem flip_commutes_single {i j : Fin r} (hij : i ≠ j) (t : Fˣ) :
    Commute (flipOne (F := F) i) (diagonal (Pi.mulSingle j t)) := by
  apply (mul_inv_eq_iff_eq_mul).mp
  rw [flip_conj_diagonal]
  apply congrArg diagonal
  funext k
  by_cases h : k = i
  · subst k
    simp [hij]
  · simp [h]

omit [CharP F 2] in
theorem doubleFlip_inverts {i k : Fin r} (hik : i ≠ k) (t : Fˣ) :
    (flipOne i * flipOne k) * diagonal (Pi.mulSingle i t) * (flipOne i * flipOne k)⁻¹ =
      (diagonal (Pi.mulSingle i t))⁻¹ := by
  calc
    _ = flipOne i * (flipOne k * diagonal (Pi.mulSingle i t) * (flipOne k)⁻¹) *
        (flipOne i)⁻¹ := by group
    _ = flipOne i * diagonal (Pi.mulSingle i t) * (flipOne i)⁻¹ := by
      rw [(flip_commutes_single hik.symm t).eq, mul_inv_cancel_right]
    _ = _ := flip_conj_single_self i t

omit [CharP F 2] in
theorem doubleFlip_commutes {i j k : Fin r} (hij : i ≠ j) (hkj : k ≠ j) (t : Fˣ) :
    Commute (flipOne (F := F) i * flipOne k) (diagonal (Pi.mulSingle j t)) :=
  (flip_commutes_single hij t).mul_left (flip_commutes_single hkj t)

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.DoubleFlip
