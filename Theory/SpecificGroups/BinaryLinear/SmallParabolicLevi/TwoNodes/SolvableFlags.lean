module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Solvable binary five-space flags with three-part nine

The diagonal action of an actual basis flag is onto the product of its block
linear groups. Solvability excludes blocks of dimension at least three, since
those binary linear groups are nontrivial and perfect. The diagonal kernel is
a two-group, so the three-part of the flag stabilizer counts precisely the
blocks of dimension two. Three-part nine therefore forces the block sizes
2+2+1, 2+1+2 or 1+2+2, which delete two nonadjacent nodes.

The conclusion is proved for every basis and every cut set, with no assumed
block decomposition or quotient identification in its hypotheses. Cuts index
the dimensions i+1; the complementary indices are the deleted nodes.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
the rank-two parabolic step in 13.8.25, printed pp.959–960 (PDF pp.976–977).
-/

public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry

private theorem linearGroup_card_formula (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private noncomputable def blockCoordinates (c : Fin 5 → Fin 5) (k : Fin 5) :
    BlockSpace c k ≃ₗ[ZMod 2] Space (Nat.card (Block c k)) := by
  classical
  exact LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    ((Fintype.equivFin (Block c k)).trans (finCongr Nat.card_eq_fintype_card.symm)).symm

private theorem block_card_le (c : Fin 5 → Fin 5) (k : Fin 5) :
    Nat.card (Block c k) ≤ 5 := by
  simpa using Nat.card_le_card_of_injective (Subtype.val : Block c k → Fin 5) Subtype.val_injective

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem linearGroup_not_solvable (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5) :
    ¬ Group.IsSolvable (LinearGroup n) := by
  have : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n hn
  have : Nontrivial (LinearGroup n) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [linearGroup_card_formula]
    interval_cases n <;> decide
  exact Group.IsPerfect.not_isSolvable _

/-- Every block of a solvable binary five-space flag has dimension at most two. -/
theorem flag_block_card_le_two_of_solvable (b : FiveBasis) (cuts : Set (Fin 4))
    (hs : Group.IsSolvable (flagStabilizer b cuts)) (k : Fin 5) :
    Nat.card (Block (cutLabel cuts) k) ≤ 2 := by
  classical
  let := hs
  let f := Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) k
  have hf : Function.Surjective f := by
    intro a
    exact ⟨Function.update 1 k a, Function.update_self ..⟩
  have : Group.IsSolvable (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) :=
    Group.isSolvable_of_surjective (flagDiagonalAction_surjective b cuts)
  have : Group.IsSolvable (BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) :=
    Group.isSolvable_of_surjective hf
  let e := linearGroupCongr (blockCoordinates (cutLabel cuts) k)
  have : Group.IsSolvable (LinearGroup (Nat.card (Block (cutLabel cuts) k))) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  by_contra h
  exact linearGroup_not_solvable (Nat.card (Block (cutLabel cuts) k)) (by omega)
    (block_card_le (cutLabel cuts) k) inferInstance

private theorem small_block_card (c : Fin 5 → Fin 5) (k : Fin 5)
    (hk : Nat.card (Block c k) ≤ 2) :
    Nat.card (BinaryLinear.GL (BlockSpace c k)) =
      if Nat.card (Block c k) = 2 then 6 else 1 := by
  rw [Nat.card_congr (linearGroupCongr (blockCoordinates c k)).toEquiv,
    linearGroup_card_formula]
  generalize Nat.card (Block c k) = n at hk ⊢
  interval_cases n <;> decide

private instance (c : Fin 5 → Fin 5) (k : Fin 5) : Finite (BinaryLinear.GL (BlockSpace c k)) :=
  Finite.of_injective (fun g : BinaryLinear.GL (BlockSpace c k) =>
    (g : BlockSpace c k → BlockSpace c k)) DFunLike.coe_injective

private theorem flag_three_part (b : FiveBasis) (cuts : Set (Fin 4)) :
    (Nat.card (flagStabilizer b cuts)).factorization 3 =
      (Nat.card (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel cuts) k))).factorization 3 := by
  let f := flagDiagonalAction b cuts
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = pCore 2 (flagStabilizer b cuts) from ker_flagDiagonalAction b cuts]
    exact pCore_isPGroup
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hc : Nat.card (flagStabilizer b cuts) =
      2 ^ n * Nat.card (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) := by
    rw [← f.ker.card_mul_index, index_ker, hn,
      f.range_eq_top_of_surjective (flagDiagonalAction_surjective b cuts), card_top]
  rw [hc, Nat.factorization_mul (pow_ne_zero n (by decide)) Nat.card_pos.ne']
  simp [Nat.factorization_pow, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]

/-- Each two-dimensional diagonal block contributes one factor of three; the
two-group kernel contributes none. -/
theorem flag_three_part_eq_two_blocks (b : FiveBasis) (cuts : Set (Fin 4))
    (hs : Group.IsSolvable (flagStabilizer b cuts)) :
    (Nat.card (flagStabilizer b cuts)).factorization 3 =
      ∑ k : Fin 5, if Nat.card (Block (cutLabel cuts) k) = 2 then 1 else 0 := by
  classical
  rw [flag_three_part, Nat.card_pi, Nat.factorization_prod_apply
    (fun _ _ => Nat.card_pos.ne')]
  apply Finset.sum_congr rfl
  intro k _
  rw [small_block_card _ _ (flag_block_card_le_two_of_solvable b cuts hs k)]
  split_ifs
  · rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2),
      Nat.Prime.factorization_self (by decide : Nat.Prime 3)]
  · simp

-- A computable count of the actual coordinate fibers, used only for the
-- finite combinatorics of the sixteen possible cut sets.
private def blockCount (s : Finset (Fin 4)) (k : Fin 5) : ℕ :=
  (Finset.univ.filter fun i : Fin 5 => (s.filter fun j => j.val < i.val).card = k.val).card

private theorem blockCount_eq (s : Finset (Fin 4)) (k : Fin 5) :
    blockCount s k = Nat.card (Block (cutLabel (s : Set (Fin 4))) k) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold blockCount cutLabel
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Fin.ext_iff]
  have he : s.filter (fun j => j.val < i.val) =
      Finset.univ.filter (fun j : Fin 4 => j ∈ (s : Set (Fin 4)) ∧ j.val < i.val) := by
    ext j
    simp
  rw [he]
  apply Iff.of_eq
  congr 3

-- With all blocks of size at most two and exactly two blocks of size two,
-- the five coordinates have sizes 2+2+1, 2+1+2 or 1+2+2.
private theorem finite_cut_classification :
    ∀ s : Finset (Fin 4),
      (∀ k : Fin 5, blockCount s k ≤ 2) →
      (∑ k : Fin 5, if blockCount s k = 2 then 1 else 0) = 2 →
      ∃ i j : Fin 4, i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
        s = ({i, j} : Finset (Fin 4))ᶜ := by
  decide

/-- A solvable flag stabilizer with three-part nine deletes precisely two
distinct, nonadjacent nodes of the four-node diagram. -/
theorem cuts_eq_compl_pair_of_solvable_three_part (b : FiveBasis) (cuts : Set (Fin 4))
    (hs : Group.IsSolvable (flagStabilizer b cuts))
    (h3 : (Nat.card (flagStabilizer b cuts)).factorization 3 = 2) :
    ∃ i j : Fin 4, i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      cuts = ({i, j} : Set (Fin 4))ᶜ := by
  classical
  have hb : ∀ k : Fin 5, blockCount cuts.toFinset k ≤ 2 := by
    intro k
    simpa only [blockCount_eq, Set.coe_toFinset] using flag_block_card_le_two_of_solvable b cuts hs k
  have hc : (∑ k : Fin 5, if blockCount cuts.toFinset k = 2 then 1 else 0) = 2 := by
    simpa only [blockCount_eq, Set.coe_toFinset, ← flag_three_part_eq_two_blocks b cuts hs] using h3
  obtain ⟨i, j, hij, hn, he⟩ := finite_cut_classification cuts.toFinset hb hc
  refine ⟨i, j, hij, hn, ?_⟩
  simpa only [Set.coe_toFinset, Finset.coe_compl, Finset.coe_insert, Finset.coe_singleton]
    using congrArg (fun s : Finset (Fin 4) => (s : Set (Fin 4))) he

end BinaryLinear.SmallParabolicLevi.TwoNodes
