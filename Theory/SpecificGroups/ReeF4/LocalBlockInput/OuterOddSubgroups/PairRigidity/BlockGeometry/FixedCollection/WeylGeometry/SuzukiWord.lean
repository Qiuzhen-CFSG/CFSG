module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.WordIdentity

/-!
# The relative Suzuki Weyl word in its signed fixed blocks

Let `z₊ = x_{α+β}(1)x_{α+2β}(1)` in the middle B₂ block, and negate
both roots to obtain `z₋`. Exceptional duality exchanges the commuting
factors, so these elements are fixed by the supplied Ree twist. The
Chevalley exchanges, transported by the two simple reflections, give
`z₊ z₋ z₊ z₋ z₊ = n₁ n₂ n₁ n₂`. This places the specified relative
Weyl representative in the join of the actual signed fixed blocks.

The eight signed B₂ roots and their reflection permutations below discharge
every hypothesis of the group word calculation in `WordIdentity`.
No simplicity, perfectness, Sylow, or positive parameter bound is used.

Source: GLS3, 2.3.8 and Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`.
-/

noncomputable section

namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SuzukiCalculation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics.Binary.FixedGeometry
open Parabolics.RadicalCoordinates Parabolics.RadicalCoordinates.FixedCoordinates
open B2WordCalculation
variable {m : ℕ}
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

def positiveRoot (i : Fin 4) : F4Chevalley.Root :=
  ((rootBlocks .positive).roots (.inr ((0 : Fin 4), i))).val

def root (i : Fin 8) : F4Chevalley.Root :=
  ![positiveRoot 0, positiveRoot 1, positiveRoot 2, positiveRoot 3,
    -positiveRoot 0, -positiveRoot 1, -positiveRoot 2, -positiveRoot 3] i

def vectors : Fin 8 → Vec 4 :=
  ![![0,0,1,-1], ![0,0,0,1], ![0,0,1,0], ![0,0,1,1],
    ![0,0,-1,1], ![0,0,0,-1], ![0,0,-1,0], ![0,0,-1,-1]]

lemma root_val (j : Fin 8) : (root j).val = vectors j := by
  have hn (r : F4Chevalley.Root) : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  fin_cases j
  · change (positiveRoot 0).val = ![0,0,1,-1]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (positiveRoot 1).val = ![0,0,0,1]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (positiveRoot 2).val = ![0,0,1,0]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (positiveRoot 3).val = ![0,0,1,1]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (-positiveRoot 0).val = ![0,0,-1,1]
    rw [hn]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (-positiveRoot 1).val = ![0,0,0,-1]
    rw [hn]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (-positiveRoot 2).val = ![0,0,-1,0]
    rw [hn]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  · change (-positiveRoot 3).val = ![0,0,-1,-1]
    rw [hn]
    funext k; fin_cases k <;>
      norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

lemma positiveRoot_pos (j : Fin 4) : typeF4RootPairing_base.IsPos (positiveRoot j) :=
  ((rootBlocks .positive).roots (.inr ((0 : Fin 4), j))).property

lemma positiveRoot_simple (j : Fin 2) : positiveRoot (j.castLE (by decide)) =
    typeF4SimpleRootIndex ⟨j.val + 1, by omega⟩ := by
  apply Subtype.ext
  fin_cases j <;> funext k <;> fin_cases k <;>
    norm_num [positiveRoot, rootBlocks_roots_val, RootPartition.index,
      RootPartition.quartetRow, RootPartition.table, typeF4SimpleRootIndex_val,
      typeF4SimpleRoot, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

lemma reflection_root (i : Fin 2) (j : Fin 8) :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex ⟨i.val + 1, by omega⟩) (root j) =
      root (reflectionIndex i j) := by
  apply Subtype.ext
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val, root_val]
  fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;>
    norm_num [reflectionIndex, vectors, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> rfl

def X (m : ℕ) (j : Fin 8) : SplitGroup m := rootGeneratorInGroup m (root j) 1

def node (i : Fin 2) : Fin 4 := ⟨i.val + 1, by omega⟩

def action : List (Fin 2) → Fin 8 → Fin 8
  | [], j => j
  | i :: w, j => reflectionIndex i (action w j)

lemma wordAction_root (w : List (Fin 2)) (j : Fin 8) :
    wordAction (w.map node) (root j) = root (action w j) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex (node i))
      (wordAction (w.map node) (root j)) = _
    rw [ih]
    exact reflection_root i (action w j)

lemma conj_X (w : List (Fin 2)) (j : Fin 8) :
    (MulAut.conj (simpleWord m (w.map node))) (X m j) = X m (action w j) := by
  change simpleWord m (w.map node) * rootGeneratorInGroup m (root j) 1 *
    (simpleWord m (w.map node))⁻¹ = _
  rw [simpleWord_conj_root, wordAction_root]
  rfl

lemma X_sq (j : Fin 8) : X m j * X m j = 1 := by
  apply Subtype.ext
  change F4Chevalley.rootCurve _ (1 : CoefficientField m) * F4Chevalley.rootCurve _ 1 = _
  rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero, F4Chevalley.rootCurve_zero]
  rfl

lemma mixed_comm : Commute (X m 3) (X m 2) := by
  apply mixedRootCommutation m _ _ (positiveRoot_pos 3) (positiveRoot_pos 2)
  · have hd := (rootBlocks .positive).quartet_dual_two (0 : Fin 4)
    change exceptionalRootPermutation (positiveRoot 2) = positiveRoot 3 at hd
    rw [← hd]
    exact (exceptionalRootPermutation_short_iff _).mp
      ((rootBlocks .positive).quartet_short_two (0 : Fin 4))
  · exact (rootBlocks .positive).quartet_short_two (0 : Fin 4)
  · change 0 ≤ dot (root 3).val (root 2).val
    norm_num [root_val, vectors, dot, Fin.sum_univ_four,
      Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

lemma short_comm : Commute (X m 2) (X m 1) := by
  apply Subtype.ext
  apply (rootCurve_commute_of_short_long_sum m (positiveRoot 2) (positiveRoot 1)
    (positiveRoot 3) (positiveRoot_pos 2) (positiveRoot_pos 1)
    ((rootBlocks .positive).quartet_short_two (0 : Fin 4)) _ _ 1 1).eq
  · have hd := (rootBlocks .positive).quartet_dual_two (0 : Fin 4)
    change exceptionalRootPermutation (positiveRoot 2) = positiveRoot 3 at hd
    rw [← hd]
    exact (exceptionalRootPermutation_short_iff _).mp
      ((rootBlocks .positive).quartet_short_two (0 : Fin 4))
  · change (root 3).val = (root 2).val + (root 1).val
    simp only [root_val]
    funext k; fin_cases k <;> norm_num [vectors, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

lemma long_comm : Commute (X m 3) (X m 0) := by
  apply rootGenerator_commute_of_no_sum m
    ((rootBlocks .positive).roots (.inr ((0 : Fin 4), (3 : Fin 4))))
    ((rootBlocks .positive).roots (.inr ((0 : Fin 4), (0 : Fin 4))))
  rintro ⟨r, hr⟩
  have hn : dot r.val r.val ≤ 2 := by
    by_cases hl : IsLongRoot r
    · rw [isLongRoot_norm r hl]
    · rw [isShortRoot_norm r hl]; norm_num
  change r.val = (root 3).val + (root 0).val at hr
  rw [hr, root_val, root_val] at hn
  norm_num [vectors, dot, Fin.sum_univ_four, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] at hn

lemma base_exchange : X m 0 * X m 1 * X m 2 * X m 3 = X m 1 * X m 0 := by
  have h := b2RootSwap m (positiveRoot 0) (positiveRoot 1) (positiveRoot 2) (positiveRoot 3)
    (positiveRoot_pos 0) (positiveRoot_pos 1)
    ((rootBlocks .positive).quartet_long (0 : Fin 4))
    (by
      have hd := (rootBlocks .positive).quartet_dual_zero (0 : Fin 4)
      change exceptionalRootPermutation (positiveRoot 0) = positiveRoot 1 at hd
      rw [← hd]
      exact (exceptionalRootPermutation_long_iff _).mp
        ((rootBlocks .positive).quartet_long (0 : Fin 4)))
    ((rootBlocks .positive).quartet_dot (0 : Fin 4))
    ((rootBlocks .positive).quartet_add (0 : Fin 4))
    ((rootBlocks .positive).quartet_add_two (0 : Fin 4)) 1 1
  change rootGeneratorInGroup m (positiveRoot 0) 1 *
    rootGeneratorInGroup m (positiveRoot 1) 1 * rootGeneratorInGroup m (positiveRoot 2) 1 *
    rootGeneratorInGroup m (positiveRoot 3) 1 =
    rootGeneratorInGroup m (positiveRoot 1) 1 * rootGeneratorInGroup m (positiveRoot 0) 1
  simpa only [one_mul, one_pow] using h.symm

lemma transport_comm (w : List (Fin 2)) (a b : Fin 8)
    (h : X m a * X m b = X m b * X m a) :
    X m (action w a) * X m (action w b) = X m (action w b) * X m (action w a) := by
  simpa only [map_mul, conj_X] using
    congrArg (MulAut.conj (simpleWord m (w.map node))) h

lemma all_comm (i : Fin 16) : let p := commutingPairs i
    X m p.1 * X m p.2 = X m p.2 * X m p.1 := by
  fin_cases i
  · exact transport_comm [1] 2 3 (mixed_comm (m := m)).symm.eq
  · exact transport_comm [] 2 1 (short_comm (m := m)).eq
  · exact transport_comm [] 3 0 (long_comm (m := m)).eq
  · exact transport_comm [0] 3 2 (mixed_comm (m := m)).eq
  · exact transport_comm [] 3 2 (mixed_comm (m := m)).eq
  · exact transport_comm [0, 1] 3 2 (mixed_comm (m := m)).eq
  · exact transport_comm [0] 0 3 (long_comm (m := m)).symm.eq
  · exact transport_comm [1, 0] 2 3 (mixed_comm (m := m)).symm.eq
  · exact transport_comm [1] 1 2 (short_comm (m := m)).symm.eq
  · exact transport_comm [0, 1] 1 2 (short_comm (m := m)).symm.eq
  · exact transport_comm [0, 1, 0] 2 3 (mixed_comm (m := m)).symm.eq
  · exact transport_comm [1, 0, 1] 1 2 (short_comm (m := m)).symm.eq
  · exact transport_comm [1, 0] 0 3 (long_comm (m := m)).symm.eq
  · exact transport_comm [0, 1, 0] 0 3 (long_comm (m := m)).symm.eq
  · exact transport_comm [1, 0, 1] 3 2 (mixed_comm (m := m)).eq
  · exact transport_comm [1, 0, 1, 0] 3 2 (mixed_comm (m := m)).eq

lemma transport_exchange (w : List (Fin 2)) :
    X m (action w 0) * X m (action w 1) * X m (action w 2) * X m (action w 3) =
      X m (action w 1) * X m (action w 0) := by
  simpa only [map_mul, conj_X] using
    congrArg (MulAut.conj (simpleWord m (w.map node))) (base_exchange (m := m))

lemma all_exchange (i : Fin 8) : let p := exchangeRoots i
    X m p.1 * X m p.2.1 * X m p.2.2.1 * X m p.2.2.2 = X m p.2.1 * X m p.1 := by
  fin_cases i
  · exact transport_exchange []
  · exact transport_exchange [1, 0, 1]
  · exact transport_exchange [1]
  · exact transport_exchange [0, 1]
  · exact transport_exchange [0]
  · exact transport_exchange [1, 0, 1, 0]
  · exact transport_exchange [0, 1, 0]
  · exact transport_exchange [1, 0]

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SuzukiCalculation


namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SuzukiCalculation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics.Binary.FixedGeometry B2WordCalculation
variable {m : ℕ}
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

def letter (m : ℕ) : Fin 10 → SplitGroup m :=
  ![X m 0, X m 1, X m 2, X m 3, X m 4, X m 5, X m 6, X m 7,
    simpleWord m [1], simpleWord m [2]]

lemma letter_root (j : Fin 8) : letter m (j.castLE (by decide)) = X m j := by
  fin_cases j <;> rfl

lemma letter_weyl (i : Fin 2) : letter m ⟨8 + i.val, by omega⟩ = simpleWord m [node i] := by
  fin_cases i <;> rfl

lemma letter_conj (i : Fin 2) (j : Fin 8) :
    letter m ⟨8 + i.val, by omega⟩ * letter m (j.castLE (by decide)) =
      letter m ((reflectionIndex i j).castLE (by decide)) * letter m ⟨8 + i.val, by omega⟩ := by
  rw [letter_root, letter_root, letter_weyl]
  have h := congrArg (fun z => z * simpleWord m [node i]) (conj_X (m := m) [i] j)
  change simpleWord m [node i] * X m j * (simpleWord m [node i])⁻¹ *
      simpleWord m [node i] = X m (reflectionIndex i j) * simpleWord m [node i] at h
  simpa only [inv_mul_cancel_right] using h

lemma letter_weyl_eq (i : Fin 2) :
    letter m (i.castLE (by decide)) * letter m ⟨i.val + 4, by omega⟩ *
      letter m (i.castLE (by decide)) = letter m ⟨8 + i.val, by omega⟩ := by
  fin_cases i
  · change X m 0 * X m 4 * X m 0 = simpleWord m [1]
    simp only [simpleWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Parabolics.weylWord, inv_one, CharTwo.neg_eq]
    rw [← show positiveRoot 0 = typeF4SimpleRootIndex 1 from positiveRoot_simple 0]
    rfl
  · change X m 1 * X m 5 * X m 1 = simpleWord m [2]
    simp only [simpleWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Parabolics.weylWord, inv_one, CharTwo.neg_eq]
    rw [← show positiveRoot 1 = typeF4SimpleRootIndex 2 from positiveRoot_simple 1]
    rfl

private lemma palindrome_sq {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) : (a * b * a) * (a * b * a) = 1 := by
  calc
    _ = a * (b * ((a * a) * b)) * a := by group
    _ = 1 := by rw [ha, one_mul, hb, mul_one, ha]

lemma letter_sq (j : Fin 10) : letter m j * letter m j = 1 := by
  have hn (i : Fin 2) : letter m ⟨8 + i.val, by omega⟩ * letter m ⟨8 + i.val, by omega⟩ = 1 := by
    rw [← letter_weyl_eq]
    apply palindrome_sq
    · fin_cases i
      · exact X_sq (m := m) 0
      · exact X_sq (m := m) 1
    · fin_cases i
      · exact X_sq (m := m) 4
      · exact X_sq (m := m) 5
  fin_cases j
  · exact X_sq (m := m) 0
  · exact X_sq (m := m) 1
  · exact X_sq (m := m) 2
  · exact X_sq (m := m) 3
  · exact X_sq (m := m) 4
  · exact X_sq (m := m) 5
  · exact X_sq (m := m) 6
  · exact X_sq (m := m) 7
  · exact hn 0
  · exact hn 1

lemma root_braid : letter m 7 * letter m 3 * letter m 7 =
    letter m 3 * letter m 7 * letter m 3 := by
  have h := letter_conj (m := m) 0 0
  change simpleWord m [1] * X m 0 = X m 4 * simpleWord m [1] at h
  have hw : X m 0 * X m 4 * X m 0 = simpleWord m [1] := letter_weyl_eq (m := m) 0
  rw [← hw] at h
  have hb := congrArg (fun z => z * X m 0) h
  simp only [mul_assoc, X_sq, mul_one] at hb
  have hc := congrArg (MulAut.conj (simpleWord m ([1].map node))) hb
  simp only [map_mul, conj_X] at hc
  change X m 3 * (X m 7 * X m 3) = X m 7 * (X m 3 * X m 7) at hc
  change X m 7 * X m 3 * X m 7 = X m 3 * X m 7 * X m 3
  simpa only [mul_assoc] using hc.symm

lemma letter_braid : letter m 9 * letter m 8 * letter m 9 * letter m 8 =
    letter m 8 * letter m 9 * letter m 8 * letter m 9 := by
  have h := sideWord_fixed m .suzuki
  rw [reeTwist_simpleWord] at h
  change simpleWord m [2, 1, 2, 1] = simpleWord m [1, 2, 1, 2] at h
  change simpleWord m [2] * simpleWord m [1] * simpleWord m [2] * simpleWord m [1] =
    simpleWord m [1] * simpleWord m [2] * simpleWord m [1] * simpleWord m [2]
  simpa only [simpleWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc] using h

lemma five_central_factors :
    (X m 2 * X m 3) * (X m 6 * X m 7) * (X m 2 * X m 3) *
      (X m 6 * X m 7) * (X m 2 * X m 3) = simpleWord m (sideWord .suzuki) := by
  have h := central_word (letter m) letter_sq letter_conj letter_weyl_eq root_braid letter_braid
    (fun i => by simpa only [letter_root] using all_comm (m := m) i)
    (fun i => by simpa only [letter_root] using all_exchange (m := m) i)
  change (X m 2 * X m 3) * (X m 6 * X m 7) * (X m 2 * X m 3) *
    (X m 6 * X m 7) * (X m 2 * X m 3) =
    simpleWord m [1] * simpleWord m [2] * simpleWord m [1] * simpleWord m [2] at h
  simpa only [simpleWord, sideWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc] using h

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SuzukiCalculation


@[expose] public section

namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics.Binary.FixedGeometry
open Parabolics.RadicalCoordinates Parabolics.RadicalCoordinates.FixedCoordinates
variable {m : ℕ}
local instance suzukiWordRootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def centralRoot (j : Fin 2) : F4Chevalley.Root :=
  ((rootBlocks .positive).roots (.inr ((0 : Fin 4), if j = 0 then 2 else 3))).val

private theorem centralRoot_mem (j : Fin 2) : IsSimpleBlockRoot .suzuki true (centralRoot j) :=
  (positiveBlockRoots_simple_iff .suzuki _).mp ⟨_, rfl⟩

def suzukiCentralWord (m : ℕ) (positive : Bool) : SplitGroup m :=
  rootGeneratorInGroup m
    (if positive then ((rootBlocks .positive).roots (.inr ((0 : Fin 4), (2 : Fin 4)))).val
      else -((rootBlocks .positive).roots (.inr ((0 : Fin 4), (2 : Fin 4)))).val) 1 *
    rootGeneratorInGroup m
      (if positive then ((rootBlocks .positive).roots (.inr ((0 : Fin 4), (3 : Fin 4)))).val
        else -((rootBlocks .positive).roots (.inr ((0 : Fin 4), (3 : Fin 4)))).val) 1

private lemma centralWord_eq (m : ℕ) (positive : Bool) :
    suzukiCentralWord m positive =
  rootGeneratorInGroup m (if positive then centralRoot 0 else -centralRoot 0) 1 *
    rootGeneratorInGroup m (if positive then centralRoot 1 else -centralRoot 1) 1 := rfl

lemma suzukiCentralWord_roots (m : ℕ) (positive : Bool) :
    suzukiCentralWord m positive =
      rootGeneratorInGroup m (if positive then ((rootBlocks .positive).roots (.inr ((0 : Fin 4), (2 : Fin 4)))).val
        else -((rootBlocks .positive).roots (.inr ((0 : Fin 4), (2 : Fin 4)))).val) 1 *
      rootGeneratorInGroup m (if positive then ((rootBlocks .positive).roots (.inr ((0 : Fin 4), (3 : Fin 4)))).val
        else -((rootBlocks .positive).roots (.inr ((0 : Fin 4), (3 : Fin 4)))).val) 1 := rfl

lemma suzukiCentralWord_mem (m : ℕ) (positive : Bool) :
    suzukiCentralWord m positive ∈ splitSimpleBlock m .suzuki positive := by
  have hr (j : Fin 2) : IsSimpleBlockRoot .suzuki positive
      (if positive then centralRoot j else -centralRoot j) := by
    cases positive
    · exact (isSimpleBlockRoot_neg_iff .suzuki true _).mpr (centralRoot_mem j)
    · exact centralRoot_mem j
  exact mul_mem (Subgroup.subset_closure ⟨_, 1, hr 0, rfl⟩)
    (Subgroup.subset_closure ⟨_, 1, hr 1, rfl⟩)

private lemma centralWord_positive_fixed (d : LocalBlockInput m) :
    d.twist (suzukiCentralWord m true) = suzukiCentralWord m true := by
  have hd : exceptionalRootPermutation (centralRoot 0) = centralRoot 1 :=
    (rootBlocks .positive).quartet_dual_two (0 : Fin 4)
  have hb : exceptionalRootPermutation (centralRoot 1) = centralRoot 0 := by
    rw [← hd, exceptionalRootPermutation_involutive]
  have hs : IsShortRoot (centralRoot 0) := (rootBlocks .positive).quartet_short_two (0 : Fin 4)
  have hl : IsLongRoot (centralRoot 1) := by
    rw [← hd]
    exact (exceptionalRootPermutation_short_iff _).mp hs
  have hc : Commute (rootGeneratorInGroup m (centralRoot 1) 1)
      (rootGeneratorInGroup m (centralRoot 0) 1) :=
    mixedRootCommutation m _ _ (centralRoot_mem 1).2 (centralRoot_mem 0).2 hl hs
      (by have h := (rootBlocks .positive).quartet_top_dot (0 : Fin 4)
          change dot (centralRoot 1).val (centralRoot 0).val = 1 at h
          rw [h]; norm_num) 1 1
  simp only [centralWord_eq, ↓reduceIte, map_mul, d.twist_root,
    ← Parabolics.rootFieldEnd_apply, map_one, hd, hb]
  exact hc.eq

lemma relativeWeyl_conj_suzukiCentralWord (d : LocalBlockInput m) :
    (relativeWeyl d .suzuki).val * suzukiCentralWord m true *
      (relativeWeyl d .suzuki).val⁻¹ = suzukiCentralWord m false := by
  simp only [relativeWeyl_val, centralWord_eq, ↓reduceIte, Bool.false_eq_true]
  rw [show ∀ a b c : SplitGroup m, a * (b * c) * a⁻¹ =
      (a * b * a⁻¹) * (a * c * a⁻¹) by intros; group]
  rw [simpleWord_conj_root, simpleWord_conj_root,
    wordAction_sideWord_neg .suzuki _ (centralRoot_mem 0),
    wordAction_sideWord_neg .suzuki _ (centralRoot_mem 1)]

lemma suzukiCentralWord_fixed (d : LocalBlockInput m) (positive : Bool) :
    d.twist (suzukiCentralWord m positive) = suzukiCentralWord m positive := by
  cases positive
  · rw [← relativeWeyl_conj_suzukiCentralWord d, map_mul, map_mul, map_inv,
      show d.twist (relativeWeyl d .suzuki).val = (relativeWeyl d .suzuki).val from
        (relativeWeyl d .suzuki).property, centralWord_positive_fixed]
  · exact centralWord_positive_fixed d

def suzukiCentralElement (d : LocalBlockInput m) (positive : Bool) : d.fixedGroup :=
  ⟨suzukiCentralWord m positive, suzukiCentralWord_fixed d positive⟩

@[simp] lemma suzukiCentralElement_val (d : LocalBlockInput m) (positive : Bool) :
    (suzukiCentralElement d positive).val = suzukiCentralWord m positive := rfl

lemma suzukiCentralElement_mem (d : LocalBlockInput m) (positive : Bool) :
    suzukiCentralElement d positive ∈ simpleBlock d .suzuki positive :=
  suzukiCentralWord_mem m positive

/-- The middle-node Weyl lift is a five-factor word in fixed central elements. -/
theorem relativeWeyl_suzuki_eq (d : LocalBlockInput m) :
    relativeWeyl d .suzuki =
      suzukiCentralElement d true * suzukiCentralElement d false *
        suzukiCentralElement d true * suzukiCentralElement d false *
          suzukiCentralElement d true := by
  apply Subtype.ext
  exact (SuzukiCalculation.five_central_factors (m := m)).symm

/-- The middle-node Weyl representative lies in its signed fixed blocks. -/
theorem relativeWeyl_suzuki_mem (d : LocalBlockInput m) :
    relativeWeyl d .suzuki ∈ simpleBlock d .suzuki true ⊔ simpleBlock d .suzuki false := by
  rw [relativeWeyl_suzuki_eq]
  have hp : suzukiCentralElement d true ∈ simpleBlock d .suzuki true ⊔ simpleBlock d .suzuki false :=
    mem_sup_left (suzukiCentralElement_mem d true)
  have hn : suzukiCentralElement d false ∈ simpleBlock d .suzuki true ⊔ simpleBlock d .suzuki false :=
    mem_sup_right (suzukiCentralElement_mem d false)
  exact mul_mem (mul_mem (mul_mem (mul_mem hp hn) hp) hn) hp

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection

end
