module

public import Theory.GroupTheory.CheckedFiniteTable
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB

/-!
# Rank-three Frattini model for small even candidate 51

The enumerated elements embed in the verified Ree Sylow group. A checked
multiplication table, generator words, and products of squares identify the
exact candidate, its binary Frattini quotient, and its order-centralizer counts.
The complement action is checked once per element and reused in multiplication.

Source: Shinoda (1975), (2.3), pp. 81–82, using the root convention of
`SmallEvenCandidates`. The finite witnesses were generated from the original
root presentation; every equation and count is checked by Lean's kernel.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB
open Theory.GroupTheory
namespace C51
set_option maxRecDepth 32768
def val (x : Fin 32) : SylowModel :=
  (#[⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩] : Array SylowModel)[x.val]!
def mul (x y : Fin 32) : Fin 32 :=
  ⟨((#[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    #[1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 18, 19, 20, 21, 22, 16, 15, 23, 10, 11, 12, 13, 14, 17, 29, 31, 27, 26, 30, 24, 28, 25],
    #[2, 10, 11, 12, 13, 14, 9, 24, 20, 25, 26, 18, 17, 3, 27, 21, 28, 29, 5, 22, 15, 23, 1, 30, 8, 19, 6, 31, 4, 16, 7, 0],
    #[3, 15, 12, 5, 11, 16, 30, 1, 26, 7, 21, 17, 14, 18, 28, 9, 0, 27, 29, 8, 6, 25, 20, 19, 10, 24, 23, 4, 2, 31, 22, 13],
    #[4, 8, 13, 11, 0, 17, 21, 19, 1, 23, 20, 3, 18, 2, 29, 26, 27, 5, 12, 7, 10, 6, 24, 9, 22, 30, 15, 16, 31, 14, 25, 28],
    #[5, 9, 14, 16, 17, 0, 22, 15, 23, 1, 25, 27, 28, 29, 2, 7, 3, 4, 31, 26, 30, 24, 6, 8, 21, 10, 19, 11, 12, 13, 20, 18],
    #[6, 18, 19, 20, 21, 22, 5, 29, 12, 31, 27, 10, 23, 7, 26, 13, 30, 24, 9, 14, 16, 17, 0, 28, 4, 11, 2, 25, 8, 15, 3, 1],
    #[7, 16, 20, 9, 19, 15, 28, 0, 27, 3, 13, 23, 22, 10, 30, 5, 1, 26, 24, 4, 2, 31, 12, 11, 18, 29, 17, 8, 6, 25, 14, 21],
    #[8, 4, 21, 19, 1, 23, 13, 11, 0, 17, 12, 7, 10, 6, 24, 27, 26, 9, 20, 3, 18, 2, 29, 5, 14, 28, 16, 15, 25, 22, 31, 30],
    #[9, 5, 22, 15, 23, 1, 14, 16, 17, 0, 31, 26, 30, 24, 6, 3, 7, 8, 25, 27, 28, 29, 2, 4, 13, 18, 11, 19, 20, 21, 12, 10],
    #[10, 2, 9, 24, 20, 25, 11, 12, 13, 14, 5, 22, 15, 23, 1, 28, 21, 30, 26, 18, 17, 3, 27, 29, 16, 0, 31, 6, 7, 8, 4, 19],
    #[11, 26, 18, 17, 3, 27, 25, 8, 15, 19, 6, 5, 29, 12, 31, 23, 4, 16, 14, 1, 21, 30, 10, 7, 20, 22, 9, 0, 13, 28, 24, 2],
    #[12, 21, 17, 14, 18, 28, 7, 10, 6, 24, 23, 29, 27, 5, 4, 25, 2, 31, 16, 20, 9, 19, 15, 22, 26, 8, 30, 13, 11, 0, 1, 3],
    #[13, 20, 3, 18, 2, 29, 23, 22, 10, 30, 15, 12, 5, 11, 16, 6, 31, 14, 17, 24, 26, 9, 8, 25, 1, 7, 21, 28, 0, 27, 19, 4],
    #[14, 25, 27, 28, 29, 2, 1, 21, 30, 10, 19, 31, 4, 16, 11, 24, 12, 13, 0, 6, 7, 8, 9, 20, 23, 26, 22, 18, 17, 3, 15, 5],
    #[15, 3, 30, 1, 26, 7, 12, 5, 11, 16, 29, 8, 6, 25, 20, 0, 9, 19, 21, 17, 14, 18, 28, 27, 31, 13, 4, 23, 22, 10, 2, 24],
    #[16, 7, 28, 0, 27, 3, 20, 9, 19, 15, 24, 4, 2, 31, 12, 1, 5, 11, 13, 23, 22, 10, 30, 26, 25, 21, 8, 17, 14, 18, 6, 29],
    #[17, 23, 29, 27, 5, 4, 24, 26, 9, 8, 30, 16, 31, 14, 13, 19, 11, 0, 28, 15, 25, 22, 21, 1, 6, 20, 7, 3, 18, 2, 10, 12],
    #[18, 6, 5, 29, 12, 31, 19, 20, 21, 22, 9, 14, 16, 17, 0, 30, 13, 28, 27, 10, 23, 7, 26, 24, 15, 1, 25, 2, 3, 4, 8, 11],
    #[19, 27, 10, 23, 7, 26, 31, 4, 16, 11, 2, 9, 24, 20, 25, 17, 8, 15, 22, 0, 13, 28, 18, 3, 12, 14, 5, 1, 21, 30, 29, 6],
    #[20, 13, 23, 22, 10, 30, 3, 18, 2, 29, 17, 24, 26, 9, 8, 31, 6, 25, 15, 12, 5, 11, 16, 14, 27, 4, 28, 21, 19, 1, 0, 7],
    #[21, 12, 7, 10, 6, 24, 17, 14, 18, 28, 16, 20, 9, 19, 15, 2, 25, 22, 23, 29, 27, 5, 4, 31, 0, 3, 13, 30, 1, 26, 11, 8],
    #[22, 31, 26, 30, 24, 6, 0, 13, 28, 18, 11, 25, 8, 15, 19, 29, 20, 21, 1, 2, 3, 4, 5, 12, 17, 27, 14, 10, 23, 7, 16, 9],
    #[23, 17, 24, 26, 9, 8, 29, 27, 5, 4, 28, 15, 25, 22, 21, 11, 19, 1, 30, 16, 31, 14, 13, 0, 2, 12, 3, 7, 10, 6, 18, 20],
    #[24, 28, 15, 25, 22, 21, 4, 2, 31, 12, 3, 30, 1, 26, 7, 14, 10, 6, 8, 13, 11, 0, 17, 18, 5, 16, 29, 20, 9, 19, 27, 23],
    #[25, 14, 1, 21, 30, 10, 27, 28, 29, 2, 0, 6, 7, 8, 9, 12, 24, 20, 19, 31, 4, 16, 11, 13, 3, 5, 18, 22, 15, 23, 17, 26],
    #[26, 11, 25, 8, 15, 19, 18, 17, 3, 27, 14, 1, 21, 30, 10, 4, 23, 7, 6, 5, 29, 12, 31, 16, 28, 2, 0, 9, 24, 20, 13, 22],
    #[27, 19, 31, 4, 16, 11, 10, 23, 7, 26, 22, 0, 13, 28, 18, 8, 17, 3, 2, 9, 24, 20, 25, 15, 30, 6, 1, 5, 29, 12, 21, 14],
    #[28, 24, 4, 2, 31, 12, 15, 25, 22, 21, 8, 13, 11, 0, 17, 10, 14, 18, 3, 30, 1, 26, 7, 6, 19, 23, 20, 29, 27, 5, 9, 16],
    #[29, 30, 16, 31, 14, 13, 8, 6, 25, 20, 7, 28, 0, 27, 3, 22, 18, 2, 4, 21, 19, 1, 23, 10, 9, 15, 24, 12, 5, 11, 26, 17],
    #[30, 29, 8, 6, 25, 20, 16, 31, 14, 13, 4, 21, 19, 1, 23, 18, 22, 10, 7, 28, 0, 27, 3, 2, 11, 17, 12, 24, 26, 9, 5, 15],
    #[31, 22, 0, 13, 28, 18, 26, 30, 24, 6, 1, 2, 3, 4, 5, 20, 29, 12, 11, 25, 8, 15, 19, 21, 7, 9, 10, 14, 16, 17, 23, 27]] : Array (Array Nat))[x.val]!)[y.val]! % 32, Nat.mod_lt _ (by decide)⟩
def inv (x : Fin 32) : Fin 32 := (#[0, 1, 31, 16, 4, 5, 22, 7, 8, 9, 25, 27, 29, 28, 18, 15, 3, 17, 14, 19, 30, 24, 6, 23, 21, 10, 26, 11, 13, 12, 20, 2] : Array (Fin 32))[x.val]!
def act (x : Fin 32) : ReeTwo.Core := (#[⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, ⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, ⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, ⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩]  : Array ReeTwo.Core).getD x.val 1
set_option maxHeartbeats 16000000 in
def data : Theory.GroupTheory.CheckedFiniteTable.Data SylowModel 32 where
  val := val
  mul := mul
  inv := inv
  unit := 0
  injective := by decide +kernel
  val_unit := by decide +kernel
  val_mul := Theory.GroupTheory.CheckedFiniteTable.mul_of_action val mul
    (Multiplicative.ofAdd 2) act (by decide +kernel) (by decide +kernel) (by decide +kernel)
  inv_mul := by decide +kernel
abbrev M := Theory.GroupTheory.CheckedFiniteTable.Carrier data
def gen : Fin 5 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
def letter : Fin 5 → M := (![1, 2, 3, 4, 5] : Fin 5 → Fin 32)
def words (x : M) : List (Fin 5) :=
  (#[[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 1], [1, 2], [1, 3], [1, 4], [2, 0], [2, 4], [3, 4], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 3, 4], [1, 0, 2], [1, 0, 4], [1, 1, 0], [1, 1, 4], [1, 2, 4], [1, 3, 4], [2, 0, 1], [0, 1, 0, 4]] : Array (List (Fin 5)))[x.val]!
theorem generated : smallEvenCandidate 51 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
set_option maxHeartbeats 4000000 in
noncomputable def equiv : M ≃* smallEvenCandidate 51 :=
  (Theory.GroupTheory.CheckedFiniteTable.equiv data gen letter (by decide +kernel) words (by decide +kernel)).trans
    (MulEquiv.subgroupCongr generated.symm)
def label (x : M) : Binary 3 :=
  let a := (#[0, 1, 4, 3, 3, 0, 5, 2, 2, 1, 5, 0, 7, 7, 4, 2, 3, 3, 4, 1, 6, 6, 5, 2, 6, 5, 1, 0, 7, 7, 6, 4] : Array Nat)[x.val]!
  Multiplicative.ofAdd ![(a % 2 : Nat), ((a / 2) % 2 : Nat), ((a / 4) % 2 : Nat)]
set_option maxHeartbeats 4000000 in
def projection : M →* Binary 3 where
  toFun := label
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
def lift (v : Binary 3) : M :=
  (#[0, 1, 7, 3, 2, 6, 20, 12] : Array (Fin 32))[(v.toAdd 0).val + 2 * (v.toAdd 1).val + 4 * (v.toAdd 2).val]!
theorem surjective : Function.Surjective projection := by
  intro v
  exact ⟨lift v, (by decide +kernel : ∀ v, projection (lift v) = v) v⟩
def squares (x : M) : List (Fin 32) :=
  (#[[], [], [], [], [], [3], [], [], [], [], [], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [12], [], [], [], []] : Array (List (Fin 32)))[x.val]!
set_option maxHeartbeats 4000000 in
theorem ker : projection.ker = frattini M :=
  Theory.GroupTheory.CheckedFiniteTable.kernel ((IsPGroup.of_card (n := 12) card).of_injective
    (Theory.GroupTheory.CheckedFiniteTable.embedding data) data.injective) projection
    (by decide +kernel) (fun x => x) squares (by decide +kernel)
def ord (x : M) : Nat := (#[1, 2, 8, 4, 2, 2, 4, 2, 2, 2, 4, 4, 8, 8, 8, 2, 4, 2, 8, 2, 4, 4, 4, 2, 4, 4, 2, 4, 8, 8, 4, 8] : Array Nat)[x.val]!
def cent (x : M) : Nat := (#[32, 8, 16, 16, 32, 32, 8, 8, 8, 8, 8, 16, 16, 16, 16, 8, 16, 32, 16, 8, 8, 8, 8, 8, 8, 8, 8, 16, 16, 16, 8, 16] : Array Nat)[x.val]!
set_option maxHeartbeats 4000000 in
theorem order_eq (x : M) : orderOf x = ord x :=
  Theory.GroupTheory.CheckedFiniteTable.order_eq x (ord x) ((by decide +kernel : ∀ x, 0 < ord x) x)
    ((by decide +kernel : ∀ x : M, x ^ ord x = 1 ∧ ∀ j : Fin (ord x),
      0 < j.val → x ^ j.val ≠ 1) x)
set_option maxHeartbeats 4000000 in
theorem cent_eq (x : M) : MulAut.commutingCard x = cent x := by
  rw [MulAut.commutingCard_eq_card_filter_of_equiv (Equiv.refl M)]
  exact (by decide +kernel : ∀ x : M, (Finset.univ.filter (fun y : M => y * x = x * y)).card = cent x) x
set_option maxHeartbeats 4000000 in
theorem counts (v : Binary 3) :
    (projection.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests 5 0)) v,
     projection.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests 5 1)) v,
     projection.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests 5 2)) v) =
      rankThreeProfile 5 v := by
  change (projection.predicateFiberCard (MulAut.orderCentralizerTest (2,8,0)) v,
    projection.predicateFiberCard (MulAut.orderCentralizerTest (2,8,0)) v,
    projection.predicateFiberCard (MulAut.orderCentralizerTest (2,8,0)) v) = _
  rw [Theory.GroupTheory.CheckedFiniteTable.count projection ord cent order_eq cent_eq]
  revert v
  decide +kernel
/-- The exact candidate realizes its specified rank-three intrinsic profile. -/
public theorem model : RankThreeModel 5 := by
  unfold RankThreeModel
  rw [show rankThreeIndex 5 = 51 from rfl]
  refine ⟨projection.comp equiv.symm.toMonoidHom, surjective.comp equiv.symm.surjective,
    projection.ker_comp_mulEquiv_eq_frattini equiv.symm ker, ?_⟩
  intro v
  simp only [MonoidHom.orderCentralizerFiberCard_comp_mulEquiv]
  exact counts v
end C51
end ReeTwo.SylowModel.SmallEvenAutB
