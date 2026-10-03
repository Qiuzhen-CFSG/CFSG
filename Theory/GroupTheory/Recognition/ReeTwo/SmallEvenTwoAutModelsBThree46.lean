module

public import Theory.GroupTheory.CheckedFiniteTable
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB

/-!
# Rank-three Frattini model for small even candidate 46

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
namespace C46
set_option maxRecDepth 32768
def val (x : Fin 32) : SylowModel :=
  (#[⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩,
    ⟨⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩] : Array SylowModel)[x.val]!
def mul (x y : Fin 32) : Fin 32 :=
  ⟨((#[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    #[1, 3, 6, 7, 8, 9, 11, 5, 14, 15, 17, 18, 19, 10, 20, 21, 22, 23, 13, 25, 16, 0, 27, 2, 28, 29, 24, 30, 31, 26, 4, 12],
    #[2, 10, 5, 11, 12, 13, 1, 23, 24, 6, 9, 15, 16, 0, 25, 17, 26, 3, 7, 8, 31, 18, 19, 21, 22, 27, 4, 28, 14, 20, 29, 30],
    #[3, 7, 11, 5, 14, 15, 18, 9, 20, 21, 23, 13, 25, 17, 16, 0, 27, 2, 10, 29, 22, 1, 30, 6, 31, 26, 28, 4, 12, 24, 8, 19],
    #[4, 8, 12, 14, 0, 16, 19, 20, 1, 22, 24, 25, 2, 26, 3, 27, 5, 28, 29, 6, 7, 30, 9, 31, 10, 11, 13, 15, 17, 18, 21, 23],
    #[5, 9, 13, 15, 16, 0, 10, 21, 22, 1, 6, 17, 26, 2, 27, 3, 4, 11, 23, 24, 30, 7, 8, 18, 19, 28, 12, 14, 25, 31, 20, 29],
    #[6, 17, 9, 18, 19, 10, 3, 2, 28, 11, 15, 21, 22, 1, 29, 23, 24, 7, 5, 14, 12, 13, 25, 0, 27, 30, 8, 31, 20, 16, 26, 4],
    #[7, 5, 18, 9, 20, 21, 13, 15, 16, 0, 2, 10, 29, 23, 22, 1, 30, 6, 17, 26, 27, 3, 4, 11, 12, 24, 31, 8, 19, 28, 14, 25],
    #[8, 14, 19, 20, 1, 22, 25, 16, 3, 27, 28, 29, 6, 24, 7, 30, 9, 31, 26, 11, 5, 4, 15, 12, 17, 18, 10, 21, 23, 13, 0, 2],
    #[9, 15, 10, 21, 22, 1, 17, 0, 27, 3, 11, 23, 24, 6, 30, 7, 8, 18, 2, 28, 4, 5, 14, 13, 25, 31, 19, 20, 29, 12, 16, 26],
    #[10, 11, 1, 23, 24, 6, 15, 13, 25, 17, 3, 7, 8, 9, 31, 18, 19, 21, 0, 27, 26, 2, 28, 5, 14, 20, 22, 29, 30, 4, 12, 16],
    #[11, 23, 15, 13, 25, 17, 7, 6, 31, 18, 21, 0, 27, 3, 26, 2, 28, 5, 9, 20, 19, 10, 29, 1, 30, 4, 14, 12, 16, 22, 24, 8],
    #[12, 24, 16, 25, 2, 26, 8, 31, 10, 19, 22, 27, 5, 4, 11, 28, 13, 14, 20, 1, 23, 29, 6, 30, 9, 15, 0, 17, 3, 7, 18, 21],
    #[13, 6, 0, 17, 26, 2, 9, 18, 19, 10, 1, 3, 4, 5, 28, 11, 12, 15, 21, 22, 29, 23, 24, 7, 8, 14, 16, 25, 27, 30, 31, 20],
    #[14, 20, 25, 16, 3, 27, 29, 22, 7, 30, 31, 26, 11, 28, 5, 4, 15, 12, 24, 18, 9, 8, 21, 19, 23, 13, 17, 0, 2, 10, 1, 6],
    #[15, 21, 17, 0, 27, 3, 23, 1, 30, 7, 18, 2, 28, 11, 4, 5, 14, 13, 6, 31, 8, 9, 20, 10, 29, 12, 25, 16, 26, 19, 22, 24],
    #[16, 22, 26, 27, 5, 4, 24, 30, 9, 8, 19, 28, 13, 12, 15, 14, 0, 25, 31, 10, 21, 20, 1, 29, 6, 17, 2, 3, 11, 23, 7, 18],
    #[17, 18, 3, 2, 28, 11, 21, 10, 29, 23, 7, 5, 14, 15, 12, 13, 25, 0, 1, 30, 24, 6, 31, 9, 20, 16, 27, 26, 4, 8, 19, 22],
    #[18, 2, 21, 10, 29, 23, 5, 11, 12, 13, 0, 1, 30, 7, 24, 6, 31, 9, 15, 16, 25, 17, 26, 3, 4, 8, 20, 19, 22, 27, 28, 14],
    #[19, 28, 22, 29, 6, 24, 14, 12, 17, 25, 27, 30, 9, 8, 18, 31, 10, 20, 16, 3, 2, 26, 11, 4, 15, 21, 1, 23, 7, 5, 13, 0],
    #[20, 16, 29, 22, 7, 30, 26, 27, 5, 4, 12, 24, 18, 31, 9, 8, 21, 19, 28, 13, 15, 14, 0, 25, 2, 10, 23, 1, 6, 17, 3, 11],
    #[21, 0, 23, 1, 30, 7, 2, 3, 4, 5, 13, 6, 31, 18, 8, 9, 20, 10, 11, 12, 14, 15, 16, 17, 26, 19, 29, 22, 24, 25, 27, 28],
    #[22, 27, 24, 30, 9, 8, 28, 4, 15, 14, 25, 31, 10, 19, 21, 20, 1, 29, 12, 17, 0, 16, 3, 26, 11, 23, 6, 7, 18, 2, 5, 13],
    #[23, 13, 7, 6, 31, 18, 0, 17, 26, 2, 5, 9, 20, 21, 19, 10, 29, 1, 3, 4, 28, 11, 12, 15, 16, 22, 30, 24, 8, 14, 25, 27],
    #[24, 25, 8, 31, 10, 19, 27, 26, 11, 28, 14, 20, 1, 22, 23, 29, 6, 30, 4, 15, 13, 12, 17, 16, 3, 7, 9, 18, 21, 0, 2, 5],
    #[25, 31, 27, 26, 11, 28, 20, 19, 23, 29, 30, 4, 15, 14, 13, 12, 17, 16, 22, 7, 6, 24, 18, 8, 21, 0, 3, 2, 5, 9, 10, 1],
    #[26, 19, 4, 28, 13, 12, 22, 29, 6, 24, 8, 14, 0, 16, 17, 25, 2, 27, 30, 9, 18, 31, 10, 20, 1, 3, 5, 11, 15, 21, 23, 7],
    #[27, 30, 28, 4, 15, 14, 31, 8, 21, 20, 29, 12, 17, 25, 0, 16, 3, 26, 19, 23, 1, 22, 7, 24, 18, 2, 11, 5, 13, 6, 9, 10],
    #[28, 29, 14, 12, 17, 25, 30, 24, 18, 31, 20, 16, 3, 27, 2, 26, 11, 4, 8, 21, 10, 19, 23, 22, 7, 5, 15, 13, 0, 1, 6, 9],
    #[29, 12, 30, 24, 18, 31, 16, 25, 2, 26, 4, 8, 21, 20, 10, 19, 23, 22, 27, 5, 11, 28, 13, 14, 0, 1, 7, 6, 9, 15, 17, 3],
    #[30, 4, 31, 8, 21, 20, 12, 14, 0, 16, 26, 19, 23, 29, 1, 22, 7, 24, 25, 2, 3, 27, 5, 28, 13, 6, 18, 9, 10, 11, 15, 17],
    #[31, 26, 20, 19, 23, 29, 4, 28, 13, 12, 16, 22, 7, 30, 6, 24, 18, 8, 14, 0, 17, 25, 2, 27, 5, 9, 21, 10, 1, 3, 11, 15]] : Array (Array Nat))[x.val]!)[y.val]! % 32, Nat.mod_lt _ (by decide)⟩
def inv (x : Fin 32) : Fin 32 := (#[0, 21, 13, 15, 4, 5, 23, 9, 30, 7, 18, 11, 26, 2, 27, 3, 16, 17, 10, 31, 22, 1, 20, 6, 29, 25, 12, 14, 28, 24, 8, 19] : Array (Fin 32))[x.val]!
def act (x : Fin 32) : ReeTwo.Core := (#[⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩]  : Array ReeTwo.Core).getD x.val 1
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
def gen : Fin 5 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9]
def letter : Fin 5 → M := (![1, 2, 3, 4, 5] : Fin 5 → Fin 32)
def words (x : M) : List (Fin 5) :=
  (#[[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4], [0, 1, 0], [0, 1, 2], [0, 1, 3], [0, 2, 3], [0, 2, 4], [0, 3, 4], [1, 0, 2], [1, 0, 3], [1, 2, 3], [1, 3, 4], [2, 3, 4], [0, 1, 0, 3], [0, 1, 2, 3], [0, 2, 3, 4], [1, 0, 2, 3]] : Array (List (Fin 5)))[x.val]!
theorem generated : smallEvenCandidate 46 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
set_option maxHeartbeats 4000000 in
noncomputable def equiv : M ≃* smallEvenCandidate 46 :=
  (Theory.GroupTheory.CheckedFiniteTable.equiv data gen letter (by decide +kernel) words (by decide +kernel)).trans
    (MulEquiv.subgroupCongr generated.symm)
def label (x : M) : Binary 3 :=
  let a := (#[0, 4, 1, 0, 3, 0, 5, 4, 7, 4, 5, 1, 2, 1, 3, 0, 3, 1, 5, 6, 7, 4, 7, 5, 6, 2, 2, 3, 2, 6, 7, 6] : Array Nat)[x.val]!
  Multiplicative.ofAdd ![(a % 2 : Nat), ((a / 2) % 2 : Nat), ((a / 4) % 2 : Nat)]
set_option maxHeartbeats 4000000 in
def projection : M →* Binary 3 where
  toFun := label
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
def lift (v : Binary 3) : M :=
  (#[0, 2, 12, 4, 1, 6, 19, 8] : Array (Fin 32))[(v.toAdd 0).val + 2 * (v.toAdd 1).val + 4 * (v.toAdd 2).val]!
theorem surjective : Function.Surjective projection := by
  intro v
  exact ⟨lift v, (by decide +kernel : ∀ v, projection (lift v) = v) v⟩
def squares (x : M) : List (Fin 32) :=
  (#[[], [], [], [1], [], [2], [], [], [], [], [], [], [], [], [], [7], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []] : Array (List (Fin 32)))[x.val]!
set_option maxHeartbeats 4000000 in
theorem ker : projection.ker = frattini M :=
  Theory.GroupTheory.CheckedFiniteTable.kernel ((IsPGroup.of_card (n := 12) card).of_injective
    (Theory.GroupTheory.CheckedFiniteTable.embedding data) data.injective) projection
    (by decide +kernel) (fun x => x) squares (by decide +kernel)
def ord (x : M) : Nat := (#[1, 8, 4, 4, 2, 2, 8, 8, 8, 8, 8, 2, 4, 4, 4, 4, 2, 2, 8, 8, 8, 8, 8, 8, 8, 2, 4, 4, 2, 8, 8, 8] : Array Nat)[x.val]!
def cent (x : M) : Nat := (#[32, 16, 16, 32, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 16, 16, 16, 16] : Array Nat)[x.val]!
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
    (projection.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests 4 0)) v,
     projection.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests 4 1)) v,
     projection.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests 4 2)) v) =
      rankThreeProfile 4 v := by
  change (projection.predicateFiberCard (MulAut.orderCentralizerTest (2,16,0)) v,
    projection.predicateFiberCard (MulAut.orderCentralizerTest (2,16,0)) v,
    projection.predicateFiberCard (MulAut.orderCentralizerTest (2,16,0)) v) = _
  rw [Theory.GroupTheory.CheckedFiniteTable.count projection ord cent order_eq cent_eq]
  revert v
  decide +kernel
/-- The exact candidate realizes its specified rank-three intrinsic profile. -/
public theorem model : RankThreeModel 4 := by
  unfold RankThreeModel
  rw [show rankThreeIndex 4 = 46 from rfl]
  refine ⟨projection.comp equiv.symm.toMonoidHom, surjective.comp equiv.symm.surjective,
    projection.ker_comp_mulEquiv_eq_frattini equiv.symm ker, ?_⟩
  intro v
  simp only [MonoidHom.orderCentralizerFiberCard_comp_mulEquiv]
  exact counts v
end C46
end ReeTwo.SylowModel.SmallEvenAutB
