module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.Weyl
/-!
# Exact nonopposite root relations in the concrete Spin pinning

The natural eight-dimensional action checks the eight sum-root and fifteen
commuting cases for one fixed root. Checked Weyl words carry every root to
that root and preserve addition. Faithfulness then gives all actual pinned
root relations, with nonzero exchange constant one in characteristic two.
The later coefficient extraction uses these literal parameters; neither
root-subgroup uniqueness nor an abstract Chevalley-system witness is assumed.

Source: GLS3 1.12.1(b,h) and Steinberg, Representations of algebraic groups, §2.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration
set_option linter.unusedSimpArgs false
public noncomputable section
namespace Triality.SimplyConnected.Pinning.RootPairs
universe u
variable (k : Type u) [Field k] [CharP k 2]
private theorem exchange_4 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 4) b z) =
      rootAction k (rootAt 4) b (rootAction k (rootAt 12) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_5 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 5) b z) =
      rootAction k (rootAt 5) b (rootAction k (rootAt 13) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_8 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 8) b z) =
      rootAction k (rootAt 8) b (rootAction k (rootAt 16) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_9 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 9) b z) =
      rootAction k (rootAt 9) b (rootAction k (rootAt 17) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_14 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 14) b z) =
      rootAction k (rootAt 14) b (rootAction k (rootAt 6) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_15 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 15) b z) =
      rootAction k (rootAt 15) b (rootAction k (rootAt 7) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_18 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 18) b z) =
      rootAction k (rootAt 18) b (rootAction k (rootAt 10) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem exchange_19 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 19) b z) =
      rootAction k (rootAt 19) b (rootAction k (rootAt 11) (a*b)
        (rootAction k (rootAt 2) a z)) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf <;> simp only [show (2:k)=0 from CharP.cast_eq_zero k 2, mul_zero, add_zero, zero_add]
private theorem commute_0 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 0) b z) =
      rootAction k (rootAt 0) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_2 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 2) b z) =
      rootAction k (rootAt 2) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_3 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 3) b z) =
      rootAction k (rootAt 3) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_6 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 6) b z) =
      rootAction k (rootAt 6) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_7 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 7) b z) =
      rootAction k (rootAt 7) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_10 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 10) b z) =
      rootAction k (rootAt 10) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_11 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 11) b z) =
      rootAction k (rootAt 11) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_12 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 12) b z) =
      rootAction k (rootAt 12) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_13 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 13) b z) =
      rootAction k (rootAt 13) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_16 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 16) b z) =
      rootAction k (rootAt 16) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_17 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 17) b z) =
      rootAction k (rootAt 17) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff] <;>
      ring_nf
private theorem commute_20 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 20) b z) =
      rootAction k (rootAt 20) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff]
private theorem commute_21 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 21) b z) =
      rootAction k (rootAt 21) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff]
private theorem commute_22 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 22) b z) =
      rootAction k (rootAt 22) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff]
private theorem commute_23 (a b : k) (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 2) a (rootAction k (rootAt 23) b z) =
      rootAction k (rootAt 23) b (rootAction k (rootAt 2) a z) := by
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAt, rootAction]
    norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul, Fin.ext_iff]

private def indexWord : List (Fin 4) → Fin 24 → Fin 24
  | [], r => r
  | i::w, r => reflectionIndex i (indexWord w r)
private def wordToTwo : Fin 24 → List (Fin 4) :=
  ![[0,1,3,2,1], [0], [], [1,3,2,1], [0,1,3,2], [0,1], [1], [1,3,2],
    [0,1,3], [0,1,2], [1,2], [1,3], [0,1,3,2,0], [0,1,0], [1,0], [1,3,2,0],
    [0,1,3,0], [0,1,2,0], [1,2,0], [1,3,0], [0,1,3,0,1], [0,1,2,0,1], [1,2,0,1], [1,3,0,1]]
private theorem wordToTwo_spec : ∀ r, indexWord (wordToTwo r) r = 2 := by decide
private def wordPerm : List (Fin 4) → Equiv.Perm RootIndex
  | [] => Equiv.refl _
  | i::w => (wordPerm w).trans ((typeDRootPairing 2).reflectionPerm (simpleRoot i))
private theorem wordPerm_rootAt (w : List (Fin 4)) (r : Fin 24) :
    wordPerm w (rootAt r) = rootAt (indexWord w r) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (typeDRootPairing 2).reflectionPerm (simpleRoot i) (wordPerm w (rootAt r)) = _
    rw [ih,reflection_rootAt]
    rfl
private theorem wordPerm_sum (w : List (Fin 4)) (a b c : RootIndex) :
    (typeDRootPairing 2).root (wordPerm w c) =
      (typeDRootPairing 2).root (wordPerm w a) + (typeDRootPairing 2).root (wordPerm w b) ↔
    (typeDRootPairing 2).root c = (typeDRootPairing 2).root a + (typeDRootPairing 2).root b := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordPerm, Equiv.trans_apply, (typeDRootPairing 2).root_reflectionPerm, ← map_add,
      ((typeDRootPairing 2).reflection _).injective.eq_iff]
    exact ih
private theorem wordPerm_neg (w : List (Fin 4)) (a : RootIndex) :
    wordPerm w (negativeRoot a) = negativeRoot (wordPerm w a) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (typeDRootPairing 2).reflectionPerm _ (wordPerm w (negativeRoot a)) = _
    rw [ih,reflection_negativeRoot]
    rfl

private theorem sum_pairing (a b c : RootIndex)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root a + (typeDRootPairing 2).root b) :
    (typeDRootPairing 2).pairing a b = -1 := by
  have symm (x y : RootIndex) : (typeDRootPairing 2).pairing x y =
      (typeDRootPairing 2).pairing y x := by
    rw [typeDRootPairing_pairing,typeDRootPairing_pairing,dot_comm]
  have h₁ := RootPairing.pairing_eq_add_of_root_eq_add (l := a) hs
  have h₂ := RootPairing.pairing_eq_add_of_root_eq_add (l := b) hs
  have h₃ := RootPairing.pairing_eq_add_of_root_eq_add (l := c) hs
  rw [(typeDRootPairing 2).pairing_same] at h₁ h₂ h₃
  rw [symm b a] at h₁
  rw [symm a c,symm b c] at h₃
  linarith
private theorem base_sum_certificate : ∀ (r : Fin 24),
    (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt r p) = -1 →
    ∀ p, rootVectorInt (reflectionIndex 0 r) p = rootVectorInt 2 p + rootVectorInt r p := by decide
private theorem base_sum (r : Fin 24)
    (h : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt r p) = -1) :
    (typeDRootPairing 2).root (rootAt (reflectionIndex 0 r)) =
      (typeDRootPairing 2).root (rootAt 2) + (typeDRootPairing 2).root (rootAt r) := by
  apply Subtype.ext
  funext p
  change typeDRootVector 4 (rootAt (reflectionIndex 0 r)) p =
    typeDRootVector 4 (rootAt 2) p + typeDRootVector 4 (rootAt r) p
  simp only [rootAt_vector]
  exact_mod_cast base_sum_certificate r h p
private theorem base_sum_index (r : Fin 24) (c : RootIndex)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root (rootAt 2) + (typeDRootPairing 2).root (rootAt r)) :
    (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt r p) = -1 ∧
      c = rootAt (reflectionIndex 0 r) := by
  have hp := sum_pairing (rootAt 2) (rootAt r) c hs
  rw [typeDRootPairing_pairing] at hp
  change (∑ p : Fin 4, typeDRootVector 4 (rootAt r) p * typeDRootVector 4 (rootAt 2) p) = -1 at hp
  simp only [rootAt_vector] at hp
  have hp' : (∑ p : Fin 4, rootVectorInt r p * rootVectorInt 2 p) = -1 := by exact_mod_cast hp
  have hh : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt r p) = -1 := by
    simpa only [mul_comm] using hp'
  exact ⟨hh,(typeDRootPairing 2).root.injective (hs.trans (base_sum r hh).symm)⟩

variable [IsAlgClosed k]
private def pointWord : List (Fin 4) → MulAut (Points k)
  | [] => 1
  | i::w => MulAut.conj ((simpleNormalizer k i)⁻¹) * pointWord w
private theorem pointWord_root (w : List (Fin 4)) (r : RootIndex) (a : k) :
    pointWord k w (rootPoint k r a) = rootPoint k (wordPerm w r) a := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (simpleNormalizer k i)⁻¹ * pointWord k w (rootPoint k r a) *
      ((simpleNormalizer k i)⁻¹)⁻¹ = _
    rw [ih,inv_inv,simpleNormalizer_rootPoint_conjugation]
    rfl
private theorem base_exchange (r : Fin 24) (c : RootIndex)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root (rootAt 2) + (typeDRootPairing 2).root (rootAt r))
    (a b : k) :
    rootPoint k (rootAt 2) a * rootPoint k (rootAt r) b =
      rootPoint k (rootAt r) b * rootPoint k c (a*b) * rootPoint k (rootAt 2) a := by
  obtain ⟨h,rfl⟩ := base_sum_index r c hs
  apply naturalAction_injective k
  simp only [map_mul,naturalAction_rootPoint]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul,LinearEquiv.mul_apply,rootAction_spec]
  fin_cases r
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 0 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 1 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 2 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 3 p) ≠ -1) h).elim
  · exact exchange_4 k a b z
  · exact exchange_5 k a b z
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 6 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 7 p) ≠ -1) h).elim
  · exact exchange_8 k a b z
  · exact exchange_9 k a b z
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 10 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 11 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 12 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 13 p) ≠ -1) h).elim
  · exact exchange_14 k a b z
  · exact exchange_15 k a b z
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 16 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 17 p) ≠ -1) h).elim
  · exact exchange_18 k a b z
  · exact exchange_19 k a b z
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 20 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 21 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 22 p) ≠ -1) h).elim
  · exact ((by decide : (∑ p : Fin 4, rootVectorInt 2 p * rootVectorInt 23 p) ≠ -1) h).elim
private theorem base_commute (r : Fin 24)
    (hop : rootAt r ≠ negativeRoot (rootAt 2))
    (hs : ¬ ∃ c : RootIndex, (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root (rootAt 2) + (typeDRootPairing 2).root (rootAt r))
    (a b : k) : Commute (rootPoint k (rootAt 2) a) (rootPoint k (rootAt r) b) := by
  show _ * _ = _ * _
  apply naturalAction_injective k
  simp only [map_mul,naturalAction_rootPoint]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul,LinearEquiv.mul_apply,rootAction_spec]
  fin_cases r
  · exact commute_0 k a b z
  · exact (hop (by simp [rootAt,negativeRoot])).elim
  · exact commute_2 k a b z
  · exact commute_3 k a b z
  · exact (hs ⟨_,base_sum 4 (by decide)⟩).elim
  · exact (hs ⟨_,base_sum 5 (by decide)⟩).elim
  · exact commute_6 k a b z
  · exact commute_7 k a b z
  · exact (hs ⟨_,base_sum 8 (by decide)⟩).elim
  · exact (hs ⟨_,base_sum 9 (by decide)⟩).elim
  · exact commute_10 k a b z
  · exact commute_11 k a b z
  · exact commute_12 k a b z
  · exact commute_13 k a b z
  · exact (hs ⟨_,base_sum 14 (by decide)⟩).elim
  · exact (hs ⟨_,base_sum 15 (by decide)⟩).elim
  · exact commute_16 k a b z
  · exact commute_17 k a b z
  · exact (hs ⟨_,base_sum 18 (by decide)⟩).elim
  · exact (hs ⟨_,base_sum 19 (by decide)⟩).elim
  · exact commute_20 k a b z
  · exact commute_21 k a b z
  · exact commute_22 k a b z
  · exact commute_23 k a b z

/-- The actual pinned sum-root relation, including its nonzero constant one. -/
theorem rootPoint_exchange (r s t : RootIndex)
    (hs : (typeDRootPairing 2).root t =
      (typeDRootPairing 2).root r + (typeDRootPairing 2).root s) (a b : k) :
    rootPoint k r a * rootPoint k s b =
      rootPoint k s b * rootPoint k t (a*b) * rootPoint k r a := by
  obtain ⟨i,rfl⟩ := rootAt_surjective r
  let w := wordToTwo i
  have h0 : wordPerm w (rootAt i) = rootAt 2 := by rw [wordPerm_rootAt,wordToTwo_spec]
  obtain ⟨j,hj⟩ := rootAt_surjective (wordPerm w s)
  apply (pointWord k w).injective
  simp only [map_mul,pointWord_root,h0,← hj]
  apply base_exchange k
  rw [hj,← h0]
  exact (wordPerm_sum w _ _ _).mpr hs

/-- Distinct nonopposite pinned roots with no sum commute. -/
theorem rootPoint_commute (r s : RootIndex) (hop : s ≠ negativeRoot r)
    (hs : ¬ ∃ t : RootIndex, (typeDRootPairing 2).root t =
      (typeDRootPairing 2).root r + (typeDRootPairing 2).root s) (a b : k) :
    Commute (rootPoint k r a) (rootPoint k s b) := by
  obtain ⟨i,rfl⟩ := rootAt_surjective r
  let w := wordToTwo i
  have h0 : wordPerm w (rootAt i) = rootAt 2 := by rw [wordPerm_rootAt,wordToTwo_spec]
  obtain ⟨j,hj⟩ := rootAt_surjective (wordPerm w s)
  show _ * _ = _ * _
  apply (pointWord k w).injective
  simp only [map_mul,pointWord_root,h0,← hj]
  apply (base_commute k j ?_ ?_ a b).eq
  · rw [hj,← h0,← wordPerm_neg]
    exact (wordPerm w).injective.ne hop
  · rintro ⟨t,ht⟩
    apply hs
    refine ⟨(wordPerm w).symm t,(wordPerm_sum w _ _ _).mp ?_⟩
    simpa only [Equiv.apply_symm_apply,h0,← hj] using ht
end Triality.SimplyConnected.Pinning.RootPairs
