module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutModelsBFiveCoordinates
/-!
# Realization of the four rank-five small even Frattini profiles

The coordinate module supplies surjections from the exact root-generated
subgroups at indices 23, 29, 35, and 40, with Frattini kernels. Here the
polynomial commutation equations reduce centralizer enumeration to 80 distinct
rows. Kernel-checked order, centralizer, and fiber counts identify all three
intrinsic tests with the prescribed profiles, completing the four models.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root convention
in `SmallEvenCandidates`. The finite tables use the binary bases of
`SmallEvenTwoAutProfilesB`; all witness data are checked against the group law.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB
namespace Five
open EvenCyclicAction
set_option maxRecDepth 32768
set_option Elab.async false

def commTest (i : Fin 4) (a b : Fin 8 → ZMod 2) : Prop :=
  (![(a 1 * b 0 + a 2 * b 0 + a 0 * b 1 + a 0 * b 2 = 0 ∧
      a 1 * b 0 + a 0 * b 1 + a 2 * b 1 + a 1 * b 2 = 0 ∧
      a 1 * b 0 + a 0 * a 1 * b 0 + a 2 * b 0 + a 0 * a 2 * b 0 + a 3 * b 0 + a 6 * b 0 + a 0 * b 1 + a 0 * a 1 * b 1 + a 2 * b 1 + a 1 * a 2 * b 1 + a 4 * b 1 + a 5 * b 1 + a 0 * b 0 * b 1 + a 1 * b 0 * b 1 + a 0 * b 2 + a 1 * b 2 + a 0 * b 0 * b 2 + a 1 * b 1 * b 2 + a 0 * b 3 + a 1 * b 4 + a 1 * b 5 + a 0 * b 6 = 0),
    (a 3 * b 0 + a 2 * b 1 + a 1 * b 2 + a 0 * b 3 = 0),
    (a 1 * b 0 + a 2 * b 0 + a 0 * b 1 + a 3 * b 1 + a 0 * b 2 + a 1 * b 3 = 0),
    (a 1 * b 0 + a 2 * b 0 + a 3 * b 0 + a 5 * b 0 + a 0 * b 1 + a 0 * a 1 * b 1 + a 2 * b 1 + a 4 * b 1 + a 1 * b 0 * b 1 + a 0 * b 2 + a 1 * b 2 + a 0 * b 3 + a 1 * b 4 + a 0 * b 5 = 0)]) i

instance (i : Fin 4) (a b : Fin 8 → ZMod 2) : Decidable (commTest i a b) := by
  unfold commTest
  rcases i with ⟨i, hi⟩
  interval_cases i <;> dsimp <;> infer_instance


private theorem core_eq_iff (x y : Core) :
    x = y ↔ x.b0 + y.b0 = 0 ∧
      x.b1 + y.b1 = 0 ∧
      x.b2 + y.b2 = 0 ∧
      x.b3 + y.b3 = 0 ∧
      x.b4 + y.b4 = 0 ∧
      x.b5 + y.b5 = 0 ∧
      x.b6 + y.b6 = 0 ∧
      x.b7 + y.b7 = 0 ∧
      x.b8 + y.b8 = 0 ∧
      x.b9 + y.b9 = 0 := by
  simp only [CharTwo.add_eq_zero, Core.ext_iff]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem commTest_iff (i : Fin 4) (a b : Fin 8 → ZMod 2) :
    fastMul (rawElement i a) (rawElement i b) =
      fastMul (rawElement i b) (rawElement i a) ↔ commTest i a b := by
  rw [SemidirectProduct.ext_iff]
  have hr : (fastMul (rawElement i a) (rawElement i b)).right =
      (fastMul (rawElement i b) (rawElement i a)).right := mul_comm _ _
  rw [and_iff_left hr, core_eq_iff]
  fin_cases i
  all_goals dsimp [rawElement, commTest, fastMul]
  all_goals rcases binary_cases (a 1) with ha | ha
  all_goals rcases binary_cases (b 1) with hb | hb
  all_goals simp only [ha, hb, action_flag_zero, action_flag_one, ↓reduceIte,
    coreMul_eq, Core.mul, actionTwo]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals try simp only [binary_sq]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals tauto

def finiteComm (i : Fin 4) (a b : Fin (size i)) : Prop :=
  commTest i (fun j => bit a.val j.val) (fun j => bit b.val j.val)
instance (i : Fin 4) (a b : Fin (size i)) : Decidable (finiteComm i a b) :=
  inferInstanceAs (Decidable (commTest i _ _))
theorem finiteComm_iff (i : Fin 4) (a b : Fin (size i)) :
    finiteComm i a b ↔ element i a * element i b = element i b * element i a := by
  unfold finiteComm
  rw [← commTest_iff]
  change fastMul (element i a) (element i b) = fastMul (element i b) (element i a) ↔ _
  rw [fastMul_element, fastMul_element]
def rowSize (i : Fin 4) : ℕ := if i = 0 then 32 else 16
instance (i : Fin 4) : NeZero (rowSize i) := ⟨by unfold rowSize; split <;> omega⟩
def reduceParameters (i : Fin 4) (a : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  (![![a 0, a 1, a 2, a 3 + a 6, a 4 + a 5, 0, 0, 0],
    ![a 0, a 1, a 2, a 3, 0, 0, 0, 0],
    ![a 0, a 1, a 2, a 3, 0, 0, 0, 0],
    ![a 0, a 1, a 2 + a 4, a 3 + a 4 + a 5, 0, 0, 0, 0]]) i

theorem commTest_reduce (i : Fin 4) (a b : Fin 8 → ZMod 2) :
    commTest i a b ↔ commTest i a (reduceParameters i b) := by
  fin_cases i <;> dsimp [commTest, reduceParameters] <;> ring_nf
  reduce_mod_char
  rfl

def row (i : Fin 4) (k : Fin (size i)) : Fin (rowSize i) :=
  let a := reduceParameters i (fun j => bit k.val j.val)
  ⟨((a 0).val + 2 * (a 1).val + 4 * (a 2).val + 8 * (a 3).val +
    16 * (a 4).val) % rowSize i, Nat.mod_lt _ (NeZero.pos _)⟩

def rowRepresentative (i : Fin 4) (c : Fin (rowSize i)) : Fin (size i) :=
  ⟨c.val % size i, Nat.mod_lt _ (NeZero.pos _)⟩

set_option maxHeartbeats 4000000 in
theorem row_bits : ∀ i k,
    reduceParameters i (fun j => bit k.val j.val) =
      (fun j => bit (rowRepresentative i (row i k)).val j.val) := by decide +kernel

theorem finiteComm_row (i : Fin 4) (j k : Fin (size i)) :
    finiteComm i j k ↔ finiteComm i j (rowRepresentative i (row i k)) := by
  unfold finiteComm
  rw [commTest_reduce, row_bits]

def elementOrder (i : Fin 4) (k : Fin (size i)) : ℕ :=
  (![#[1, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4],
    #[1, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 4],
    #[1, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 4, 2, 4, 4, 4, 2, 4, 4, 2],
    #[1, 2, 4, 4, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 4, 4, 2, 2, 4, 4, 2, 4, 4, 4]]) i |>.getD k.val 0

set_option maxHeartbeats 16000000 in
theorem order_certificate : ∀ i k, 0 < elementOrder i k ∧
    fastPow (element i k) (elementOrder i k) = 1 ∧
    ∀ m : Fin (elementOrder i k), 0 < m.val → fastPow (element i k) m.val ≠ 1 := by
  decide +kernel

theorem elementOrder_eq (i : Fin 4) (k : Fin (size i)) :
    orderOf (enumeration i k) = elementOrder i k := by
  have ho : orderOf (element i k) = elementOrder i k := by
    obtain ⟨hp, he, hn⟩ := order_certificate i k
    apply (orderOf_eq_iff hp).mpr
    refine ⟨?_, fun m hm hp => ?_⟩
    · simpa only [fastPow_eq _ (element_even i k)] using he
    · simpa only [fastPow_eq _ (element_even i k)] using hn ⟨m, hm⟩ hp
  exact (orderOf_injective (smallEvenCandidate (rankFiveIndex i)).subtype
    Subtype.val_injective (enumeration i k)).symm.trans ho

def centralizerOrder (i : Fin 4) (k : Fin (size i)) : ℕ :=
  (![#[256, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 128, 32, 32, 64, 64, 64, 64, 32, 256, 32, 32, 64, 64, 64, 64, 32],
    #[128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64],
    #[128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64],
    #[128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64]]) i |>.getD k.val 0

set_option maxHeartbeats 16000000 in
theorem centralizer_row_certificate : ∀ i (c : Fin (rowSize i)),
    (Finset.univ.filter (fun j : Fin (size i) =>
      finiteComm i j (rowRepresentative i c))).card =
      centralizerOrder i (rowRepresentative i c) := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem centralizerOrder_row : ∀ i k,
    centralizerOrder i (rowRepresentative i (row i k)) = centralizerOrder i k := by
  decide +kernel

theorem centralizer_certificate (i : Fin 4) (k : Fin (size i)) :
    (Finset.univ.filter (fun j : Fin (size i) => finiteComm i j k)).card =
      centralizerOrder i k := by
  simp_rw [finiteComm_row i _ k]
  rw [centralizer_row_certificate, centralizerOrder_row]

theorem centralizerOrder_eq (i : Fin 4) (k : Fin (size i)) :
    MulAut.commutingCard (enumeration i k) = centralizerOrder i k := by
  rw [MulAut.commutingCard_eq_card_filter_of_equiv (enumeration i)]
  have hc := centralizer_certificate i k
  simp only [finiteComm_iff] at hc
  convert hc using 2
  simp only [Subtype.ext_iff]
  rfl

def finiteTest (i : Fin 4) (j : Fin 3) (k : Fin (size i)) : Prop :=
  elementOrder i k = (rankFiveTests i j).1 ∧
    centralizerOrder i k = (rankFiveTests i j).2.1

instance (i : Fin 4) (j : Fin 3) : DecidablePred (finiteTest i j) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem finiteTest_iff (i : Fin 4) (j : Fin 3) (k : Fin (size i)) :
    MulAut.orderCentralizerTest (rankFiveTests i j) (enumeration i k) ↔ finiteTest i j k := by
  have hz : ∀ i j, (rankFiveTests i j).2.2 = 0 := by decide +kernel
  simp only [MulAut.orderCentralizerTest, elementOrder_eq, centralizerOrder_eq,
    hz, true_or, and_true, finiteTest]

def finiteCount (i : Fin 4) (j : Fin 3) (v : Binary 5) : ℕ :=
  (Finset.univ.filter (fun k : Fin (size i) =>
    label i (element i k) = v ∧ finiteTest i j k)).card

set_option maxHeartbeats 16000000 in
theorem count_certificate : ∀ i v,
    (finiteCount i 0 v, finiteCount i 1 v, finiteCount i 2 v) = rankFiveProfile i v := by
  decide +kernel

theorem count_eq (i : Fin 4) (j : Fin 3) (v : Binary 5) :
    (projection i).predicateFiberCard (MulAut.orderCentralizerTest (rankFiveTests i j)) v =
      finiteCount i j v := by
  unfold MonoidHom.predicateFiberCard finiteCount
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact (enumeration i).symm.subtypeEquiv (fun x => by
    obtain ⟨k, rfl⟩ := (enumeration i).surjective x
    simp only [Equiv.symm_apply_apply, ← finiteTest_iff]
    rfl)

end Five

/-- Each prescribed rank-five profile is realized on its exact candidate subgroup. -/
public theorem rankFiveModels (i : Fin 4) : RankFiveModel i := by
  refine ⟨Five.projection i, Five.projection_surjective i, Five.projection_ker i, ?_⟩
  intro v
  simp only [Five.count_eq]
  exact Five.count_certificate i v

end ReeTwo.SylowModel.SmallEvenAutB
