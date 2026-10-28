module
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB
public import Theory.GroupTheory.PGroup.InvariantFiberCoordinates
public import Theory.Frattini.BinarySquares
public import Theory.SpecificGroups.ReeTwo.EvenCyclicAction

/-!
# Rank-five coordinates for four small even Ree two subgroups

Explicit binary parameters enumerate the original generator closures at
indices 23, 29, 35, and 40. Polynomial quotient coordinates use the precise
basis convention of `SmallEvenTwoAutProfilesB`. Generator words prove that
every parameter lies in the original subgroup; coordinate closure proves
the reverse containment. Every identity-fiber element is a square, so the
surjective binary maps have exactly the Frattini subgroups as kernels.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model.
The finite word and square witnesses were extracted from the saved realization
data; every equation is checked against the Lean group operation.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallEvenAutB
namespace Five
open EvenCyclicAction

set_option maxHeartbeats 16000000 in
theorem binary_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem binary_sq : ∀ x : ZMod 2, x ^ 2 = x := by decide +kernel
set_option maxRecDepth 32768

def size (i : Fin 4) : ℕ := if i = 0 then 256 else 128
instance (i : Fin 4) : NeZero (size i) := ⟨by unfold size; split <;> omega⟩
def bit (k : ℕ) (j : ℕ) : ZMod 2 := (k / 2 ^ j : ℕ)
def rawElement (i : Fin 4) (a : Fin 8 → ZMod 2) : SylowModel :=
  (![⟨⟨a 0, a 1, a 2, a 1, a 0, a 3, a 4, a 5, a 6, a 7⟩, Multiplicative.ofAdd (2 * (0 : ZMod 2).val)⟩,
    ⟨⟨0, 0, 0, a 0, a 1, a 2, a 3, a 4, a 5, a 6⟩, Multiplicative.ofAdd (2 * (0 : ZMod 2).val)⟩,
    ⟨⟨0, 0, a 0, a 1, a 2, a 0, a 3, a 4, a 5, a 6⟩, Multiplicative.ofAdd (2 * (a 1).val)⟩,
    ⟨⟨a 0, a 1, a 0, a 0, a 0 + a 1, a 2, a 3, a 4, a 5, a 6⟩, Multiplicative.ofAdd (2 * (0 : ZMod 2).val)⟩] : Fin 4 → SylowModel) i
def element (i : Fin 4) (k : Fin (size i)) : SylowModel :=
  rawElement i (fun j => bit k.val j.val)

def parameters (i : Fin 4) (x : SylowModel) : Fin 8 → ZMod 2 :=
  (![![x.left.b0, x.left.b1, x.left.b2, x.left.b5, x.left.b6, x.left.b7, x.left.b8, x.left.b9],
     ![x.left.b3, x.left.b4, x.left.b5, x.left.b6, x.left.b7, x.left.b8, x.left.b9, 0],
     ![x.left.b2, x.left.b3, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9, 0],
     ![x.left.b0, x.left.b1, x.left.b5, x.left.b6, x.left.b7, x.left.b8, x.left.b9, 0]]) i

def index (i : Fin 4) (x : SylowModel) : Fin (size i) :=
  ⟨(![1 * x.left.b0.val + 2 * x.left.b1.val + 4 * x.left.b2.val + 8 * x.left.b5.val + 16 * x.left.b6.val + 32 * x.left.b7.val + 64 * x.left.b8.val + 128 * x.left.b9.val,
    1 * x.left.b3.val + 2 * x.left.b4.val + 4 * x.left.b5.val + 8 * x.left.b6.val + 16 * x.left.b7.val + 32 * x.left.b8.val + 64 * x.left.b9.val,
    1 * x.left.b2.val + 2 * x.left.b3.val + 4 * x.left.b4.val + 8 * x.left.b6.val + 16 * x.left.b7.val + 32 * x.left.b8.val + 64 * x.left.b9.val,
    1 * x.left.b0.val + 2 * x.left.b1.val + 4 * x.left.b5.val + 8 * x.left.b6.val + 16 * x.left.b7.val + 32 * x.left.b8.val + 64 * x.left.b9.val]) i % size i, Nat.mod_lt _ (NeZero.pos _)⟩

def label (i : Fin 4) (x : SylowModel) : Binary 5 :=
  Multiplicative.ofAdd ((![![x.left.b0 + x.left.b1 + x.left.b0 * x.left.b1 + x.left.b1 * x.left.b2 + x.left.b6 + x.left.b7,
    x.left.b0 + x.left.b0 * x.left.b1 + x.left.b2 + x.left.b1 * x.left.b2 + x.left.b6 + x.left.b7,
    x.left.b1 + x.left.b2 + x.left.b0 * x.left.b2 + x.left.b1 * x.left.b2 + x.left.b5 + x.left.b6 + x.left.b7 + x.left.b8,
    x.left.b0 + x.left.b1,
    x.left.b2],
    ![x.left.b4 + x.left.b7,
    x.left.b5,
    x.left.b4,
    x.left.b5 + x.left.b6,
    x.left.b3],
    ![x.left.b2 + x.left.b4 + x.left.b7,
    x.left.b3,
    x.left.b2 + x.left.b6,
    x.left.b4 + x.left.b6,
    x.left.b2 + x.left.b3],
    ![x.left.b0 + x.left.b7 + x.left.b8,
    x.left.b0 + x.left.b0 * x.left.b1 + x.left.b6 + x.left.b7 + x.left.b8,
    x.left.b0 + x.left.b0 * x.left.b1 + x.left.b5 + x.left.b7,
    x.left.b0 + x.left.b1,
    x.left.b1]]) i)

def generators (i : Fin 4) : Fin 8 → SylowModel :=
  (![![root 0 * root 4 * root 7 * root 8,
    root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8,
    root 1 * root 3 * root 5 * root 6 * root 7 * root 9,
    root 5 * root 6 * root 7,
    root 6 * root 7 * root 8 * root 9,
    root 7 * root 9,
    root 8 * root 9,
    root 9],
    ![root 3,
    root 4 * root 7 * root 8,
    root 5 * root 6 * root 9,
    root 6 * root 7 * root 8 * root 9,
    root 7 * root 9,
    root 8 * root 9,
    root 9,
    1],
    ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9,
    rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9,
    root 4 * root 7 * root 8,
    root 6 * root 7 * root 8 * root 9,
    root 7 * root 9,
    root 8 * root 9,
    root 9,
    1],
    ![root 0 * root 2 * root 3 * root 4 * root 7,
    root 0 * root 1 * root 2 * root 3 * root 6 * root 8,
    root 8,
    root 5 * root 7 * root 8 * root 9,
    root 6,
    root 7 * root 9,
    root 9,
    1]]) i

set_option maxHeartbeats 16000000 in
theorem index_element : ∀ i k, index i (element i k) = k := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem one_element : ∀ i, element i (index i 1) = 1 := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem element_even : ∀ i k, (element i k).right = 1 ∨
    (element i k).right = Multiplicative.ofAdd (2 : ZMod 4) := by decide +kernel

theorem fastMul_element (i : Fin 4) (a : Fin (size i)) (y : SylowModel) :
    fastMul (element i a) y = element i a * y := fastMul_eq _ _ (element_even i a)


set_option maxHeartbeats 16000000 in
theorem element_index_raw : ∀ i (a : Fin 8 → ZMod 2),
    element i (index i (rawElement i a)) = rawElement i a := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem two_add_val : ∀ a b : ZMod 2,
    (2 * (a + b).val : ZMod 4) = 2 * a.val + 2 * b.val := by decide +kernel

theorem coreMul_eq (x y : Core) : x * y = Core.mul x y := rfl

set_option linter.unusedSimpArgs false in
theorem raw_repack_mul (i : Fin 4) (a b : Fin 8 → ZMod 2) :
    rawElement i (parameters i (fastMul (rawElement i a) (rawElement i b))) =
      fastMul (rawElement i a) (rawElement i b) := by
  fin_cases i <;> apply SemidirectProduct.ext
  all_goals first | apply Core.ext | apply Multiplicative.toAdd.injective
  all_goals dsimp [rawElement, parameters, fastMul]
  all_goals try split_ifs
  all_goals try simp only [coreMul_eq, Core.mul, actionTwo]
  all_goals try simp [two_add_val]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals simpa only [ZMod.natCast_val, mul_comm] using two_add_val (a 1) (b 1)

theorem mul_element (i : Fin 4) (a b : Fin (size i)) :
    element i (index i (element i a * element i b)) = element i a * element i b := by
  rw [← fastMul_element]
  change element i (index i (fastMul (rawElement i _) (rawElement i _))) = _
  have h := raw_repack_mul i (fun j => bit a.val j.val) (fun j => bit b.val j.val)
  have hn := element_index_raw i (parameters i
    (fastMul (rawElement i (fun j => bit a.val j.val)) (rawElement i (fun j => bit b.val j.val))))
  rw [h] at hn
  exact hn

set_option maxHeartbeats 16000000 in
theorem action_flag_zero :
    Multiplicative.ofAdd (2 * (0 : ZMod 2).val : ZMod 4) = 1 := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem action_flag_one :
    Multiplicative.ofAdd (2 * (1 : ZMod 2).val : ZMod 4) ≠ 1 := by decide +kernel

set_option linter.unusedSimpArgs false in
theorem label_mul : ∀ i a b,
    label i (element i a * element i b) = label i (element i a) * label i (element i b) := by
  simp_rw [← fastMul_element]
  intro i a b
  fin_cases i
  all_goals apply Multiplicative.toAdd.injective
  all_goals funext j
  all_goals fin_cases j
  all_goals dsimp [label, element, rawElement, fastMul]
  all_goals try simp only [coreMul_eq, Core.mul]
  all_goals rcases binary_cases (bit a.val 1) with ht | ht
  all_goals try simp only [ht, action_flag_zero, action_flag_one, ↓reduceIte]
  all_goals try dsimp [actionTwo]
  all_goals ring_nf
  all_goals reduce_mod_char
set_option maxHeartbeats 16000000 in
theorem inv_element (i : Fin 4) (a : Fin (size i)) :
    element i (index i (element i a)⁻¹) = (element i a)⁻¹ := by
  have hc : ∀ i a, element i (index i (fastPow (element i a) 3)) = fastPow (element i a) 3 ∧
      fastPow (element i a) 4 = 1 := by decide +kernel
  have hi : fastPow (element i a) 3 = (element i a)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [fastPow_eq _ (element_even i a), ← pow_succ', ← fastPow_eq _ (element_even i a)]
    exact (hc i a).2
  rw [← hi]
  exact (hc i a).1


def carrier (i : Fin 4) : Subgroup SylowModel where
  carrier := {x | element i (index i x) = x}
  one_mem' := one_element i
  mul_mem' := by
    intro x y hx hy
    change element i (index i x) = x at hx
    change element i (index i y) = y at hy
    rw [← hx, ← hy]
    exact mul_element i _ _
  inv_mem' := by
    intro x hx
    change element i (index i x) = x at hx
    rw [← hx]
    exact inv_element i _

theorem generators_mem (i : Fin 4) (j : Fin 8) :
    generators i j ∈ smallEvenCandidate (rankFiveIndex i) := by
  fin_cases i <;> fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Subgroup.one_mem _

set_option maxHeartbeats 16000000 in
theorem generators_carrier : ∀ i j, generators i j ∈ carrier i := by
  change ∀ i j, element i (index i (generators i j)) = generators i j
  decide +kernel

theorem candidate_le_carrier (i : Fin 4) :
    smallEvenCandidate (rankFiveIndex i) ≤ carrier i := by
  fin_cases i
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact generators_carrier 0 0
    · exact generators_carrier 0 1
    · exact generators_carrier 0 2
    · exact generators_carrier 0 3
    · exact generators_carrier 0 4
    · exact generators_carrier 0 5
    · exact generators_carrier 0 6
    · exact generators_carrier 0 7
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact generators_carrier 1 0
    · exact generators_carrier 1 1
    · exact generators_carrier 1 2
    · exact generators_carrier 1 3
    · exact generators_carrier 1 4
    · exact generators_carrier 1 5
    · exact generators_carrier 1 6
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact generators_carrier 2 0
    · exact generators_carrier 2 1
    · exact generators_carrier 2 2
    · exact generators_carrier 2 3
    · exact generators_carrier 2 4
    · exact generators_carrier 2 5
    · exact generators_carrier 2 6
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact generators_carrier 3 0
    · exact generators_carrier 3 1
    · exact generators_carrier 3 2
    · exact generators_carrier 3 3
    · exact generators_carrier 3 4
    · exact generators_carrier 3 5
    · exact generators_carrier 3 6

set_option maxHeartbeats 16000000 in
def words (i : Fin 4) (k : Fin (size i)) : List (Fin 8) :=
  (![#[[], [0, 5, 6], [2, 3, 7], [2, 6, 0], [1, 0, 5, 7], [0, 1, 0], [0, 6, 1, 2], [0, 0, 1, 2], [0, 3, 0], [0, 2, 5, 2], [0, 0, 2], [0, 0, 0, 2], [0, 5, 6, 1], [4, 1], [0, 2, 1, 7], [2, 4, 1], [0, 0, 5], [4, 0], [0, 0, 3, 5, 2], [2, 0, 4, 5], [0, 1, 1, 1], [1, 2, 5, 2], [0, 1, 2, 4, 5], [1, 2, 5], [3, 5, 7], [3, 0, 6], [2, 5], [0, 2, 5], [0, 1, 4], [1, 5, 6], [2, 1, 0, 5], [2, 1, 5, 6], [5, 7], [6, 0], [2, 3, 5], [0, 2, 3, 5], [1, 0], [1, 1, 1, 5], [0, 1, 2, 5, 6], [0, 0, 1, 5, 2], [0, 0, 3, 5], [0, 2, 2], [0, 0, 5, 2], [0, 0, 0, 5, 2], [0, 1, 6], [1, 4, 5], [0, 2, 1, 5], [1, 2, 3, 5], [4, 6], [0, 4, 5], [0, 0, 2, 3], [2, 4, 0], [0, 0, 1, 0, 5], [1, 2, 2], [0, 2, 3, 1], [1, 2, 7], [3], [0, 1, 1, 5], [2, 7], [0, 2, 7], [0, 4, 1, 5], [6, 1], [2, 1, 0, 7], [2, 6, 1], [6, 7], [0, 5, 7], [1, 1, 2], [2, 0], [1, 0, 5, 6], [1, 3], [0, 1, 2], [1, 2, 4], [2, 2], [0, 0, 0, 3, 5], [2, 4], [0, 2, 4], [0, 1, 5], [1, 4, 6], [0, 2, 1, 6], [1, 1, 1, 2], [4, 5], [0, 4, 6], [0, 2, 0, 5], [0, 0, 2, 0, 5], [0, 3, 1], [0, 0, 1, 3, 5], [1, 5, 2, 0], [1, 5, 2, 6], [1, 1, 5], [0, 3], [5, 2, 6], [0, 5, 2, 6], [0, 0, 0, 1], [1, 5, 7], [0, 1, 3, 5, 2], [5, 2, 1], [5, 6], [0], [1, 1, 5, 2], [5, 2, 0], [1, 6, 0], [3, 1, 5], [0, 1, 5, 2], [1, 4, 5, 2], [2, 5, 2], [0, 0, 3, 0], [4, 5, 2], [0, 4, 5, 2], [0, 1, 7], [0, 0, 1, 5], [0, 2, 5, 6, 1], [0, 0, 2, 1, 5], [4, 7], [0, 0, 0, 5], [2, 3, 4], [0, 2, 3, 4], [0, 1, 3, 5], [0, 0, 3, 1], [1, 2, 0], [1, 2, 6], [1, 1, 7], [3, 0, 5], [2, 6], [0, 2, 6], [0, 1, 4, 5, 6], [1], [0, 1, 2, 3], [2, 1], [7], [5, 6, 0], [2, 3], [0, 2, 3], [1, 0, 5], [1, 1, 1], [0, 1, 2, 6], [1, 1, 2, 1], [0, 0, 3], [0, 2, 2, 5], [1, 2, 1], [0, 1, 2, 1], [0, 1, 5, 6], [1, 4], [0, 2, 1], [1, 2, 3], [4, 5, 6], [0, 4], [0, 0, 2, 3, 5], [2, 4, 0, 5], [0, 0, 1, 0], [1, 2, 2, 5], [0, 1, 4, 5, 2], [1, 5, 2], [3, 5], [0, 1, 1], [5, 2], [0, 5, 2], [0, 4, 1], [5, 6, 1], [5, 2, 1, 0], [2, 5, 6, 1], [5], [0, 6], [3, 5, 2], [0, 3, 5, 2], [1, 0, 7], [0, 1, 0, 5], [0, 1, 5, 2, 6], [0, 0, 1, 2, 5], [0, 3, 0, 5], [0, 3, 4], [0, 0, 2, 5], [0, 0, 0, 2, 5], [0, 6, 1], [4, 1, 5], [0, 5, 2, 1], [1, 3, 5, 2], [0, 0], [4, 0, 5], [0, 2, 6, 0], [2, 0, 4], [0, 1, 1, 1, 5], [1, 3, 4], [0, 1, 2, 4], [1, 2], [3, 7], [3, 0, 5, 6], [2], [0, 2], [0, 1, 4, 5], [1, 6], [2, 1, 0], [2, 1, 6], [6], [0, 5], [1, 1, 2, 7], [2, 0, 7], [1, 5, 6, 0], [3, 1], [0, 1, 2, 7], [2, 3, 1], [3, 4], [0, 0, 3, 0, 5], [2, 4, 7], [4, 0, 2], [0, 1, 5, 7], [0, 0, 1], [0, 2, 6, 1], [0, 0, 2, 1], [4, 5, 7], [0, 0, 0], [0, 5, 2, 0], [0, 0, 5, 2, 0], [0, 1, 3], [0, 0, 3, 1, 5], [1, 2, 0, 5], [1, 2, 5, 6], [1, 1, 5, 7], [3, 0], [2, 5, 6], [0, 2, 5, 6], [0, 1, 4, 6], [1, 5], [0, 1, 2, 3, 5], [2, 1, 5], [5, 6, 7], [0, 7], [1, 1, 2, 5], [2, 0, 5], [1, 0, 6], [1, 3, 5], [0, 1, 2, 5], [1, 2, 4, 5], [2, 2, 5], [0, 0, 0, 3], [2, 4, 5], [0, 2, 4, 5], [0, 1], [1, 4, 5, 6], [0, 2, 1, 5, 6], [0, 0, 5, 2, 1], [4], [0, 4, 5, 6], [0, 2, 0], [0, 0, 2, 0], [0, 3, 1, 5], [0, 0, 1, 3], [1, 2, 0, 7], [6, 1, 2], [1, 1], [0, 3, 5], [2, 6, 7], [2, 3, 0], [0, 0, 0, 1, 5], [1, 7], [0, 2, 4, 1], [2, 1, 7]],
    #[[], [0], [1, 4, 5], [0, 1, 4, 5], [2, 3, 4, 5], [0, 2, 3, 4, 5], [1, 2, 3], [0, 1, 2, 3], [0, 0, 3, 4], [3, 0, 4, 5], [1, 3, 6], [1, 3, 0], [2, 6], [2, 0], [2, 1, 4, 5], [0, 2, 1, 4, 5], [4, 6], [0, 4, 6], [0, 0, 1], [0, 0, 0, 1], [0, 0, 2, 3], [2, 0, 3, 5], [2, 1, 3, 4], [0, 2, 1, 3, 4], [3, 5], [0, 3, 5], [1, 3, 4], [0, 1, 3, 4], [2, 4], [0, 2, 4], [1, 2, 5], [0, 1, 2, 5], [0, 0], [0, 0, 0], [1, 4, 6], [0, 1, 4, 6], [2, 3, 4, 6], [2, 0, 3, 4], [2, 1, 3, 5], [0, 2, 1, 3, 5], [3, 4], [0, 3, 4], [1, 3, 5], [0, 1, 3, 5], [2, 5], [0, 2, 5], [1, 2, 4], [0, 1, 2, 4], [4, 5], [0, 4, 5], [1], [0, 1], [2, 3], [0, 2, 3], [1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [3, 6], [3, 0], [0, 0, 1, 3, 4], [1, 3, 0, 4, 5], [0, 0, 2, 4], [2, 0, 4, 5], [2, 1], [0, 2, 1], [6], [0, 6], [0, 0, 1, 4], [0, 0, 0, 1, 4], [0, 0, 2, 3, 4], [2, 0, 3, 4, 5], [2, 1, 3], [0, 2, 1, 3], [3, 4, 5], [0, 3, 4, 5], [1, 3], [0, 1, 3], [2], [0, 2], [1, 2, 4, 5], [0, 1, 2, 4, 5], [4], [0, 4], [1, 5], [0, 1, 5], [2, 3, 5], [0, 2, 3, 5], [1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 0, 3], [3, 0, 5], [1, 3, 4, 6], [1, 3, 0, 4], [2, 4, 6], [2, 0, 4], [2, 1, 5], [0, 2, 1, 5], [5], [0, 5], [1, 4], [0, 1, 4], [2, 3, 4], [0, 2, 3, 4], [1, 2, 3, 5], [0, 1, 2, 3, 5], [3, 4, 6], [3, 0, 4], [0, 0, 1, 3], [1, 3, 0, 5], [0, 0, 2], [2, 0, 5], [2, 1, 4], [0, 2, 1, 4], [0, 0, 4], [0, 0, 0, 4], [1, 6], [0, 1, 6], [2, 3, 6], [2, 0, 3], [2, 1, 3, 4, 5], [0, 2, 1, 3, 4, 5], [3], [0, 3], [1, 3, 4, 5], [0, 1, 3, 4, 5], [2, 4, 5], [0, 2, 4, 5], [1, 2], [0, 1, 2]],
    #[[], [2, 0, 3], [0, 1], [2, 1, 3, 6], [2, 4, 5], [0, 3, 4, 6], [0, 2, 1, 4], [1, 3, 4], [0, 0, 3, 4], [0, 2, 4, 6], [0, 1, 3, 4], [2, 1, 4, 6], [2, 3, 6], [0, 5], [0, 2, 1, 3], [1], [4, 6], [2, 0, 3, 4, 6], [0, 1, 4, 6], [2, 1, 3, 4], [0, 0, 2], [0, 3], [0, 2, 1, 6], [1, 3, 6], [3, 5], [0, 2], [0, 1, 3, 6], [2, 1], [2, 3, 4], [0, 0, 0, 4], [0, 2, 1, 3, 4, 6], [1, 4, 6], [0, 0], [0, 2, 3, 6], [0, 0, 0, 1], [1, 2, 3], [2, 4, 6], [0, 3, 4, 5], [0, 1, 2, 4, 6], [3, 1, 4, 6], [3, 4], [2, 0, 4], [0, 3, 1, 4, 6], [1, 2, 4], [2, 3, 5], [0, 6], [0, 1, 2, 3, 6], [0, 0, 1], [4, 5], [0, 2, 3, 4], [0, 1, 4, 5], [1, 2, 3, 4, 6], [2], [0, 0, 0, 3], [0, 1, 2], [3, 1], [3, 6], [2, 0, 6], [0, 3, 1], [1, 2, 6], [0, 0, 2, 3, 4], [0, 4], [0, 1, 2, 3, 4], [1, 4, 5], [6], [2, 0, 3, 6], [0, 1, 6], [2, 1, 3], [0, 0, 2, 4], [0, 3, 4], [0, 2, 1, 4, 6], [1, 3, 4, 6], [3, 4, 5], [0, 2, 4], [0, 1, 3, 4, 6], [2, 1, 4], [2, 3], [0, 0, 0], [0, 2, 1, 3, 6], [1, 6], [4], [2, 0, 3, 4], [0, 1, 4], [2, 1, 3, 4, 6], [2, 5], [0, 3, 6], [0, 2, 1], [1, 3], [0, 0, 3], [0, 2, 6], [0, 1, 3], [2, 1, 6], [2, 3, 4, 6], [0, 4, 5], [0, 2, 1, 3, 4], [1, 4], [5], [0, 2, 3], [0, 1, 5], [1, 2, 3, 6], [2, 4], [0, 0, 0, 3, 4], [0, 1, 2, 4], [3, 1, 4], [3, 4, 6], [2, 0, 4, 6], [0, 3, 1, 4], [1, 2, 4, 6], [0, 0, 2, 3], [0], [0, 1, 2, 3], [1, 5], [0, 0, 4], [0, 2, 3, 4, 6], [0, 0, 0, 1, 4], [1, 2, 3, 4], [2, 6], [0, 3, 5], [0, 1, 2, 6], [3, 1, 6], [3], [2, 0], [0, 3, 1, 6], [1, 2], [2, 3, 4, 5], [0, 4, 6], [0, 1, 2, 3, 4, 6], [0, 0, 1, 4]],
    #[[], [0, 5, 6], [0, 1, 6], [1, 2, 4], [2, 3, 5], [2, 0, 3], [0, 2, 1, 3, 5], [1, 3, 4, 5], [4], [4, 0, 5], [0, 4, 1], [1, 2], [2, 3, 4, 5], [2, 0, 3, 4], [0, 2, 1, 3, 4, 5], [1, 3, 5], [5, 6], [0], [0, 1, 5], [2, 1, 4, 5], [1, 2, 1], [0, 2, 3, 5], [0, 1, 2, 3], [3, 4, 1], [4, 5, 6], [0, 4], [0, 1, 4, 5], [2, 1, 5], [1, 2, 1, 4], [0, 2, 3, 4, 5], [0, 1, 2, 3, 4], [1, 3, 6], [2], [2, 0, 5], [0, 2, 1], [1, 4], [3, 5], [0, 3, 6], [0, 3, 5, 1], [1, 2, 3, 4, 5], [2, 4], [2, 0, 4, 5], [0, 2, 1, 4], [1], [3, 4, 5], [3, 4, 0], [0, 3, 4, 1, 5], [1, 2, 3, 5], [2, 5, 6], [0, 2], [0, 1, 2, 5], [4, 1, 5], [3, 6], [0, 3, 5], [0, 1, 3], [2, 1, 3, 4], [2, 4, 5, 6], [0, 2, 4], [0, 1, 2, 4, 5], [5, 1], [1, 4, 1], [0, 3, 4, 5], [0, 1, 3, 4], [2, 1, 3], [6], [0, 5], [0, 1], [2, 1, 4], [1, 2, 1, 5], [0, 2, 3], [0, 1, 2, 3, 5], [3, 4, 1, 5], [4, 6], [0, 4, 5], [0, 1, 4], [2, 1], [1, 2, 1, 4, 5], [0, 2, 3, 4], [0, 1, 2, 3, 4, 5], [3, 5, 1], [5], [0, 6], [0, 5, 1], [1, 2, 4, 5], [2, 3], [2, 0, 3, 5], [0, 2, 1, 3], [1, 3, 4], [4, 5], [4, 0], [0, 4, 1, 5], [1, 2, 5], [2, 3, 4], [2, 0, 3, 4, 5], [0, 2, 1, 3, 4], [1, 3], [2, 6], [0, 2, 5], [0, 1, 2], [4, 1], [1, 5, 1], [0, 3], [0, 1, 3, 5], [2, 1, 3, 4, 5], [2, 4, 6], [0, 2, 4, 5], [0, 1, 2, 4], [1, 6], [1, 4, 1, 5], [0, 3, 4], [0, 1, 3, 4, 5], [2, 1, 3, 5], [2, 5], [2, 0], [0, 2, 1, 5], [1, 4, 5], [3], [0, 1, 5, 1], [0, 1, 3, 6], [1, 2, 3, 4], [2, 4, 5], [2, 0, 4], [0, 2, 1, 4, 5], [1, 5], [3, 4], [3, 4, 0, 5], [0, 3, 4, 1], [1, 2, 3]]]) i |>.getD k.val []

def generatorIndex (i : Fin 4) (j : Fin 8) : Fin (size i) :=
  ⟨(![![97,
    125,
    186,
    56,
    240,
    160,
    192,
    128],
    ![1,
    50,
    76,
    120,
    80,
    96,
    64,
    0],
    ![109,
    15,
    52,
    120,
    80,
    96,
    64,
    0],
    ![17,
    43,
    32,
    116,
    8,
    80,
    64,
    0]]) i j % size i, Nat.mod_lt _ (NeZero.pos _)⟩

set_option maxHeartbeats 16000000 in
theorem generatorIndex_valid : ∀ i j, element i (generatorIndex i j) = generators i j := by
  decide +kernel

def evalWord (i : Fin 4) : List (Fin 8) → SylowModel
  | [] => 1
  | j :: w => fastMul (element i (generatorIndex i j)) (evalWord i w)

theorem evalWord_eq (i : Fin 4) (w : List (Fin 8)) :
    evalWord i w = (w.map (generators i)).prod := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [evalWord, fastMul_element, generatorIndex_valid, ih]
    rfl

set_option maxHeartbeats 16000000 in
theorem words_valid : ∀ i k, ((words i k).map (generators i)).prod = element i k := by
  simp_rw [← evalWord_eq]
  decide +kernel

theorem element_mem (i : Fin 4) (k : Fin (size i)) :
    element i k ∈ smallEvenCandidate (rankFiveIndex i) := by
  rw [← words_valid i k]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact generators_mem i j

def enumeration (i : Fin 4) : Fin (size i) ≃ smallEvenCandidate (rankFiveIndex i) where
  toFun k := ⟨element i k, element_mem i k⟩
  invFun x := index i x.val
  left_inv := index_element i
  right_inv x := Subtype.ext (candidate_le_carrier i x.property)

def projection (i : Fin 4) : smallEvenCandidate (rankFiveIndex i) →* Binary 5 :=
  MonoidHom.mk' (fun x => label i x.val) (by
    intro x y
    have hx := candidate_le_carrier i x.property
    have hy := candidate_le_carrier i y.property
    change element i (index i x.val) = x.val at hx
    change element i (index i y.val) = y.val at hy
    change label i (x.val * y.val) = label i x.val * label i y.val
    rw [← hx, ← hy]
    exact label_mul i _ _)

set_option maxHeartbeats 16000000 in
theorem projection_surjective (i : Fin 4) : Function.Surjective (projection i) := by
  have h : ∀ i (v : Binary 5), ∃ k : Fin (size i), label i (element i k) = v := by
    decide +kernel
  intro v
  obtain ⟨k, hk⟩ := h i v
  exact ⟨enumeration i k, hk⟩

set_option maxHeartbeats 16000000 in
def squareRoot (i : Fin 4) (k : Fin (size i)) : Fin (size i) :=
  ⟨(![#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 183, 0, 0, 0, 0, 0, 0, 0, 236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) i |>.getD k.val 0 |>.mod (size i), Nat.mod_lt _ (NeZero.pos _)⟩

set_option maxHeartbeats 16000000 in
theorem squareRoot_valid : ∀ i k, label i (element i k) = 1 →
    element i (squareRoot i k) ^ 2 = element i k := by
  simp_rw [← fastPow_eq _ (element_even _ _)]
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem projection_ker (i : Fin 4) :
    (projection i).ker = frattini (smallEvenCandidate (rankFiveIndex i)) := by
  rw [((IsPGroup.of_card (n := 12) card).to_subgroup _).frattini_eq_closure_squares]
  apply le_antisymm
  · intro x hx
    obtain ⟨k, rfl⟩ := (enumeration i).surjective x
    have h : enumeration i (squareRoot i k) ^ 2 = enumeration i k :=
      Subtype.ext (squareRoot_valid i k hx)
    rw [← h]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    change projection i (x ^ 2) = 1
    rw [map_pow]
    exact (by decide +kernel : ∀ v : Binary 5, v ^ 2 = 1) _

end Five
end ReeTwo.SylowModel.SmallEvenAutB
