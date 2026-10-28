module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Elimination
public import Mathlib.Algebra.CharP.Two

/-!
# The kernel of the final binary row form

The rows `e_i + v_i e_0`, for all nonzero coordinates i, express exactly
that a column is its zeroth coordinate times v, provided v_0 = 1.
This is the normal form consumed by the concrete HS kernel certificate.
-/

@[expose] public section

namespace PackedBinaryRows
open Thompson.BinaryMatrix

def normalRow (v i : Nat) : Nat :=
  2^(i+1) ^^^ (if v / 2^(i+1) % 2 == 1 then 1 else 0)

def normalState (n v : Nat) : State :=
  ((List.range n).reverse.map (normalRow v), [0])

lemma decode_pow (n k : Nat) (hk : k < n) :
    (fun j : Fin n => bit (2^k) j.val) = Pi.single ⟨k, hk⟩ (1 : ZMod 2) := by
  funext j
  simp [bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

lemma normalRow_decode (n v i : Nat) (hi : i < n) :
    (fun j : Fin (n+1) => bit (normalRow v i) j.val) =
      Pi.single ⟨i+1, by omega⟩ (1 : ZMod 2) + Pi.single 0 (bit v (i+1)) := by
  have hlow :
      (fun j : Fin (n+1) => bit (if v / 2^(i+1) % 2 == 1 then 1 else 0) j.val) =
        Pi.single 0 (bit v (i+1)) := by
    by_cases hv : v / 2^(i+1) % 2 = 1
    · have hb : bit v (i+1) = 1 := by
        simp only [bit, Nat.testBit_eq_decide_div_mod_eq, hv, decide_true, ite_true]
      simp only [beq_iff_eq, hv, ite_true, hb]
      exact decode_pow (n+1) 0 (by omega)
    · have hb : bit v (i+1) = 0 := by
        simp only [bit, Nat.testBit_eq_decide_div_mod_eq, hv, decide_false, Bool.false_eq_true,
          ite_false]
      simp only [beq_iff_eq, hv, ite_false, hb]
      funext j
      simp [bit]
  have hh := congrArg₂ (fun x y : Fin (n+1) → ZMod 2 => x+y)
    (decode_pow (n+1) (i+1) (by omega)) hlow
  funext j
  simpa only [normalRow, bit_xor, Pi.add_apply] using congrFun hh j

lemma normalRow_dot (n v i : Nat) (hi : i < n) (w : Fin (n+1) → ZMod 2) :
    (fun j : Fin (n+1) => bit (normalRow v i) j.val) ⬝ᵥ w =
      w ⟨i+1, by omega⟩ + bit v (i+1) * w 0 := by
  rw [normalRow_decode n v i hi, add_dotProduct, single_dotProduct, single_dotProduct,
    one_mul]

lemma normalState_solutions (n v : Nat) (hv : bit v 0 = 1) (w : Fin (n+1) → ZMod 2) :
    stateSolutions (n+1) (normalState n v) w ↔
      w = w 0 • (fun i : Fin (n+1) => bit v i.val) := by
  simp only [stateSolutions, normalState, solutions_zero_cons]
  have hn : solutions (n+1) [] w := solutions_nil _ _
  simp only [hn, and_true]
  constructor
  · intro h
    funext i
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      subst i
      simp [hv]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have hkn : k < n := by omega
      have hr : normalRow v k ∈ (List.range n).reverse.map (normalRow v) :=
        List.mem_map.mpr ⟨k, List.mem_reverse.mpr (List.mem_range.mpr hkn), rfl⟩
      have he := h _ hr
      rw [normalRow_dot n v k hkn w, CharTwo.add_eq_zero] at he
      have hii : (⟨k+1, by omega⟩ : Fin (n+1)) = i := Fin.ext (by change k+1 = i.val; omega)
      rw [hii] at he
      simpa only [hk, Pi.smul_apply, smul_eq_mul, mul_comm] using he
  · intro h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    have hkn : k < n := List.mem_range.mp (List.mem_reverse.mp hk)
    rw [normalRow_dot n v k hkn w, CharTwo.add_eq_zero]
    have he := congrFun h ⟨k+1, by omega⟩
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using he

end PackedBinaryRows
