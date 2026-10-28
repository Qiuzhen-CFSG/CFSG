module

public import Mathlib.Data.List.Rotate

/-!
# A fixed rotation gives a repeated block

If a list of length `s * t` is fixed by rotation through `s` places, it is
`t` copies of its first `s` entries. The prefix commutes with the whole list;
length induction cancels one copy at a time. This elementary word lemma
supplies the repeated-block step in GLS III, Remark 2.8.8.
-/

public section

namespace List
private theorem repeat_of_commute {α : Type*} (b v : List α) (t : ℕ)
    (hlen : v.length = b.length * t) (hc : b ++ v = v ++ b) :
    v = (List.replicate t b).flatten := by
  induction t generalizing v with
  | zero => simpa using hlen
  | succ t ih =>
    have hb : b.length ≤ v.length := by rw [hlen, Nat.mul_succ]; omega
    have htake : v.take b.length = b := by
      have h := congrArg (List.take b.length) hc
      simpa only [List.take_left, List.take_append_of_le_length hb] using h.symm
    have hv : v = b ++ v.drop b.length := by
      calc
        v = v.take b.length ++ v.drop b.length := (List.take_append_drop _ _).symm
        _ = b ++ v.drop b.length := by rw [htake]
    have hcomm : b ++ v.drop b.length = v.drop b.length ++ b := by
      rw [hv, List.append_assoc] at hc
      exact List.append_cancel_left hc
    have hl : (v.drop b.length).length = b.length * t := by
      simp only [List.length_drop, hlen, Nat.mul_succ, Nat.add_sub_cancel]
    calc
      v = b ++ v.drop b.length := hv
      _ = b ++ (List.replicate t b).flatten := by rw [ih _ hl hcomm]
      _ = (List.replicate (t + 1) b).flatten := by simp [List.replicate_succ]

theorem eq_flatten_replicate_take_of_rotate_eq {α : Type*} (w : List α) (s t : ℕ)
    (ht : 0 < t) (hlen : w.length = s * t) (hrot : w.rotate s = w) :
    w = (List.replicate t (w.take s)).flatten := by
  have hs : s ≤ w.length := by rw [hlen]; exact Nat.le_mul_of_pos_right s ht
  have hc : w.take s ++ w = w ++ w.take s := by
    rw [List.rotate_eq_drop_append_take hs] at hrot
    calc
      w.take s ++ w = w.take s ++ (w.drop s ++ w.take s) := by rw [hrot]
      _ = w ++ w.take s := by rw [← List.append_assoc, List.take_append_drop]
  apply repeat_of_commute _ _ t _ hc
  simpa only [List.length_take, Nat.min_eq_left hs] using hlen
end List
