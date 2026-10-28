module
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Encoding

/-!
# Bounded ranges for finite certificate checks

A family of checks on short consecutive ranges proves a predicate on a whole
finite type. Remainders make the final short range harmless. This avoids one
large kernel reduction for the ATLAS point maps and coset transitions.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate
@[expose] public def rangeIndex (n : Nat) [NeZero n] (start : Nat) {k : Nat}
    (r : Fin k) : Fin n := ⟨(start + r.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩

public theorem all_of_blocks {n k b : Nat} [NeZero n] [NeZero k]
    (hn : n ≤ k * b) (P : Fin n → Prop)
    (h : ∀ block : Fin b, ∀ r : Fin k, P (rangeIndex n (k * block.val) r)) :
    ∀ r, P r := by
  intro r
  have hk := NeZero.pos k
  have hb : r.val / k < b := (Nat.div_lt_iff_lt_mul hk).mpr (by simpa only [Nat.mul_comm] using r.isLt.trans_le hn)
  have he : rangeIndex n (k * (r.val / k)) (⟨r.val % k, Nat.mod_lt _ hk⟩ : Fin k) = r := by
    apply Fin.ext
    change (k * (r.val / k) + r.val % k) % n = r.val
    rw [Nat.div_add_mod, Nat.mod_eq_of_lt r.isLt]
  exact he ▸ h ⟨r.val / k, hb⟩ ⟨r.val % k, Nat.mod_lt _ hk⟩
end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate
