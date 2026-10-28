module
public import Mathlib.GroupTheory.Sylow
/-!
# Sylow subgroups in a normal supplement

If G = NC with N normal and C containing a Sylow p-subgroup of N,
then C contains a Sylow p-subgroup of G. The normal-subgroup index
formula gives [G:C] = [N:N intersect C], which is prime to p.

This is the Sylow-central placement step in Aschbacher--Smith,
proof of 12.6.26, printed p.832.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A supplement containing a full Sylow of the normal factor contains an ambient Sylow. -/
theorem exists_sylow_le_of_normal_supplement (N C : Subgroup G) [N.Normal]
    (hgen : N ⊔ C = ⊤) (P : Sylow p N)
    (hPC : (P : Subgroup N).map N.subtype ≤ C) :
    ∃ S : Sylow p G, (S : Subgroup G) ≤ C := by
  have hi : C.index = C.relIndex N := by
    have he : N.relIndex C * C.index = N.relIndex C * C.relIndex N := by
      calc
        _ = (C ⊓ N).index := by
          rw [←inf_relIndex_left (H := C) (K := N)]
          exact relIndex_mul_index inf_le_left
        _ = (C ⊓ N).relIndex N * N.index := (relIndex_mul_index inf_le_right).symm
        _ = N.relIndex C * C.relIndex N := by
          rw [inf_relIndex_right,←relIndex_top_right N,←hgen,relIndex_sup_left]
          exact Nat.mul_comm _ _
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (index_ne_zero_of_finite : N.relIndex C ≠ 0)) he
  have hC : ¬ p ∣ C.index := by
    rw [hi]
    intro hd
    apply P.not_dvd_index
    exact hd.trans (index_dvd_of_le (show (P : Subgroup N) ≤ C.subgroupOf N from
      fun x hx => hPC (mem_map_of_mem N.subtype hx)))
  let Q : Sylow p C := Classical.choice inferInstance
  let R := (Q : Subgroup C).map C.subtype
  have hR : ¬ p ∣ R.index := by
    rw [show R.index = (Q : Subgroup C).index * C.index from index_map_subtype _]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim Q.not_dvd_index hC
  exact ⟨(Q.isPGroup'.map C.subtype).toSylow hR,map_subtype_le _⟩
end Subgroup
