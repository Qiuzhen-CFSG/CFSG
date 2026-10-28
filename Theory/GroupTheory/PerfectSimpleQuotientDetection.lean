module

public import Theory.GroupTheory.PerfectSimpleImageKernel

/-!
# Detecting trivial actions of a perfect simple extension

In a perfect group with simple quotient modulo a solvable normal subgroup N,
every proper normal subgroup lies in N. Thus an action is trivial if it kills
a subgroup not contained in N. A normal p-subgroup is a special case of the
solvable kernel; no prescribed action or coordinate model is needed.
-/

public section
open Subgroup

namespace Subgroup

/-- A normal subgroup reaching outside a solvable kernel of a simple quotient
is the whole perfect group. -/
theorem eq_top_of_not_le_solvable_simple_quotient
    {B : Type*} [Group B] [Group.IsPerfect B]
    (N K : Subgroup B) [N.Normal] [K.Normal]
    [Group.IsSolvable N] [IsSimpleGroup (B ⧸ N)] (hKN : ¬ K ≤ N) : K = ⊤ := by
  let q := QuotientGroup.mk' N
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : (K.map q).Normal := (inferInstance : K.Normal).map q
    (QuotientGroup.mk'_surjective N)
  rcases (inferInstance : (K.map q).Normal).eq_bot_or_eq_top with hb | ht
  · exact (hKN (by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff K).mp hb)).elim
  · exact eq_top_of_perfect_of_solvable_kernel_image q K ht

end Subgroup

namespace MonoidHom

/-- Killing a subgroup outside the solvable kernel of a simple quotient kills
every homomorphism from the given perfect group. -/
theorem eq_one_of_kills_subgroup_not_le_solvable_simple_quotient
    {B D : Type*} [Group B] [Group D] [Group.IsPerfect B]
    (N L : Subgroup B) [N.Normal] [Group.IsSolvable N]
    [IsSimpleGroup (B ⧸ N)] (f : B →* D)
    (hL : L ≤ f.ker) (hLN : ¬ L ≤ N) : f = 1 := by
  have hk := Subgroup.eq_top_of_not_le_solvable_simple_quotient N f.ker
    (fun h => hLN (hL.trans h))
  ext b
  exact MonoidHom.mem_ker.mp (hk.symm ▸ mem_top b)

end MonoidHom
