module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Normal subgroups detected by a simple image

In a p-perfect group, a normal subgroup not contained in the p-group kernel
of a surjection onto a simple group is the whole group. Simplicity makes
its image surjective; the remaining quotient is a p-group and p-perfectness
kills it. No finiteness assumption is needed.

Source application: Aschbacher–Smith 13.2.9, printed p. 880, identifying
[L,X] with the original A₅ component once its image is nontrivial.
-/
public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] {p : ℕ}

theorem normal_eq_top_of_simple_image [IsSimpleGroup D]
    (hG : IsPPerfect p G) (f : G →* D) (hf : Function.Surjective f)
    (hp : IsPGroup p f.ker) (N : Subgroup G) [N.Normal]
    (hne : ¬ N ≤ f.ker) : N = ⊤ := by
  have hn : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  have ht : N.map f = ⊤ := hn.eq_bot_or_eq_top.resolve_left
    (fun hb => hne ((map_eq_bot_iff _).mp hb))
  have hgen : N ⊔ f.ker = ⊤ := by
    have h := congrArg (comap f) ht
    simpa only [comap_map_eq,comap_top] using h
  exact hG N inferInstance (isPGroup_quotient_of_sup_eq_top N f.ker hp hgen)
end Subgroup

