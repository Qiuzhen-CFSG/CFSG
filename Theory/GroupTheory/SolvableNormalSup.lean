module

public import Mathlib.GroupTheory.Solvable

/-!
# Solvability from a normal solvable supplement

If a normal solvable subgroup and a solvable subgroup generate a finite or
infinite group, the quotient by the normal subgroup is a solvable image of the
supplement. Solvability of extensions then gives solvability of the ambient
group. The result is used in the Dickson subgroup cases for the minimal-simple
PSL₂ converse.

Source: the elementary extension argument in Huppert II.8.27; no
classification theorem is used.
-/

namespace Group

/-- A normal solvable subgroup with a solvable supplement generates a solvable
group. -/
public theorem isSolvable_of_normal_sup_eq_top
    {G : Type*} [Group G] (N C : Subgroup G) [N.Normal]
    [IsSolvable N] [IsSolvable C] (hsup : N ⊔ C = ⊤) : IsSolvable G := by
  let q := QuotientGroup.mk' N
  let f : C →* G ⧸ N := q.comp C.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ N ⊔ C := by rw [hsup]; trivial
    obtain ⟨n, hn, c, hc, hgc⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N) (t := C)).mp hg
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff (N := N) n).mpr hn
    refine ⟨⟨c, hc⟩, ?_⟩
    change q c = q g
    rw [← hgc, map_mul, hqn, one_mul]
  let : IsSolvable (G ⧸ N) := isSolvable_of_surjective hf
  exact (isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

end Group
