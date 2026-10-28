module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Nilpotent

/-!
# Two-core transfer through a rank-one factor and a torus

Suppose a group maps to a product L × T with solvable kernel, where T is
solvable and has no nonidentity two-elements. If every nonsolvable subgroup
of L has trivial two-core, the two-core of any nonsolvable source group is
killed by the product map. Its projection to L is normal in the actual image,
whose nonsolvability follows from the solvable kernel and torus; the T
projection is killed by its two-power order.

The subgroup version retains the inclusion in the full parabolic and
identifies its kernel with a specified ambient radical. It is applied to
both concrete Ree Levi projections in `ReeF4.ParabolicSubgroupCores`.
Source: solvable extension theory and the rank-one factors in
Aschbacher--Smith F.1.12(I)(5), printed pp.263--264; GLS3, Theorem 2.6.5.
-/

public section

open Subgroup
namespace ReeF4.ParabolicSubgroupCores
variable {G L T : Type*} [Group G] [Group L] [Group T]

/-- A nonsolvable source has its two-core in the solvable kernel of the product map. -/
theorem twoCore_le_ker_of_rankOne_product (f : G →* L × T)
    [Group.IsSolvable f.ker] [Group.IsSolvable T]
    (ht : ∀ t : T, ∀ k : ℕ, t ^ (2 ^ k) = 1 → t = 1)
    (hl : ∀ H : Subgroup L, ¬ Group.IsSolvable H → pCore 2 H = ⊥)
    (hG : ¬ Group.IsSolvable G) : pCore 2 G ≤ f.ker := by
  let a : G →* L := (MonoidHom.fst L T).comp f
  have hA : ¬ Group.IsSolvable a.range := by
    intro hA
    let : Group.IsSolvable a.range := hA
    let b : G →* a.range × T := a.rangeRestrict.prod ((MonoidHom.snd L T).comp f)
    apply hG
    apply Group.isSolvable_of_ker_le_range f.ker.subtype b
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have h := congrArg (fun y : a.range × T => ((y.1 : L), y.2))
      (show b x = 1 from hx)
    exact h
  have hm : (pCore 2 G).map a.rangeRestrict ≤ pCore 2 a.range :=
    le_sSup ⟨Normal.map inferInstance _ a.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  rw [hl a.range hA] at hm
  intro x hx
  have hax : a x = 1 := congrArg Subtype.val (mem_bot.mp
    (hm (mem_map_of_mem a.rangeRestrict hx)))
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := G)) ⟨x, hx⟩
  have htx : (f x).2 = 1 := ht (f x).2 k (by
    have h := congrArg (fun y : pCore 2 G => (f y.val).2) hk
    simpa using h)
  exact Prod.ext hax htx

/-- Subgroup two-core containment for a full-parabolic projection with a two-group kernel. -/
theorem pCoreIn_le_of_rankOne_product {A : Type*} [Group A] [Finite A]
    (P R J : Subgroup A) (hJP : J ≤ P) (f : P →* L × T)
    (hker : f.ker = R.subgroupOf P) (hp : IsPGroup 2 f.ker)
    [Group.IsSolvable T]
    (ht : ∀ t : T, ∀ k : ℕ, t ^ (2 ^ k) = 1 → t = 1)
    (hl : ∀ H : Subgroup L, ¬ Group.IsSolvable H → pCore 2 H = ⊥)
    (hJ : ¬ Group.IsSolvable J) : J.pCoreIn 2 ≤ R := by
  let a : J →* L × T := f.comp (inclusion hJP)
  have ha : IsPGroup 2 a.ker := hp.comap_of_injective
    (inclusion hJP) (inclusion_injective hJP)
  let : Group.IsNilpotent a.ker := ha.isNilpotent
  have hc := twoCore_le_ker_of_rankOne_product a ht hl hJ
  rintro x ⟨y, hy, rfl⟩
  have hy' : inclusion hJP y ∈ f.ker := hc hy
  rw [hker] at hy'
  exact hy'
end ReeF4.ParabolicSubgroupCores
