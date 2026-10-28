module
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.GroupTheory.PerfectAutomorphismStabilizer

/-!
# Perfect automorphism groups stabilizing a two-subgroup of G₂

Soluble outer automorphisms make a perfect automorphism subgroup inner.
The centerless G₂ model gives a faithful implementing homomorphism, whose
image lies in the literal two-subgroup normalizer. The proved parabolic
normalizer theorem then bounds every odd-prime rank by one.

Source: Aschbacher–Smith C.4.5–7, printed pp.152–153.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Atlas.G2.PerfectSubgroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem perfect_automorphism_stabilizer_odd_rank_le_one
    (P : Subgroup (Atlas.G2.Model F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hq : 2 < Nat.card F) (A : Subgroup (MulAut (Atlas.G2.Model F))) [Group.IsPerfect A]
    [Group.IsSolvable (MulAut.Outer (Atlas.G2.Model F))]
    (hA : A ≤ MulAction.stabilizer (MulAut (Atlas.G2.Model F)) P)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift A
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)
  by_contra! hb
  apply Atlas.G2.PerfectSubgroups.no_perfect_odd_rank_two_in_two_normalizer
    P hp hne ho (by omega) hq f hf
  rintro _ ⟨a,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [hconj a]
  exact hA a.property

end Atlas.G2.PerfectSubgroups
