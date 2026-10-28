module

public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect subgroups in rank-one extensions

A perfect group has trivial image in an abelian group. Thus a homomorphism
into a product of a rank-one factor and an abelian group sends every element
into the first factor. If its kernel is a two-group, the restriction to a
Sylow three-subgroup is injective. Cyclic three-subgroups in the first factor
then give three-rank at most one in the original perfect group.

This elementary argument is used for the full Ree parabolics in the
Theorem C inspection of Aschbacher–Smith, E.6.18, printed p.252 of
`refs/quasithin.pdf`. The hypotheses retain the actual homomorphism and kernel.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A perfect group with a two-kernel projection to a rank-one factor times an
abelian group has three-rank at most one. -/
theorem perfect_threeRank_le_one_of_projection
    {G H A : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [Group H] [CommGroup A]
    (π : G →* H × A) (hker : IsPGroup 2 π.ker)
    (hcyc : ∀ U : Subgroup H, IsPGroup 3 U → IsCyclic U) :
    primeRank 3 G ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let χ : G →* A := (MonoidHom.snd H A).comp π
  let : Group.IsPerfect χ.range := Group.IsPerfect.range χ
  let : Subsingleton χ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hχ (x : G) : χ x = 1 :=
    congrArg Subtype.val (Subsingleton.elim (χ.rangeRestrict x) 1)
  let P : Sylow 3 G := Classical.choice inferInstance
  let f : P →* H := ((MonoidHom.fst H A).comp π).comp (P : Subgroup G).subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hxker : (x : G) ∈ π.ker := by
      apply Prod.ext hx (hχ x)
    exact Subtype.ext (Subgroup.disjoint_def.mp
      (P.isPGroup'.disjoint_of_coprime hker (by decide : Nat.Coprime 3 2))
      x.property hxker)
  let : IsCyclic f.range := hcyc f.range
    (P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hc : IsCyclic P := isCyclic_of_injective f.rangeRestrict
    (fun x y h => hf (congrArg Subtype.val h))
  exact P.primeRank_le_one_of_isCyclic hc

/-- The same bound applies to a perfect subgroup embedded in the domain of
such a projection; the induced kernel remains a two-group. -/
theorem perfect_threeRank_le_one_of_embedding
    {G L H A : Type*} [Group G] [Group L] [Finite L] [Group.IsPerfect L]
    [Group H] [CommGroup A]
    (π : G →* H × A) (hker : IsPGroup 2 π.ker)
    (f : L →* G) (hf : Function.Injective f)
    (hcyc : ∀ U : Subgroup H, IsPGroup 3 U → IsCyclic U) :
    primeRank 3 L ≤ 1 := by
  apply perfect_threeRank_le_one_of_projection (π.comp f) ?_ hcyc
  exact hker.comap_of_injective f hf

end Theory.GroupTheory
