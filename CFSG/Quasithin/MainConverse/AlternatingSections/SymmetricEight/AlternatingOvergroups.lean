module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.Basic

/-!
# Simple quotients of permutation groups containing the alternating group

If a simple normal subgroup has solvable quotient, a simple quotient of
the whole group is either a copy of that normal subgroup or prime cyclic.
The proof tests the actual image of the normal subgroup, and factors the
homomorphism through its quotient when that image is trivial.

For Aₙ ≤ U ≤ Sₙ, the sign restriction supplies the solvable quotient and
the normal subgroup inside U is genuinely isomorphic to Aₙ. This settles
the alternating and symmetric branches of the primitive-group calculation
used for condition K in Aschbacher–Smith, Theorem 0.1.2(3), printed pp.4
and 482. Only quotients of U itself are asserted here; its other sections
remain part of the exhaustive permutation-subgroup argument.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

namespace SymmetricEight

/-- A simple normal carrier and a solvable outer quotient suffice to classify
the simple quotients of the whole group. -/
public theorem simple_quotient_constructed_of_simple_normal {G S : Type*}
    [Group G] [Group S] [IsSimpleGroup S]
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N] [Group.IsSolvable (G ⧸ N)]
    (hN : IsConstructedCarrier N) (f : G →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  have hn : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hker : N ≤ f.ker := by
      intro x hx
      have hm : f x ∈ N.map f := Subgroup.mem_map_of_mem f hx
      exact Subgroup.mem_bot.mp (hb ▸ hm)
    let q := QuotientGroup.lift N f hker
    have hq : Function.Surjective q := by
      intro s
      obtain ⟨g, rfl⟩ := hf s
      exact ⟨QuotientGroup.mk g, rfl⟩
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hq
    exact .cyclic (primeCyclic_of_solvable_simple S)
  · apply simple_quotient_constructed hN (f.comp N.subtype)
    intro s
    obtain ⟨g, hg, hgs⟩ := (show s ∈ N.map f from ht ▸ Subgroup.mem_top s)
    exact ⟨⟨g, hg⟩, hgs⟩

end SymmetricEight

/-- The alternating-containing branch in every degree at least five. -/
public theorem alternatingOvergroup_simple_quotient_constructed (n : ℕ) (hn : 5 ≤ n)
    (U : Subgroup (Equiv.Perm (Fin n))) (hU : alternatingGroup (Fin n) ≤ U)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  let N := (alternatingGroup (Fin n)).subgroupOf U
  let e : N ≃* alternatingGroup (Fin n) := Subgroup.subgroupOfEquivOfLe hU
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  let : IsSimpleGroup N := e.isSimpleGroup
  let q := (Equiv.Perm.sign (α := Fin n)).comp U.subtype
  let : Group.IsSolvable (U ⧸ N) := by
    change Group.IsSolvable (U ⧸ q.ker)
    let a := QuotientGroup.quotientKerEquivRange q
    exact Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective
  exact SymmetricEight.simple_quotient_constructed_of_simple_normal N
    (.alternating n hn ⟨e⟩) f hf

end CFSG.Quasithin.MainConverse
