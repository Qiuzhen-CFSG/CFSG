module
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PrimeRankElementary

/-!
# A centralizing cubic in an elementary plane

An elementary plane normalizing a centerless group of three-rank at most
one cannot act faithfully if the outer automorphism group is a two-group.
Its outer action vanishes; a faithful inner action would embed the plane
in the group, contradicting the rank bound. Thus a nontrivial element of
the original plane centralizes the group.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.833, the decomposition
of the original Sylow three-subgroup into component and centralizer factors.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- An elementary plane normalizing a centerless rank-one group has a
nontrivial centralizing element when the outer automorphism group is a two-group. -/
theorem elementary_plane_centralizer_ne_bot
    {J : Type*} [Group J] [Finite J] (A B : Subgroup J) [B.Normal]
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    (hz : center B = ⊥) (hr : primeRank 3 B ≤ 1)
    (ho : IsPGroup 2 (MulAut.Outer B)) : A ⊓ centralizer (B : Set J) ≠ ⊥ := by
  let f : A →* MulAut B := (MulAut.conjNormal : J →* MulAut B).comp A.subtype
  let o := (QuotientGroup.mk' (MulAut.innerSubgroup B)).comp f
  have h3 : IsPGroup 3 o.range :=
    (IsElementaryAbelian.isPGroup 3 A).of_surjective o.rangeRestrict o.rangeRestrict_surjective
  have hzero : o.range = ⊥ := by
    simpa only [inf_idem] using
      ((ho.to_subgroup o.range).disjoint_of_coprime h3 (by decide)).eq_bot
  have hfi (x : A) : f x ∈ MulAut.innerSubgroup B := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact mem_bot.mp (hzero ▸ (MonoidHom.mem_range.mpr ⟨x,rfl⟩))
  let e : B ≃* MulAut.innerSubgroup B :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  let g : A →* B := e.symm.toMonoidHom.comp (f.codRestrict _ hfi)
  have hg (x : A) : MulAut.conj (g x) = f x :=
    congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hfi x))
  intro hc
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hc]
    refine ⟨x.property,?_⟩
    have hh : x.val ∈ (MulAut.conjNormal : J →* MulAut B).ker := hx
    rwa [MulAut.conjNormal_ker_eq_centralizer] at hh
  have hgi : Function.Injective g := by
    intro x y hh
    apply hf
    rw [←hg,←hg,hh]
  let : IsElementaryAbelian 3 g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hb := (primeRank_le_iff_elementary_card_le B).mp hr g.range inferInstance
  rw [←Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv,hA] at hb
  norm_num at hb

end Theory.GroupTheory
