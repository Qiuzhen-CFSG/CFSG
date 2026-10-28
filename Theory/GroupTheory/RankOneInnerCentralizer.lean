module
public import Theory.GroupTheory.RankOneOuterCentralizer
/-!
# A centralizing cubic detected by an inner elementary-plane action

A faithful inner action on a centerless group lifts injectively to that
group. An elementary nine therefore cannot act faithfully by inner
automorphisms on a group of three-rank at most one. This keeps the
original plane and its literal centralizer, with no restriction on the
whole outer automorphism group.

Source application: Aschbacher--Smith 12.6.31, printed p.836.
-/
public section
open Subgroup
namespace Theory.GroupTheory
/-- An inner action of an elementary nine on a centerless group of
three-rank at most one has nontrivial kernel in the original plane. -/
theorem elementary_plane_inner_centralizer_ne_bot
    {J : Type*} [Group J] [Finite J] (A B : Subgroup J) [B.Normal]
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    (hz : center B = ⊥) (hr : primeRank 3 B ≤ 1)
    (hinner : A ≤ B ⊔ centralizer (B : Set J)) :
    A ⊓ centralizer (B : Set J) ≠ ⊥ := by
  let f : A →* MulAut B := (MulAut.conjNormal : J →* MulAut B).comp A.subtype
  have hfi (x : A) : f x ∈ MulAut.innerSubgroup B := by
    have hh := hinner x.property
    rwa [←MulAut.conjNormal_comap_innerSubgroup] at hh
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
