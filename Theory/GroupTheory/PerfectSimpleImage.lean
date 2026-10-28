module
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.GroupTheory.SolvableResidual

/-!
# Perfect actors retain their simple quotient in every nontrivial image

Let a perfect group surject onto a simple group with solvable kernel. For
any homomorphism, the image of its kernel in that simple quotient is either
trivial or full. The first case realizes the simple group as a section of
the target; the second makes the homomorphic image solvable and hence trivial.

This is the narrower outer-action reduction for the actual G2(2)' residual
in Aschbacher--Smith 4.4.10, printed p.621; no full Schreier property is needed
when the actual simple section can be excluded.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {F S H:Type*} [Group F] [Group S] [Group H]
  [IsSimpleGroup S] [Group.IsPerfect F]

/-- Absence of the actual simple section kills every image of the perfect covering actor. -/
theorem hom_eq_one_of_no_simple_section
    (q:F→*S) (hq:Function.Surjective q) [Group.IsSolvable q.ker]
    (hno:∀U:Subgroup H,∀g:U→*S,¬Function.Surjective g)
    (f:F→*H) : f=1 := by
  have hn:(f.ker.map q).Normal:=(inferInstance:f.ker.Normal).map q hq
  let :=hn
  rcases hn.eq_bot_or_eq_top with hb|ht
  · have hker:f.ker≤q.ker:=(Subgroup.map_eq_bot_iff _).mp hb
    let g:F⧸f.ker→*S:=QuotientGroup.lift f.ker q hker
    have hg:Function.Surjective g:=by
      intro s
      obtain ⟨a,rfl⟩:=hq s
      exact ⟨QuotientGroup.mk a,rfl⟩
    let e:=QuotientGroup.quotientKerEquivRange f
    exact (hno f.range (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective)).elim
  · have hgen:f.ker⊔q.ker=⊤:=by
      have hh:=congrArg (Subgroup.comap q) ht
      simpa only [comap_map_eq,comap_top] using hh
    have hr:q.ker.map f=f.range:=by
      have hh:=congrArg (Subgroup.map f) hgen
      rw [Subgroup.map_sup,show f.ker.map f=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,
        bot_sup_eq,←MonoidHom.range_eq_map] at hh
      exact hh
    have hs:Group.IsSolvable (q.ker.map f):=Group.isSolvable_of_surjective (f.subgroupMap_surjective q.ker)
    let :Group.IsSolvable f.range:=hr ▸ hs
    let :Group.IsPerfect f.range:=Group.IsPerfect.range f
    have htr:Subsingleton f.range:=by
      by_contra! hnt
      exact Group.IsPerfect.not_isSolvable f.range inferInstance
    ext x
    exact congrArg Subtype.val (htr.elim (f.rangeRestrict x) 1)
end Theory.GroupTheory
