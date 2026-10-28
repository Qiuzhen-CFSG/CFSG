module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# Normal residuals across solvable kernels

A normal subgroup with a nonsolvable simple quotient maps onto a simple
Levi quotient after a solvable kernel is removed. Factoring the quotient
map proves that the two simple groups are isomorphic and hence have the
same order. Apply this to the two actual ambient residuals, using
`Contrary.residual_normal`; the two central covering maps have solvable
kernels and remain distinct throughout the argument.

Source: the inner/outer residual comparison in Aschbacher–Smith 16.4.11(2),
printed p.1193, combined manuscript of 1 March 2004.
-/

public section
open Subgroup

private theorem normal_simple_card {X A S : Type*} [Group X] [Group A] [Group S]
    [IsSimpleGroup A] [IsSimpleGroup S]
    (f : X →* A) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (N : Subgroup X) [N.Normal] (h : N →* S) (hh : Function.Surjective h)
    (hS : ¬ Group.IsSolvable S) : Nat.card S = Nat.card A := by
  let P := f.ker.subgroupOf N
  let j : P →* f.ker := (N.subtype.comp P.subtype).codRestrict f.ker (fun x => x.property)
  let : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
    (f := j) (by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : f.ker => (z : X)) he)
  let : (P.map h).Normal := (inferInstance : P.Normal).map h hh
  have hbot : P.map h = ⊥ := by
    rcases (inferInstance : (P.map h).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hs : Group.IsSolvable (P.map h) :=
        Group.isSolvable_of_surjective (h.subgroupMap_surjective P)
      rw [ht] at hs
      let := hs
      exact (hS (Group.isSolvable_of_surjective
        (f := (topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom) topEquiv.surjective)).elim
  let W := N.map f
  let q : N →* W := f.subgroupMap N
  have hq : Function.Surjective q := f.subgroupMap_surjective N
  have hk : q.ker ≤ h.ker := by
    intro x hx
    have hp : x ∈ P := congrArg Subtype.val (show q x = 1 from hx)
    exact mem_bot.mp (hbot ▸ mem_map_of_mem h hp)
  let k : W →* S := q.liftOfSurjective hq ⟨h, hk⟩
  have hks : Function.Surjective k := by
    intro s
    obtain ⟨x, rfl⟩ := hh s
    exact ⟨q x, by simp [k]⟩
  let : W.Normal := (inferInstance : N.Normal).map f hf
  have ht : W = ⊤ := by
    rcases (inferInstance : W.Normal).eq_bot_or_eq_top with hb | ht
    · have hs : Group.IsSolvable W := by rw [hb]; infer_instance
      let := hs
      exact (hS (Group.isSolvable_of_surjective hks)).elim
    · exact ht
  let e : W ≃* A := (MulEquiv.subgroupCongr ht).trans topEquiv
  let v : A →* S := k.comp e.symm.toMonoidHom
  have hv : Function.Surjective v := hks.comp e.symm.surjective
  exact (Nat.card_congr (MulEquiv.ofBijective v
    ⟨v.injective_of_surjective_of_simple hv, hv⟩).toEquiv).symm

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
private theorem centralMap_solvable_kernel {X : Subgroup G} (hXL : X ≤ L) :
    Group.IsSolvable (centralImageMap hXL).ker := by
  apply Group.isSolvable_of_comm
  intro x y
  have hx : (⟨x.val, hXL x.val.property⟩ : L) ∈ center L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center L) ⟨x.val, hXL x.val.property⟩ = 1
    have he := congrArg Subtype.val x.property
    simpa only [centralImageMap, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] using he
  apply Subtype.ext
  apply Subtype.ext
  change (x.val.val : G) * (y.val.val : G) = (y.val.val : G) * (x.val.val : G)
  exact congrArg Subtype.val
    (mem_center_iff.mp hx ⟨y.val, hXL y.val.property⟩).symm

private theorem ker_comp_solvable {X I A : Type*} [Group X] [Group I] [Group A]
    (f : X →* I) (h : I →* A) [Group.IsSolvable f.ker] [Group.IsSolvable h.ker] :
    Group.IsSolvable (h.comp f).ker :=
  isSolvable_comap_of_solvable_ker f h.ker

/-- Relative normality identifies a nonsolvable simple outer residual with
an inner simple Levi quotient after removing the solvable kernels. -/
theorem normal_residual_card_eq (d : Contrary T z L g R r)
    {M A S : Type*} [Group M] [Group A] [Group S]
    [IsSimpleGroup A] [IsSimpleGroup S]
    (e : (L ⧸ center L) ≃* M)
    (f : pResidual 2 (innerAction d e).fixedSubgroup →* A)
    (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (s : pResidual 2 (outerAction d e).fixedSubgroup ≃* S)
    (hS : ¬ Group.IsSolvable S) : Nat.card S = Nat.card A := by
  let X := residual L r
  let Y := residual (L.conjBy g) z
  let c := centralImageMap ((residual_le L r).trans inf_le_left)
  let i := (innerResidualEquiv d e).toMonoidHom
  let q := f.comp (i.comp c)
  let : Group.IsSolvable c.ker := centralMap_solvable_kernel _
  let : Group.IsSolvable i.ker := by
    rw [(MonoidHom.ker_eq_bot_iff i).mpr (innerResidualEquiv d e).injective]
    infer_instance
  let : Group.IsSolvable (i.comp c).ker := ker_comp_solvable c i
  let : Group.IsSolvable q.ker := ker_comp_solvable (i.comp c) f
  have hq : Function.Surjective q := hf.comp
    ((innerResidualEquiv d e).surjective.comp (centralImageMap_surjective _))
  let N := Y.subgroupOf X
  let : N.Normal := d.residual_normal.2.1
  let j := subgroupOfEquivOfLe d.residual_normal.1
  let cY := centralImageMap ((residual_le (L.conjBy g) z).trans inf_le_left)
  let k := s.toMonoidHom.comp ((outerResidualEquiv d e).toMonoidHom.comp
    (cY.comp j.toMonoidHom))
  have hk : Function.Surjective k := s.surjective.comp
    ((outerResidualEquiv d e).surjective.comp
      ((centralImageMap_surjective ((residual_le (L.conjBy g) z).trans inf_le_left)).comp j.surjective))
  exact normal_simple_card q hq N k hk hS
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
