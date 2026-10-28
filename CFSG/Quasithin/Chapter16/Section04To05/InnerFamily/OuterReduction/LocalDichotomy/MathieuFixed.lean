module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.QuotientSetup
public import Theory.Mathieu.M22.Properties.IndexTwoFixedInvolutions

/-!
# The M22 index-two fixed-group calculation for the quotient setup

Transport the actual quotient action through an equivalence L/O2(L) with
the concrete Mathieu group. The equivalence restricts to the full fixed
groups, preserves the automorphism order and outer status, and transports
the given index-two subgroup and involution.

The intrinsic theorem proves containment from the earlier 16.1.5(5)
table with its exact maps and faithful actions. That table input remains
explicit; this module does not construct it or complete the M22 exclusion.
The exclusion's owner must supply the table, quotient index, and missing
involution obtained from the local geometry.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
16.1.5(5), printed pp.1171--1172, and proof of 16.4.9(2), printed p.1190.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy

open ComponentTransfer.Intrinsic
open Sporadic.Mathieu.M22FixedInvolutions

variable {G : Type*} [Group G] {L : Subgroup G} {r : G}

/-- The source M22 consequence on the full fixed group of the actual quotient action. -/
theorem m22_involution_mem_index_two
    (table : OuterFixedTable)
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)
    (ho : orderOf (quotientAction hn) = 2)
    (houter : ¬ ∃ g, quotientAction hn = MulAut.conj g)
    (hnp : ¬ Group.IsPerfect (quotientFixed hn))
    (D : Subgroup (quotientFixed hn)) (hD : D.index = 2)
    (x : quotientFixed hn) (hx : orderOf x = 2) : x ∈ D := by
  let a := MulAut.congr e (quotientAction hn)
  let f : quotientFixed hn ≃* a.fixedSubgroup :=
    MulAut.fixedSubgroupCongr e (quotientAction hn)
  have ha : orderOf a = 2 := by
    exact ((MulAut.congr e).orderOf_eq (quotientAction hn)).trans ho
  have haouter : ¬ ∃ g, a = MulAut.conj g := by
    intro hi
    exact houter ((MulAut.congr_inner_iff e (quotientAction hn)).mp hi)
  have hanp : ¬ Group.IsPerfect a.fixedSubgroup := by
    intro hp
    let : Group.IsPerfect a.fixedSubgroup := hp
    exact hnp (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective)
  have hm : f x ∈ D.map f.toMonoidHom :=
    mem_of_outer_fixed_table table a ha haouter hanp _
      ((D.index_map_equiv f).trans hD) (f x) ((f.orderOf_eq x).trans hx)
  rcases hm with ⟨y, hy, heq⟩
  exact f.injective heq ▸ hy

/-- The centralizer image cannot omit an involution in the M22 quotient branch. -/
theorem m22_involution_mem_imageInFixed
    (table : OuterFixedTable)
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)
    (ho : orderOf (quotientAction hn) = 2)
    (houter : ¬ ∃ g, quotientAction hn = MulAut.conj g)
    (hi : (imageInFixed hn).index = 2)
    (x : quotientFixed hn) (hx : orderOf x = 2) : x ∈ imageInFixed hn :=
  m22_involution_mem_index_two table hn e ho houter
    (quotientFixed_not_perfect hn hi) _ hi x hx

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
