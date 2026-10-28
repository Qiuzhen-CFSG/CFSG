module
public import Theory.Mathieu.M24.Properties.OddClasses.Cubic
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Cubic centralizers omit elementary sixteen-groups in native M24

The certified native cubic fusion gives fixed sets of size zero or six;
the involution fusion gives size zero or eight. A cubic acts on the fixed
set of every commuting involution, so their intersection satisfies the
cardinality congruence modulo three. In the fixed-point-free cubic case,
an elementary sixteen-group would act freely on all twenty-four points.
In the six-point case, restriction to those six points is faithful, contrary
to the proved two-rank bound for S6.

This is the native input for the marked paired alternating-five exclusion
in Aschbacher--Smith 2.4.25, printed p.543. The cubic is the actual supplied
element; no centralizer table, elementary-subgroup placement, or Sylow bound
is assumed. The permutation fusion comes from H.14.4 and the native cubic
certificates imported above.
-/

public section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24ChapterHStabilizers
namespace Sporadic.Mathieu.M24CubicElementary
open scoped BigOperators
noncomputable section

private theorem involution_fixed_card (t : M24) (ht : orderOf t = 2) :
    (fixedPoints t).card = 0 ∨ (fixedPoints t).card = 8 := by
  rcases M24InvolutionCentralizers.involution_classes t ht with h | h
  · exact Or.inr (m24Blocks_card _ (class2A_fixed_octad h))
  · exact Or.inl (by rw [class2B_fixed_empty h, Finset.card_empty])

private theorem cubic_fixed_card (x : M24) (hx : orderOf x = 3) :
    (fixedPoints x).card = 0 ∨ (fixedPoints x).card = 6 := by
  obtain ⟨i, hi⟩ := M24OddClasses.order_three_coverage x hx
  rw [fixedPoints_card_eq_of_isConj hi]
  have h : ∀ i : Fin 2,
      (fixedPoints (M24OddClasses.cubicRepresentative i)).card = 0 ∨
        (fixedPoints (M24OddClasses.cubicRepresentative i)).card = 6 := by
    decide +kernel
  exact h i

private theorem fixed_stable (x t : M24) (h : Commute x t) (a : Fin 24) :
    x.val a ∈ fixedPoints t ↔ a ∈ fixedPoints t := by
  rw [mem_fixedPoints, mem_fixedPoints]
  change t.val (x.val a) = x.val a ↔ t.val a = a
  have he : t.val (x.val a) = x.val (t.val a) :=
    congrArg (fun z : M24 => z.val a) h.eq.symm
  rw [he]
  exact x.val.injective.eq_iff

private def restricted (x t : M24) (h : Commute x t) : Equiv.Perm (fixedPoints t) :=
  x.val.subtypePerm (fixed_stable x t h)

private theorem fixed_intersection_mod_three (x t : M24) (hx : orderOf x = 3)
    (h : Commute x t) :
    (fixedPoints t).card % 3 = (fixedPoints t ∩ fixedPoints x).card % 3 := by
  classical
  let σ := restricted x t h
  have hp : σ ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change x.val (x.val (x.val a.val)) = a.val
    have he := congrArg (fun z : M24 => z.val a.val) (pow_orderOf_eq_one x)
    rw [hx] at he
    simpa only [pow_succ, pow_zero, Subgroup.coe_mul, Equiv.Perm.mul_apply,
      Subgroup.coe_one, Equiv.Perm.one_apply] using he
  have hm (a : fixedPoints t) : a ∈ σ.supportᶜ ↔ a.val ∈ fixedPoints x := by
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, mem_fixedPoints]
    change (⟨x.val a.val, _⟩ : fixedPoints t) = a ↔ x.val a.val = a.val
    exact Subtype.ext_iff
  let e : ↥(σ.supportᶜ) ≃ ↥(fixedPoints t ∩ fixedPoints x) := {
    toFun a := ⟨a.val.val, Finset.mem_inter.mpr ⟨a.val.property, (hm a.val).mp a.property⟩⟩
    invFun a := ⟨⟨a.val, (Finset.mem_inter.mp a.property).1⟩,
      (hm _).mpr (Finset.mem_inter.mp a.property).2⟩
    left_inv a := by cases a; rfl
    right_inv a := by cases a; rfl }
  have hc : σ.supportᶜ.card = (fixedPoints t ∩ fixedPoints x).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hp
  rw [hc, Fintype.card_coe] at hmod
  exact hmod.symm

private theorem fixed_free_involution (x : M24) (hx : orderOf x = 3)
    (hfree : (fixedPoints x).card = 0) (t : M24) (ht : orderOf t = 2)
    (h : Commute x t) : fixedPoints t = ∅ := by
  have hm := fixed_intersection_mod_three x t hx h
  rw [Finset.card_eq_zero.mp hfree, Finset.inter_empty, Finset.card_empty] at hm
  rcases involution_fixed_card t ht with ht | ht
  · exact Finset.card_eq_zero.mp ht
  · rw [ht] at hm
    norm_num at hm

private theorem six_fixed_faithful_involution (x : M24) (hx : orderOf x = 3)
    (hfix : (fixedPoints x).card = 6) (t : M24) (ht : orderOf t = 2)
    (h : Commute x t) (hsub : fixedPoints x ⊆ fixedPoints t) : False := by
  have hm := fixed_intersection_mod_three x t hx h
  rw [Finset.inter_eq_right.mpr hsub, hfix] at hm
  have hle := Finset.card_le_card hsub
  rcases involution_fixed_card t ht with ht | ht <;> omega

private theorem free_card_dvd {U X : Type*} [Group U] [Finite U] [Finite X]
    [MulAction U X] [IsCancelSMul U X] : Nat.card U ∣ Nat.card X := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let : Fintype X := Fintype.ofFinite X
  let : ∀ u : U, Fintype (MulAction.fixedBy X u) := fun _ => Fintype.ofFinite _
  have hsum : (∑ u : U, Nat.card (MulAction.fixedBy X u)) = Nat.card X := by
    rw [Finset.sum_eq_single 1]
    · simp [MulAction.fixedBy_one_eq_univ]
    · intro u _ hu
      have he : MulAction.fixedBy X u = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro a ha
        exact hu (IsCancelSMul.eq_one_of_smul ((MulAction.mem_fixedBy).mp ha))
      simp [he]
    · simp
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group U X
  have he : Nat.card X = Nat.card (Quotient (MulAction.orbitRel U X)) * Nat.card U := by
    rw [← hsum]
    simpa only [Nat.card_eq_fintype_card] using hb
  rw [he]
  exact dvd_mul_left _ _

/-- No native cubic element centralizes an elementary subgroup of order sixteen. -/
theorem not_centralizes_elementary_sixteen (U : Subgroup M24)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 16)
    (x : M24) (hx : orderOf x = 3)
    (hC : U ≤ centralizer ({x} : Set M24)) : False := by
  classical
  have hc (u : U) : Commute x u.val :=
    (mem_centralizer_singleton_iff.mp (hC u.property)).symm
  have ho (u : U) (hu : u ≠ 1) : orderOf u.val = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u.val u.property)
      (fun he => hu (Subtype.ext he))
  rcases cubic_fixed_card x hx with hfree | hfix
  · let : IsCancelSMul U (Fin 24) := isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
      intro u a ha
      by_contra hu
      have he := fixed_free_involution x hx hfree u.val (ho u hu) (hc u)
      have hm : a ∈ fixedPoints u.val := (mem_fixedPoints _ _).mpr ha
      rw [he] at hm
      exact Finset.notMem_empty _ hm)
    have hd := free_card_dvd (U := U) (X := Fin 24)
    rw [hU, Nat.card_fin] at hd
    exact (by decide : ¬16 ∣ 24) hd
  · let f : U →* Equiv.Perm (fixedPoints x) := {
      toFun u := restricted u.val x (hc u).symm
      map_one' := by ext a; rfl
      map_mul' u v := by ext a; rfl }
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro u hu
      change u = 1
      by_contra hne
      apply six_fixed_faithful_involution x hx hfix u.val (ho u hne) (hc u)
      intro a ha
      have he := Equiv.congr_fun (MonoidHom.mem_ker.mp hu) ⟨a,ha⟩
      exact (mem_fixedPoints _ _).mpr (congrArg Subtype.val he)
    let e : (fixedPoints x) ≃ Fin 6 :=
      Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hfix)
    let j : U →* Equiv.Perm (Fin 6) := (Equiv.permCongrHom e).toMonoidHom.comp f
    have hj : Function.Injective j := (Equiv.permCongrHom e).injective.comp hf
    let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
    have hb := (primeRank_le_iff_elementary_card_le (Equiv.Perm (Fin 6))).mp
      BinaryNaturalDual.FiveActors.ModuleGeometry.symmetric_six_rank_le_three
      j.range inferInstance
    have he : Nat.card j.range = 16 :=
      (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hU
    rw [he] at hb
    norm_num at hb

end
end Sporadic.Mathieu.M24CubicElementary
