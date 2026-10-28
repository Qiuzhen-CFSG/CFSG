module
public import Theory.GroupTheory.PGroup.FrattiniActionImage
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect actions detected on the Frattini quotient

A perfect group acting on a finite p-group acts trivially if it fixes the
Frattini quotient. Burnside's basis-kernel theorem makes the action image
a p-group, while perfectness makes that image trivial. The statement keeps
the original ambient subgroups and their conjugation action.

Application: the alternating-five branch of Aschbacher--Smith 4.3.8--10,
printed pp.616--617, as used in 5.1.7(1), pp.633--634.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative

theorem Subgroup.commutator_eq_bot_of_le_frattini_of_perfect
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (Q L : Subgroup G)
    (hQ : IsPGroup p Q) [Group.IsPerfect L]
    (hn : L ≤ normalizer (Q : Set G))
    (hc : ⁅Q,L⁆ ≤ (frattini Q).map Q.subtype) : ⁅Q,L⁆ = ⊥ := by
  let := conjMulDistribMulActionOfLeNormalizer L Q hn
  let a := MulDistribMulAction.toMulAut L Q
  have hfix : (quotientAut (frattini Q)).comp a = 1 := by
    ext s y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) y
    change quotientAut (frattini Q) (a s) (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ x
    rw [quotientAut_apply_mk]
    have hh : ⁅(s : G),(x : G)⁆ ∈ (frattini Q).map Q.subtype := by
      apply hc
      rw [commutator_comm Q L]
      exact commutator_mem_commutator s.property x.property
    obtain ⟨z,hz,he⟩ := hh
    have hz' : z = a s x * x⁻¹ := Subtype.ext he
    have hq : QuotientGroup.mk' (frattini Q) (a s x * x⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hz' ▸ hz)
    rw [map_mul,map_inv] at hq
    exact mul_inv_eq_one.mp hq
  have hp : IsPGroup p a.range := MonoidHom.isPGroup_range_of_frattini_range hQ a
    (by rw [hfix]; exact IsPGroup.of_card (n := 0) (by simp))
  let : Group.IsPerfect a.range := Group.IsPerfect.ofSurjective
    a.rangeRestrict_surjective
  have ha : a = 1 := by
    apply MonoidHom.range_eq_bot_iff.mp
    by_contra hb
    let : Nontrivial a.range := a.range.nontrivial_iff_ne_bot.mpr hb
    exact Group.IsPerfect.not_isNilpotent a.range hp.isNilpotent
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx s hs
  have he := congrArg Subtype.val
    (DFunLike.congr_fun (DFunLike.congr_fun ha (⟨s,hs⟩ : L)) (⟨x,hx⟩ : Q))
  change s*x*s⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

