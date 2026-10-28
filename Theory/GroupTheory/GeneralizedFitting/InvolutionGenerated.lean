module
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Involution-generated groups with inner socle actions

A faithful action on a normal subgroup identifies inner actors with that
subgroup. If all ambient involution centralizers are two-groups and every
involutory automorphism with a two-group fixed subgroup is inner, every
involution lies in the normal subgroup. Involution generation then removes
all outer extensions. The simple generalized Fitting subgroup supplies the
faithful action; odd outer order is a separate innerness criterion.

Source: Aschbacher--Smith E.2.7, printed p.220, the all-c2 extension step.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A self-centralizing normal subgroup contains an involution-generated
ambient group when its involutory automorphisms with two-group fixed group
are inner. -/
theorem normal_eq_top_of_involution_inner
    (L : Subgroup G) [L.Normal]
    (hC : centralizer (L : Set G) = ⊥)
    (hgen : closure {g : G | g ^ 2 = 1} = ⊤)
    (hc : ∀ t : G, orderOf t = 2 → IsPGroup 2 (centralizer ({t} : Set G)))
    (hi : ∀ a : MulAut L, orderOf a = 2 → IsPGroup 2 a.fixedSubgroup →
      a ∈ MulAut.innerSubgroup L) : L = ⊤ := by
  apply top_unique
  rw [←hgen]
  apply (closure_le _).mpr
  intro t ht
  change t ∈ L
  by_cases ht1 : t = 1
  · simpa only [ht1] using L.one_mem
  have ht2 : orderOf t = 2 := orderOf_eq_prime ht ht1
  let a : MulAut L := MulAut.conjNormal t
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.conjNormal : G →* MulAut L)
      (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC) t).trans ht2
  let f : a.fixedSubgroup →* centralizer ({t} : Set G) := {
    toFun x := ⟨x.val.val, by
      apply mem_centralizer_singleton_iff.mpr
      have hx := congrArg (fun z : L => (z : G))
        ((MulAut.mem_fixedSubgroup a x.val).mp x.property)
      change t * (x.val : G) * t⁻¹ = x.val at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : centralizer ({t} : Set G) => (z : G)) h))
  have hin := hi a ha ((hc t ht2).of_injective f hf)
  change t ∈ (MulAut.innerSubgroup L).comap (MulAut.conjNormal : G →* MulAut L) at hin
  simpa only [MulAut.conjNormal_comap_innerSubgroup, hC, sup_bot_eq] using hin

/-- The previous criterion applies to the actual nonabelian simple socle. -/
theorem generalizedFitting_eq_top_of_involution_inner
    [IsSimpleGroup (generalizedFitting G)] [Group.IsPerfect (generalizedFitting G)]
    (hgen : closure {g : G | g ^ 2 = 1} = ⊤)
    (hc : ∀ t : G, orderOf t = 2 → IsPGroup 2 (centralizer ({t} : Set G)))
    (hi : ∀ a : MulAut (generalizedFitting G), orderOf a = 2 →
      IsPGroup 2 a.fixedSubgroup → a ∈ MulAut.innerSubgroup (generalizedFitting G)) :
    generalizedFitting G = ⊤ :=
  normal_eq_top_of_involution_inner _
    (SimpleSocle.centralizer_eq_bot (Group.IsPerfect.not_isMulCommutative _)) hgen hc hi

/-- Odd order of the actual outer group forces every square-one automorphism
into the inner subgroup. -/
theorem involution_inner_of_odd_outer {L : Type*} [Group L]
    (ho : Odd (Nat.card (MulAut.Outer L))) (a : MulAut L) (ha : a ^ 2 = 1) :
    a ∈ MulAut.innerSubgroup L := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup L)
  apply (QuotientGroup.eq_one_iff a).mp
  change q a = 1
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ho.coprime_two_right
    (orderOf_dvd_natCard (q a))
    (orderOf_dvd_of_pow_eq_one (by rw [←map_pow, ha, map_one]))

omit [Finite G] in
/-- Odd outer order eliminates a faithful involution-generated extension. -/
theorem normal_eq_top_of_odd_outer
    (L : Subgroup G) [L.Normal] (hC : centralizer (L : Set G) = ⊥)
    (hgen : closure {g : G | g ^ 2 = 1} = ⊤)
    (ho : Odd (Nat.card (MulAut.Outer L))) : L = ⊤ := by
  apply top_unique
  rw [←hgen]
  apply (closure_le _).mpr
  intro t ht
  change t ∈ L
  have hin := involution_inner_of_odd_outer ho (MulAut.conjNormal t : MulAut L)
    (by rw [←map_pow,ht,map_one])
  change t ∈ (MulAut.innerSubgroup L).comap (MulAut.conjNormal : G →* MulAut L) at hin
  simpa only [MulAut.conjNormal_comap_innerSubgroup, hC, sup_bot_eq] using hin

end Theory.GroupTheory
