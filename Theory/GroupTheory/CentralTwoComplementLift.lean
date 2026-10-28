module
public import Theory.GroupTheory.CentralCoprimeLift
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Lifting odd cyclic complements through central two-kernels

For a finite surjection with central two-group kernel, an odd cyclic
complement to a normal subgroup of the quotient lifts to an odd cyclic
complement to its full inverse image. The lift has exactly the prescribed
image and the restricted quotient map is an isomorphism onto that image.

Choose a generator of the quotient complement. The coprime-power lifting
lemma produces a lift satisfying the same finite power relation. The cyclic
subgroup it generates maps onto the quotient complement, while its order is
no larger; hence the restriction is bijective. Trivial intersection follows
from the quotient complement and this injectivity. Lifting the quotient
product decomposition proves generation and the actual complement property.

This proves the complement-lifting sentence in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 3 (article page 27). The field-action
identification and centralizer description are separate steps; no such
conclusions enter this lemma as assumptions.
-/

namespace CentralExtension
open Subgroup

/-- Lift an odd cyclic quotient complement through a central two-group kernel. -/
public theorem exists_odd_cyclic_complement_lift
    {H B : Type*} [Group H] [Group B] [Finite H] [Finite B]
    (f : H →* B) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center H) (hker : IsPGroup 2 f.ker)
    (Lbar Ebar : Subgroup B) [Lbar.Normal]
    (hcomp : Lbar.IsComplement' Ebar) (hodd : Odd (Nat.card Ebar))
    (hcyclic : IsCyclic Ebar) :
    ∃ E : Subgroup H, (Lbar.comap f).IsComplement' E ∧ E.map f = Ebar ∧
      IsCyclic E ∧ Odd (Nat.card E) ∧ Nonempty (E ≃* Ebar) := by
  classical
  let : IsCyclic Ebar := hcyclic
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Ebar)
  have hbtop : zpowers b = ⊤ := by ext x; simp [hb x]
  have hbord : orderOf b = Nat.card Ebar := orderOf_eq_card_of_forall_mem_zpowers hb
  have hbpow : (b : B) ^ Nat.card Ebar = 1 := by
    rw [← hbord]
    exact congrArg Subtype.val (pow_orderOf_eq_one b)
  obtain ⟨x, hfx, hxpow⟩ := f.exists_pow_eq_one_lift_of_central_pgroup_ker
    hf hcentral hker hodd.coprime_two_left b hbpow
  let E : Subgroup H := zpowers x
  have hmap : E.map f = Ebar := by
    change (zpowers x).map f = Ebar
    rw [MonoidHom.map_zpowers, hfx]
    have hm := congrArg (Subgroup.map Ebar.subtype) hbtop
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype,
      Subgroup.coe_subtype] using hm
  let r : E →* Ebar := (f.comp E.subtype).codRestrict Ebar
    (fun y => hmap ▸ mem_map_of_mem f y.property)
  have hr : Function.Surjective r := by
    intro y
    have hy : (y : B) ∈ E.map f := by rw [hmap]; exact y.property
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hEcard : Nat.card E ≤ Nat.card Ebar := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd Nat.card_pos (orderOf_dvd_of_pow_eq_one hxpow)
  let e : E ≃* Ebar := MulEquiv.ofBijective r (hr.bijective_of_nat_card_le hEcard)
  have hinj : Function.Injective r := e.injective
  have hdis : Disjoint (Lbar.comap f) E := by
    apply disjoint_def.mpr
    intro y hyL hyE
    have hyf : f y = 1 := disjoint_def.mp hcomp.disjoint hyL (hmap ▸ mem_map_of_mem f hyE)
    have hyr : r ⟨y, hyE⟩ = 1 := Subtype.ext hyf
    exact congrArg Subtype.val (hinj (hyr.trans r.map_one.symm))
  have hc : (Lbar.comap f).IsComplement' E := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdis, ?_⟩
    intro y
    obtain ⟨⟨l, b'⟩, hlb⟩ := hcomp.2 (f y)
    obtain ⟨z, hz⟩ := hr b'
    have hzval : f z = (b' : B) := congrArg Subtype.val hz
    have hly : y * (z : H)⁻¹ ∈ Lbar.comap f := by
      change f (y * (z : H)⁻¹) ∈ Lbar
      rw [map_mul, map_inv, hzval, ← hlb, mul_inv_cancel_right]
      exact l.property
    exact ⟨⟨⟨y * (z : H)⁻¹, hly⟩, z⟩, inv_mul_cancel_right _ _⟩
  exact ⟨E, hc, hmap, inferInstance, (Nat.card_congr e.toEquiv).symm ▸ hodd, ⟨e⟩⟩

end CentralExtension

