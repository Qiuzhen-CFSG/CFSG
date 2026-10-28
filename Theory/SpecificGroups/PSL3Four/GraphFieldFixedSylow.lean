module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless.Order
public import Theory.SpecificGroups.PSL3Four.GraphFieldFixedSylow.CentralInvolutions

/-!
# Graph-field fixed Sylow subgroups of PSL₃(4)

For every graph-field-invariant Sylow two-subgroup S, its intersection with
the actual graph-field fixed group is Sylow in that fixed group.

An involutory automorphism of a nontrivial finite two-group fixes a central
involution: start with a central involution z, and use z times its image if
z itself is not fixed. In PSL₃(4), the ambient centralizer of this central
involution is exactly S. The graph-field fixed group has order 72 and a
concrete quaternion subgroup of order eight. Hence all its Sylow two-subgroups
are quaternion. A Sylow containing the fixed involution centralizes it, lies
in S, and proves maximality of the intersection with the original S.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the graph-field
branch of the proof of 16.4.9(2), printed p.1191. The automorphism is the actual
inverse-transpose times Frobenius on the matrix quotient, and no Sylow
placement or fixed-point saturation premise is used.
-/

public section

open Subgroup Matrix.PSL3Four
namespace Matrix.PSL3Four.GraphFieldFixedSylow
noncomputable section
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem fixed_central_involution {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hp : IsPGroup 2 P) (a : MulAut P) (ha : a ^ 2 = 1) :
    ∃ z : P, z ∈ center P ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ a z = z := by
  let : Nontrivial (center P) := hp.center_nontrivial
  have h2 : 2 ∣ Nat.card (center P) :=
    (hp.to_subgroup (center P)).card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card (α := center P)))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : (z : P) ^ 2 = 1 := congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  have hz1 : (z : P) ≠ 1 := by
    intro h
    have he : z = 1 := Subtype.ext h
    simp [he] at hz
  have haa (x : P) : a (a x) = x := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
      congrArg (fun b : MulAut P => b x) ha
  by_cases hfix : a (z : P) = z
  · exact ⟨z, z.property, hz1, hz2, hfix⟩
  have hac : a (z : P) ∈ center P := (centerCongr a z).property
  have hcomm : Commute (z : P) (a z) := (mem_center_iff.mp z.property _).symm
  refine ⟨(z : P) * a z, (center P).mul_mem z.property hac, ?_, ?_, ?_⟩
  · intro he
    apply hfix
    calc
      a (z : P) = (z : P) * ((z : P) * a z) := by rw [← mul_assoc, ← pow_two, hz2, one_mul]
      _ = z := by rw [he, mul_one]
  · rw [hcomm.mul_pow, hz2, ← map_pow, hz2, map_one, mul_one]
  · rw [map_mul, haa, hcomm.eq]

open InnerFamilyNormalizer.Centerless ExtendedCentralizer.ProjectiveFixer

private def quaternionSylow : Sylow 2 graphField.fixedSubgroup :=
  Sylow.ofCard (quaternion.subgroupOf graphField.fixedSubgroup) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe quaternion_le_fixed).toEquiv,
      quaternion_card, fixed_card]
    decide +kernel)

private theorem sylow_involutions_central (P : Sylow 2 graphField.fixedSubgroup)
    (z : P) (hz : z ^ 2 = 1) : z ∈ center P := by
  obtain ⟨eQ⟩ := quaternion_equiv
  let e : P ≃* QuaternionGroup 2 :=
    (P.equiv quaternionSylow).trans
      ((subgroupOfEquivOfLe quaternion_le_fixed).trans eQ)
  have he : (e z) ^ 2 = 1 := by rw [← map_pow, hz, map_one]
  have hq : ∀ x y : QuaternionGroup 2, x ^ 2 = 1 → y * x = x * y := by decide +kernel
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul] using hq (e z) (e y) he

/-- Taking graph-field fixed points preserves Sylow maximality for the supplied
invariant Sylow two-subgroup of the genuine PSL₃(4). -/
theorem exists_fixedSylow (S : Sylow 2 PSL)
    (hS : (S : Subgroup PSL).map graphField.toMonoidHom = (S : Subgroup PSL)) :
    ∃ P : Sylow 2 graphField.fixedSubgroup,
      (P : Subgroup graphField.fixedSubgroup).map graphField.fixedSubgroup.subtype =
        (S : Subgroup PSL) ⊓ graphField.fixedSubgroup := by
  let a : MulAut S := (graphField.subgroupMap S).trans (MulEquiv.subgroupCongr hS)
  have ha : a ^ 2 = 1 := by
    ext x
    exact congrArg (fun b : MulAut PSL => b (x : PSL)) graphField_sq
  have hcard : Nat.card S = 64 := by
    rw [← Nat.card_congr (unipotentEquiv.trans (unipotentSylow.equiv S)).toEquiv]
    exact SylowModel.card_U
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨z, hz, hzne, hz2, hza⟩ := fixed_central_involution S.isPGroup' a ha
  let zf : graphField.fixedSubgroup :=
    ⟨z, (MulAut.mem_fixedSubgroup _ _).mpr (congrArg Subtype.val hza)⟩
  have hzf : zf ^ 2 = 1 := Subtype.ext (congrArg (fun w : S => (w : PSL)) hz2)
  have hpz : IsPGroup 2 (zpowers zf) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hzf)
  obtain ⟨P, hP⟩ := hpz.exists_le_sylow
  have hzP : zf ∈ (P : Subgroup graphField.fixedSubgroup) := hP (mem_zpowers zf)
  have hzPc : (⟨zf, hzP⟩ : P) ∈ center P :=
    sylow_involutions_central P _ (Subtype.ext hzf)
  have hle : (P : Subgroup graphField.fixedSubgroup) ≤
      (S : Subgroup PSL).subgroupOf graphField.fixedSubgroup := by
    intro y hy
    have hcomm : (y : PSL) * (z : PSL) = (z : PSL) * (y : PSL) :=
      congrArg (fun w : P => ((w : graphField.fixedSubgroup) : PSL))
        (mem_center_iff.mp hzPc ⟨y, hy⟩)
    have hc := mem_centralizer_singleton_iff.mpr hcomm
    rw [centralizer_of_sylow_center S z hz hzne] at hc
    exact hc
  have he := P.is_maximal' (S.isPGroup'.comap_subtype) hle
  refine ⟨P, ?_⟩
  rw [← he]
  exact subgroupOf_map_subtype _ _

end
end Matrix.PSL3Four.GraphFieldFixedSylow
