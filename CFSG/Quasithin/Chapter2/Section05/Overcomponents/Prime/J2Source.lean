module
public import CFSG.Quasithin.Chapter2.Section05.J2CoverSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.J2Fusion

/-! The original nonfusion removes the double J₂ cover.  Outer involution
fusion in J₂ then gives fusion of t with t times every fixed involution.
Source: Aschbacher–Smith 2.5.19(4), printed pp.561–562. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]

theorem j2_center_eq_bot_of_nonfusion
    (E : Subgroup G) [Group.IsPerfect E]
    (e : (E ⧸ center E) ≃* Sporadic.LeechRelated.J2.Carrier)
    (t i : G) (htN : t ∈ normalizer (E : Set G))
    (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hcenter : (center E).map E.subtype ≤ zpowers i)
    (hout : ¬ ∃ y : Sporadic.LeechRelated.J2.Carrier,
      MulAut.centralQuotientAction e (E.normalizerMonoidHom ⟨t,htN⟩) = MulAut.conj y)
    (hnot : ¬ IsConj t (t * i)) : center E = ⊥ := by
  let Z := (center E).map E.subtype
  let V := zpowers i
  have hv : Nat.card V = 2 := by rw [Nat.card_zpowers,hi]
  let : Fact (Nat.card V).Prime := ⟨by rw [hv]; decide⟩
  rcases (Z.subgroupOf V).eq_bot_or_eq_top_of_prime_card with hb | hh
  · have he := congrArg (Subgroup.map V.subtype) hb
    rw [map_subgroupOf_eq_of_le hcenter,Subgroup.map_bot] at he
    exact (map_eq_bot_iff_of_injective _ E.subtype_injective).mp he
  · have he : (center E).map E.subtype = zpowers i :=
      le_antisymm hcenter (subgroupOf_eq_top.mp hh)
    exact (J2CoverSource.false_of_outer_double_cover_of_not_isConj E e t i htN ht hi
      he hout hnot).elim

/-- Once the source nonfusion removes the central cover, the literal outer
action fuses t with its product by any fixed involution of the component. -/
theorem j2_quotient_fixed_involution_ambient_fusion
    (E : Subgroup G) [Group.IsPerfect E]
    (e : (E ⧸ center E) ≃* Sporadic.LeechRelated.J2.Carrier)
    (t i : G) (htN : t ∈ normalizer (E : Set G))
    (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hcenter : (center E).map E.subtype ≤ zpowers i)
    (hout : ¬ ∃ y : Sporadic.LeechRelated.J2.Carrier,
      MulAut.centralQuotientAction e (E.normalizerMonoidHom ⟨t,htN⟩) = MulAut.conj y)
    (hnot : ¬ IsConj t (t * i))
    (x : E) (hx : E.normalizerMonoidHom ⟨t,htN⟩ x = x) (hx2 : x ^ 2 = 1) :
    IsConj t (t * (x : G)) := by
  have hz := j2_center_eq_bot_of_nonfusion E e t i htN ht hi hcenter hout hnot
  let q : E ≃* E ⧸ center E :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
  let d := q.trans e
  let a := E.normalizerMonoidHom ⟨t,htN⟩
  have hao : ¬ ∃ y : E, a = MulAut.conj y := by
    intro h
    exact hout ((MulAut.centralQuotientAction_inner_iff e a).mpr h)
  have ha : orderOf a = 2 := by
    apply orderOf_eq_prime
    · change E.normalizerMonoidHom ⟨t,htN⟩ ^ 2 = 1
      rw [←map_pow]
      have he : (⟨t,htN⟩ : normalizer (E : Set G)) ^ 2 = 1 :=
        Subtype.ext (ht ▸ pow_orderOf_eq_one t)
      rw [he,map_one]
    · intro he
      exact hao ⟨1,by simpa using he⟩
  let b := MulAut.congr d a
  have hb : orderOf b = 2 := ((MulAut.congr d).orderOf_eq a).trans ha
  have hbo : ¬ ∃ y, b = MulAut.conj y := fun h => hao ((MulAut.congr_inner_iff d a).mp h)
  have hdx : b (d x) = d x := by
    change d (a (d.symm (d x))) = d x
    rw [d.symm_apply_apply,hx]
  obtain ⟨w,hw⟩ := j2_outer_fixed_involution_coboundary b hb hbo (d x) hdx
    (by rw [←map_pow,hx2,map_one])
  let v := d.symm w
  have hv : x = v * (a v)⁻¹ := by
    apply d.injective
    rw [map_mul,map_inv]
    change d x = d (d.symm w) * (d (a (d.symm w)))⁻¹
    rw [d.apply_symm_apply]
    exact hw
  have hact (y : E) : ((a y : E) : G) = t * (y : G) * t⁻¹ := rfl
  have hxt : (x : G) * t = t * x := by
    have he := congrArg (fun y : E => (y : G)) hx
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply isConj_iff.mpr
  refine ⟨(v : G),?_⟩
  rw [←hxt,hv]
  change (v : G) * t * (v : G)⁻¹ = ((v : G) * ((a v : E) : G)⁻¹) * t
  rw [hact]
  group
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
