module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors
public import Theory.GroupTheory.QuaternionCentralProductInvertingCubics
public import Theory.GroupTheory.QuaternionCubicInverterExtension

/-!
# The quaternion–cubic complement of order forty-eight

Two independent cubic actors on commuting quaternion factors determine
an actual SL₂(3) subgroup. A simultaneous inverter whose square is the
central involution extends this subgroup to order48. The other cubic
axis is disjoint from the extension: adjoining it would give order72.
All subgroups and conjugation actions remain on the original carrier.

Source: Aschbacher, Sporadic Groups (1994),45.8,printed pp245–246.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem cubic_disjoint_of_not_le (W J : Subgroup G) (hW : Nat.card W = 3)
    (hne : ¬W ≤ J) : Disjoint W J := by
  have hd : Nat.card (W ⊓ J : Subgroup G) ∣ 3 := hW ▸ card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hi | hi
  · exact disjoint_iff.mpr (Subgroup.card_eq_one.mp hi)
  · exact (hne ((eq_of_le_of_card_ge (show W ⊓ J ≤ W from inf_le_left)
      (by rw [hW, hi])).symm.le.trans inf_le_right)).elim

private theorem double_extension_card (J : Subgroup G) (hj : Nat.card J = 24)
    (z r : G) (hz : orderOf z = 2) (hzJ : z ∈ J) (hr2 : r^2=z)
    (hr : r ∈ normalizer (J:Set G)) (hout : r ∉ J) :
    Nat.card (J ⊔ zpowers r : Subgroup G) = 48 := by
  have hz2 : z^2=1 := hz ▸ pow_orderOf_eq_one z
  have hr4 : r^4=1 := by rw [show 4=2*2 from rfl,pow_mul,hr2,hz2]
  have hro : orderOf r=4 := orderOf_eq_prime_pow (p:=2) (n:=1)
    (by simpa only [pow_one,hr2,orderOf_eq_one_iff] using
      (show z≠1 from fun hh=>by simp [hh] at hz)) hr4
  have hZle : zpowers z ≤ J ⊓ zpowers r := zpowers_le.mpr ⟨hzJ,
    hr2 ▸ (zpowers r).pow_mem (mem_zpowers r) 2⟩
  have hlo : 2 ≤ Nat.card (J ⊓ zpowers r : Subgroup G) := by
    simpa only [Nat.card_zpowers,hz] using Nat.card_le_card_of_injective (inclusion hZle) (inclusion_injective hZle)
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes J (zpowers r)
    (zpowers_le.mpr hr)
  rw [hj,Nat.card_zpowers,hro] at he
  have hup : Nat.card (J ⊔ zpowers r : Subgroup G) ≤ 48 := by nlinarith
  let K := J ⊔ zpowers r
  have hnot : J.subgroupOf K ≠ ⊤ := by
    intro hh
    exact hout (show (⟨r,mem_sup_right (mem_zpowers r)⟩:K)∈J.subgroupOf K from hh ▸ mem_top _)
  have hind := one_lt_index_of_ne_top hnot
  have hc := (J.subgroupOf K).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show J≤K from le_sup_left)).toEquiv,hj] at hc
  change Nat.card K=48
  change Nat.card K≤48 at hup
  omega

/-- The original independent cubic axes give an SL₂(3) subgroup and its
order48 extension by a simultaneous inverter. The other cubic axis is
actually disjoint from this extension. -/
public theorem QuaternionIndependentCubics.complement_of_inverter
    {B C : Subgroup G} (d : QuaternionIndependentCubics B C)
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hcomm : ∀b∈B,∀c∈C,b*c=c*b)
    (z r:G) (hz:orderOf z=2) (hzC:z∈C)
    (hrC:r∈normalizer (C:Set G)) (hr2:r^2=z)
    (hinv:∀x∈d.A,r*x*r⁻¹=x⁻¹) :
    let W := zpowers (d.x:G)
    let J := C ⊔ zpowers (d.y:G)
    let K := J ⊔ zpowers r
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    Nat.card J=24 ∧ Nat.card K=48 ∧ Disjoint W K ∧
    K≤normalizer (W:Set G) ∧ r∈normalizer (J:Set G) := by
  let W := zpowers (d.x:G)
  let J := C ⊔ zpowers (d.y:G)
  let K := J ⊔ zpowers r
  have hC8 : Nat.card C=8 := by
    rw [Nat.card_congr hC.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hY3 : Nat.card (zpowers (d.y:G))=3 := by rw [Nat.card_zpowers,d.y_order]
  have hW3 : Nat.card W=3 := by rw [Nat.card_zpowers,d.x_order]
  have hJ24 : Nat.card J=24 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C (zpowers (d.y:G))
      (zpowers_le.mpr (d.normalizes_right d.y.property))
      (disjoint_of_coprime_natCard (by rw [hC8,hY3];decide)),hC8,hY3]
  have hm := (quaternion_cubic_extension_recognition C hC (d.y:G) d.y_order
    (d.actionC d.y) (d.actionC_apply d.y) d.y_actionC_ne_one).1
  have hJB : J ≤ centralizer (B:Set G) := sup_le
    (fun c hc b hb=>hcomm b hb c hc) (zpowers_le.mpr d.y_centralizes)
  have hxB : (d.x:G)∉centralizer (B:Set G) := by
    intro hh
    apply d.x_actionB_ne_one
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [d.actionB_apply]
    change (d.x:G)*(b:G)*(d.x:G)⁻¹=(b:G)
    rw [←hh b b.property,mul_inv_cancel_right]
  have hdisJ : Disjoint W J := cubic_disjoint_of_not_le W J hW3
    (fun hh=>hxB (hJB (hh (mem_zpowers _))))
  have hJW : J ≤ centralizer (W:Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp (zpowers_le.mpr d.x_centralizes)
    · rw [le_centralizer_iff,zpowers_le]
      intro y hy
      exact mem_centralizer_singleton_iff.mp
        ((zpowers_le.mpr (mem_centralizer_singleton_iff.mpr d.commute.symm.eq)) hy)
  have hrY : (zpowers (d.y:G)).map (MulAut.conj r).toMonoidHom=zpowers (d.y:G) := by
    rw [MonoidHom.map_zpowers]
    change zpowers (r*(d.y:G)*r⁻¹)=zpowers (d.y:G)
    rw [hinv d.y d.y.property,zpowers_inv]
  have hrJ : r∈normalizer (J:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_sup,mem_normalizer_iff_map_conj_eq.mp hrC]
    change C ⊔ (zpowers (d.y:G)).map (MulAut.conj r).toMonoidHom = J
    rw [hrY]
  have hrout : r∉J := by
    intro hh
    have hc : (d.x:G)*r=r*(d.x:G) := hJW hh _ (mem_zpowers _)
    have hi := hinv d.x d.x.property
    rw [←hc,mul_inv_cancel_right] at hi
    have hx2 : (d.x:G)^2=1 := by rw [pow_two]; calc
      (d.x:G)*(d.x:G) = (d.x:G)*(d.x:G)⁻¹ := congrArg ((d.x:G)*·) hi
      _ = 1 := mul_inv_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [d.x_order] at hd
    norm_num at hd
  have hK48 : Nat.card K=48 := double_extension_card J hJ24 z r hz (mem_sup_left hzC) hr2 hrJ hrout
  have hdisK : Disjoint W K := cubic_disjoint_of_not_le W K hW3 (by
    intro hh
    have hprod : Nat.card (W ⊔ J : Subgroup G)=72 := by
      rw [card_sup_eq_mul_of_normalizes_of_disjoint W J
        (hJW.trans (centralizer_le_normalizer _)) hdisJ,hW3,hJ24]
    have hinc : W⊔J≤K := sup_le hh le_sup_left
    have hle := Nat.card_le_card_of_injective (inclusion hinc) (inclusion_injective hinc)
    rw [hprod,hK48] at hle
    omega)
  refine ⟨hm,hJ24,hK48,hdisK,sup_le (hJW.trans (centralizer_le_normalizer _)) ?_,hrJ⟩
  apply zpowers_le.mpr
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers (r*(d.x:G)*r⁻¹)=zpowers (d.x:G)
  rw [hinv d.x d.x.property,zpowers_inv]
end Subgroup
