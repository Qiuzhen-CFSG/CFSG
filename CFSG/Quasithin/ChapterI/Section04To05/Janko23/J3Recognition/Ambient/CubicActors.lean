module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneNatural
public import Theory.SpecificGroups.Janko3.SourceRecognition.InvolutoryCubic
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingAction
public import Theory.SpecificGroups.MinusExtraspecial.CubicNorm
import all Theory.SpecificGroups.MinusExtraspecial.CubicNorm

/-!
# Involutory and order-eight actors in the actual cubic normalizer

An elementary plane contains an involution outside the original
extraspecial core. Its nontrivial image in A₅ constructs an involutory
cubic inverter; Sylow conjugacy retains the chosen cubic. In its standard
core coordinates the existing even-inverter norm certificate supplies a
fixed core element q with norm of order four. Thus qr has order eight.
Ambient involution fusion transports both actors to the normalizer of
any original cubic centralizing an involution.

The intentional internal import of `CubicNorm` reuses its normalized
finite certificate. The public A₅-action theorem there assumes an A₅
complement; here the actual quotient action establishes the same parity
and support premises directly. No such complement is assumed or asserted.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), Lemma 2.4,
p.495, the involutory inverter and exclusion of the symmetric-six case;
Aschbacher, *Sporadic Groups* (1994), 47.3, p.262, for the norm argument.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient
open LocalSixteen
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

theorem outside_involution_of_returning_pair (P : ReturningPair D) :
    ∃ t : involutionCentralizer D.z, orderOf t = 2 ∧ t ∉ localCore D.z := by
  obtain ⟨eR⟩ := Geometry.Coordinates.rootEquiv P
  obtain ⟨t,ht,htQ⟩ := SetLike.not_le_iff_exists.mp (P.A₁_not_le_core eR)
  have ht1 : t ≠ 1 := fun hh => htQ (hh ▸ one_mem _)
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  let u : involutionCentralizer D.z :=
    ⟨t,(P.R_le_double_centralizer (P.A₁_le_R eR ht)).1⟩
  exact ⟨u,(orderOf_coe u).symm.trans (orderOf_eq_prime ht2 ht1),
    fun hu => htQ (mem_map_of_mem _ hu)⟩

theorem cubic_local_involutory_inverter (P : ReturningPair D)
    (s : involutionCentralizer D.z) (hs : orderOf s = 3) :
    ∃ r : involutionCentralizer D.z, orderOf r = 2 ∧ r * s * r⁻¹ = s⁻¹ := by
  obtain ⟨t,ht,htQ⟩ := outside_involution_of_returning_pair P
  let e := D.localType.quotient_equiv.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (localCore D.z))
  apply Sporadic.Janko3.SourceRecognition.InvolutoryCubic.inverter_of_alternating_quotient D.localType.centralizer_card q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) t ht ?_ s hs
  intro hh
  apply htQ
  exact (QuotientGroup.eq_one_iff t).mp ((e.map_eq_one_iff).mp hh)

private theorem order_eight_of_square {H : Type*} [Group H] [Finite H]
    (s : H) (hs : orderOf (s ^ 2) = 4) : orderOf s = 8 := by
  have hg := (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right (orderOf s) 2)
  rw [orderOf_pow] at hs
  rcases hg with hg | hg
  · rw [hg, Nat.div_one] at hs
    norm_num [hs] at hg
  · rw [hg] at hs
    have hd := Nat.gcd_dvd_left (orderOf s) 2
    rw [hg] at hd
    omega

theorem cubic_local_eight (P : ReturningPair D)
    (s : involutionCentralizer D.z) (hs : orderOf s = 3) :
    ∃ x : normalizer (zpowers s : Set (involutionCentralizer D.z)), orderOf x = 8 := by
  obtain ⟨r,hr,hri⟩ := cubic_local_involutory_inverter P s hs
  obtain ⟨e,he⟩ := cubic_core_coordinates D.localType s hs
  let H := involutionCentralizer D.z
  let Q := localCore D.z
  let f := MinusExtraspecial.AlternatingAction.coreAction Q e
  have hfs : f s = MinusExtraspecial.CubicAction.cycle := by
    apply MulEquiv.ext
    intro x
    obtain ⟨q,rfl⟩ := e.surjective x
    exact (MinusExtraspecial.AlternatingAction.coreAction_apply Q e s q).trans (he q)
  have hqr : r ∉ Q := by
    let q := QuotientGroup.mk' Q
    have hqs1 : q s ≠ 1 := by
      intro hh
      have hd := Q.orderOf_dvd_natCard ((QuotientGroup.eq_one_iff s).mp hh)
      rw [D.localType.core_card,hs] at hd
      norm_num at hd
    have hqs3 : orderOf (q s) = 3 := orderOf_eq_prime
      (by rw [← map_pow,← hs,pow_orderOf_eq_one,map_one]) hqs1
    intro hh
    have hqr : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hh
    have hi := congrArg q hri
    simp only [map_mul,map_inv,hqr,one_mul,inv_one,mul_one] at hi
    have hp : (q s)^2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hi]
      exact inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hp
    norm_num [hqs3] at hd
  obtain ⟨d,hd⟩ := MinusExtraspecial.AlternatingAction.exists_quotient_marking Q e
    (Theory.GroupTheory.centralizer_generalizedFitting_le H) D.localType.quotient_equiv.some
  have ha2 : orderOf (d (QuotientGroup.mk' Q r)) = 2 := by
    rw [d.orderOf_eq]
    apply orderOf_eq_prime
    · rw [← map_pow,← hr,pow_orderOf_eq_one,map_one]
    · exact fun hh => hqr ((QuotientGroup.eq_one_iff r).mp hh)
  have hm : (MinusExtraspecial.FixedFourCalculation.Outside.fivePointAction (f r)).support.card = 4 := by
    rw [← hd]
    rw [← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) _ ha2]
    rfl
  have hf2 : f r ^ 2 = 1 := by rw [← map_pow,← hr,pow_orderOf_eq_one,map_one]
  have hi : f r * MinusExtraspecial.CubicAction.cycle =
      MinusExtraspecial.CubicAction.cycle ^ 2 * f r := by
    have hh := congrArg f hri
    simp only [map_mul,map_inv,hfs] at hh
    have hc : MinusExtraspecial.CubicAction.cycle⁻¹ = MinusExtraspecial.CubicAction.cycle^2 :=
      inv_eq_of_mul_eq_one_right (by
        simpa only [← pow_succ'] using MinusExtraspecial.CubicAction.cycle_cube)
    rw [hc] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨q,hq,hqn⟩ := MinusExtraspecial.FixedFourCalculation.CubicNorm.normalized (f r) hf2 hm hi
  let v : Q := e.symm q
  have hv : MulAut.conjNormal s v = v := by
    apply e.injective
    rw [he,e.apply_symm_apply,hq]
  have hn : orderOf (v * MulAut.conjNormal r v) = 4 := by
    rw [← e.orderOf_eq,map_mul]
    rw [← MinusExtraspecial.AlternatingAction.coreAction_apply Q e r v]
    simpa only [v,e.apply_symm_apply] using hqn
  let x : H := (v : H) * r
  have hr2 : r*r=1 := by
    have hh : r^2=1 := hr ▸ pow_orderOf_eq_one r
    simpa only [pow_two] using hh
  have hxsq : x^2 = ((v * MulAut.conjNormal r v : Q) : H) := by
    change ((v:H)*r)^2 = (v:H)*(r*(v:H)*r⁻¹)
    rw [inv_eq_of_mul_eq_one_left hr2,pow_two]
    simp only [mul_assoc]
  have hx8 : orderOf x = 8 := by
    apply order_eight_of_square
    rw [hxsq,orderOf_coe,hn]
  have hvc : (v:H)*s=s*(v:H) := by
    have hh := congrArg Subtype.val hv
    change s*(v:H)*s⁻¹=(v:H) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hxi : x*s*x⁻¹=s⁻¹ := by
    calc
      x*s*x⁻¹=(v:H)*(r*s*r⁻¹)*(v:H)⁻¹ := by dsimp only [x]; group
      _=(v:H)*s⁻¹*(v:H)⁻¹ := by rw [hri]
      _=s⁻¹ := by rw [(show Commute (v:H) s from hvc).inv_right.eq,mul_inv_cancel_right]
  have hxN : x ∈ normalizer (zpowers s : Set H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (x*s*x⁻¹)=zpowers s
    rw [hxi,zpowers_inv]
  exact ⟨⟨x,hxN⟩,(orderOf_coe _).symm.trans hx8⟩

theorem cubic_involutory_inverter (P : ReturningPair D) (hc : OneInvolutionClass G)
    (s t : G) (hs : orderOf s = 3) (ht : orderOf t = 2) (hst : Commute s t) :
    ∃ r : normalizer (zpowers s : Set G),
      orderOf r = 2 ∧ (r : G) * s * (r : G)⁻¹ = s⁻¹ := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj D.localType.involution ht)
  let e := MulAut.conj g
  have het : e t = D.z := hg
  let H := involutionCentralizer D.z
  let u : H := ⟨e s, mem_centralizer_singleton_iff.mpr (by
    rw [← het, ← map_mul, ← map_mul, hst.eq])⟩
  have hu : orderOf u = 3 := (orderOf_coe u).symm.trans ((e.orderOf_eq s).trans hs)
  obtain ⟨a,ha,hai⟩ := cubic_local_involutory_inverter P u hu
  let r : G := e.symm a
  have hr2 : orderOf r = 2 := (e.symm.orderOf_eq _).trans ((orderOf_coe a).trans ha)
  have hi : r * s * r⁻¹ = s⁻¹ := by
    apply e.injective
    change e (e.symm (a : G) * s * (e.symm (a : G))⁻¹) = e (s⁻¹)
    rw [map_mul,map_mul,map_inv,map_inv,e.apply_symm_apply]
    exact congrArg Subtype.val hai
  have hn : r ∈ normalizer (zpowers s : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (r * s * r⁻¹) = zpowers s
    rw [hi,zpowers_inv]
  exact ⟨⟨r,hn⟩,(orderOf_coe _).symm.trans hr2,hi⟩

theorem cubic_normalizer_eight (P : ReturningPair D) (hc : OneInvolutionClass G)
    (s t : G) (hs : orderOf s = 3) (ht : orderOf t = 2) (hst : Commute s t) :
    ∃ x : normalizer (zpowers s : Set G), orderOf x = 8 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj D.localType.involution ht)
  let e := MulAut.conj g
  have het : e t = D.z := hg
  let H := involutionCentralizer D.z
  let u : H := ⟨e s, mem_centralizer_singleton_iff.mpr (by
    rw [← het, ← map_mul, ← map_mul, hst.eq])⟩
  have hu : orderOf u = 3 := (orderOf_coe u).symm.trans ((e.orderOf_eq s).trans hs)
  obtain ⟨a,ha⟩ := cubic_local_eight P u hu
  let j : H →* G := e.symm.toMonoidHom.comp H.subtype
  have hj : Function.Injective j := e.symm.injective.comp H.subtype_injective
  have hju : j u = s := e.symm_apply_apply s
  have hm : (zpowers u).map j = zpowers s := by rw [MonoidHom.map_zpowers,hju]
  have hn : j a ∈ normalizer (zpowers s : Set G) := by
    rw [← hm]
    exact (zpowers u).le_normalizer_map j (mem_map_of_mem j a.property)
  exact ⟨⟨j a,hn⟩,(orderOf_coe _).symm.trans
    ((orderOf_injective j hj _).trans ((orderOf_coe a).trans ha))⟩
end CFSG.Quasithin.Janko23.J3Recognition.Ambient



