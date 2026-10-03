module
public import Stellmacher.SectionEight.EightSixCostFourInitialResidualModule
public import Stellmacher.SectionEight.EightSixCostFourOrbitENormalizer
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The native A4 witnesses in the cost-four normalizer action

Retain the original selected cost-four configuration. For the actual module
W=[closure_E Za,Ea], the faithful image of its ambient normalizer contains
a nonidentity involution r and a fixed-point-free cubic t satisfying the
A4 relations. The actual initial plane Za, restricted to W, has order four
and is fixed pointwise by r, while an actual E-element moves this plane.
The elementary order-sixteen module and this entire packet feed the finite
A4 plane obstruction to solvability.

Choose r from the neighboring subgroup B of order sixteen outside its
centralizer U of order eight. The existing Q/Za elementary quotient kills
squares and commutators in the action on W. A generator of the actual
initial three-Sylow is fixed-point-free on the normal initial pair R.
Mathlib's fixed-point-free norm theorem gives the literal cubic norm in R;
applying the same conjugation homomorphism gives the A4 norm relation.
Finally E normalizes W, but cannot normalize Za because its actual closure
of Za is U, of larger order.

This proves the native action input for Stellmacher (8.6)(b3), Journal of
Algebra 190 (1997), printed p.44. The two printed symmetric-group image
assertions are not used. No coordinate action or replacement quotient is
assumed, and all witnesses lie in W.normalizerMonoidHom.range.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative commutatorElement
universe u
public theorem eight_six_cost_four_native_a4_witness
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a  → 
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep  → 
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    let U := conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E
    let W := ⁅U,EAt ctx.Γ ctx.criticalPath.a⁆
    let C := (ZAt ctx.Γ ctx.criticalPath.a).subgroupOf W
    let X := W.normalizerMonoidHom.range
    IsElementaryAbelianSubgroup 2 W ∧ Nat.card W=16 ∧ Nat.card C=4 ∧
      ∃ r t:MulAut W, r∈X ∧ t∈X ∧ r≠1 ∧ r^2=1 ∧ t^3=1 ∧
        (∀ w:W,t w=w → w=1) ∧ Commute r (t*r*t⁻¹) ∧
        r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1 ∧
        (∀ c:W,c∈C → r c=c) ∧ ∃ g:MulAut W,g∈X ∧ C.map g.toMonoidHom≠C := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Γ:=ctx.Γ
  let cp:=ctx.criticalPath
  let P:=GAt Γ cp.a
  let F:=EAt Γ cp.a
  let Za:=ZAt Γ cp.a
  let U:=conjugateClosure Za E
  let W:=⁅U,F⁆
  let R:=(VAt Γ previous⊓QAt Γ cp.a)⊔(VAt Γ cp.firstStep⊓QAt Γ cp.a)
  let B:=VAt Γ cp.firstStep⊓QAt Γ cp.a
  let C:=Za.subgroupOf W
  let X:=W.normalizerMonoidHom.range
  obtain ⟨helem,hWcard,hUW,hWR,hQN,hFN,_⟩:=
    eight_six_cost_four_initial_residual_module ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  let _ : IsElementaryAbelian 2 W := helem
  have hRQ : R≤Q:=data.core_generation ▸ le_sup_left
  have hWQ : W≤Q:=hWR.trans hRQ
  have hUcomm : ⁅U,W⁆=⊥:=by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact setLike_mul_comm (s:=W) hw (hUW hu)
  have hEN := eight_six_cost_four_orbit_e_normalizer ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
      W hUW hWQ hUcomm
  have hRN : R≤Subgroup.normalizer (W:Set G):=hRQ.trans hQN
  have hZU : Za≤U:=by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZW : Za≤W:=hZU.trans hUW
  have hZC : Za≤Subgroup.centralizer (Q:Set G):=
    (eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data).2.2.2
  have hUcard : Nat.card U=8:=eight_six_selected_orbit_card_eight
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hBcard : Nat.card B=16:=(eight_six_cost_four_initial_pair_card
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hcost).2.1
  have hBnot : ¬B≤U:=by
    intro hle
    have hh:=Subgroup.card_le_of_le hle
    rw [hBcard,hUcard] at hh
    omega
  obtain ⟨b,hbB,hbU⟩:=SetLike.not_le_iff_exists.mp hBnot
  let bR:R:=⟨b,(show B≤R from le_sup_right) hbB⟩
  let ρ:R →* MulAut W:=W.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  have hρ (a:R) (w:W) : (ρ a w:G)=(a:G)*(w:G)*(a:G)⁻¹:=rfl
  have hkill (a:R) (haZ:(a:G)∈Za) : ρ a=1:=by
    ext w
    rw [hρ]
    change (a:G)*(w:G)*(a:G)⁻¹=(w:G)
    rw [setLike_mul_comm (s:=W) (hZW haZ) w.property,mul_inv_cancel_right]
  have hrne : ρ bR≠1:=by
    intro hr
    have hbC : b∈Subgroup.centralizer (U:Set G):=by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hh:=congrArg (fun a:MulAut W=>(a ⟨u,hUW hu⟩:G)) hr
      change b*u*b⁻¹=u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hfixed : VAt Γ cp.firstStep⊓Subgroup.centralizer (U:Set G)=U:=
      (eight_six_cost_four_module_quaternion ctx hcenter hquot hlength hcard previous D L Q
        hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).2
    exact hbU (hfixed ▸ (show b∈VAt Γ cp.firstStep⊓Subgroup.centralizer (U:Set G) from ⟨hbB.1,hbC⟩))
  obtain ⟨quot,hquotElem⟩:=eight_six_cost_four_central_quotient ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  let _:=quot.groupX
  let _:=quot.finiteX
  let _ : IsElementaryAbelian 2 quot.X:=hquotElem
  let π:R →* quot.X:=quot.projection.comp (Subgroup.inclusion hRQ)
  have hπ (a:R) : π a=1 ↔ (a:G)∈Za:=by
    change quot.projection ⟨(a:G),hRQ a.property⟩=1 ↔ _
    rw [←MonoidHom.mem_ker,quot.kernel_eq]
    rfl
  have hρcomm (a c:R) : Commute (ρ a) (ρ c):=by
    have hzero : π ⁅a,c⁆=1:=by rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm];exact mul_comm _ _
    have hz:=hkill ⁅a,c⁆ ((hπ _).mp hzero)
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hz
    exact hz
  have hr2 : (ρ bR)^2=1:=by
    have hz : π (bR^2)=1:=by rw [map_pow];exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 quot.X) _
    rw [←map_pow]
    exact hkill _ ((hπ _).mp hz)
  have hRnormal:=eight_six_initial_pair_normal ctx hquot hlength previous hprev
  have hPR : P≤Subgroup.normalizer (R:Set G):=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRnormal.1).mp hRnormal.2
  let sylow:Sylow 3 P:=default
  let T:Subgroup G:=(sylow:Subgroup P).map P.subtype
  have hT : IsSylowIn 3 T P:=⟨sylow,rfl⟩
  have hTP : T≤P:=Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T:=sylow.isPGroup'.map P.subtype
  have hTF : T≤F:=by
    change T≤Γ.twoResidualAt cp.a
    rw [Γ.twoResidualAt_def]
    exact eight_six_three_subgroup_le_residual T P hTP hTthree
  have hTcard : Nat.card T=3:=eight_six_initial_three_card ctx hquot T hT
  let _ : IsCyclic T:=isCyclic_of_prime_card hTcard
  obtain ⟨t,htgen⟩:=isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance:IsCyclic T)
  have htorder : orderOf (t:G)=3:=by
    rw [←T.subtype_apply,orderOf_injective T.subtype T.subtype_injective,
      orderOf_eq_card_of_zpowers_eq_top htgen,hTcard]
  have ht3 : (t:G)^3=1:=htorder ▸ pow_orderOf_eq_one (t:G)
  have hgen : Subgroup.zpowers (t:G)=T:=by
    have hh:=congrArg (Subgroup.map T.subtype) htgen
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,Subgroup.range_subtype,Subgroup.subtype_apply] using hh
  have hfixedR : R⊓Subgroup.centralizer (T:Set G)=⊥:=
    eight_six_cost_four_initial_pair_fixed_free ctx hcenter hquot hlength hcard previous D L Q
      hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost T hT
  let tR:MulAut R:=R.normalizerMonoidHom ⟨t,hPR (hTP t.property)⟩
  let tW:Subgroup.normalizer (W:Set G):=⟨t,hFN (hTF t.property)⟩
  let tw:MulAut W:=W.normalizerMonoidHom tW
  have htR3 : tR^3=1:=by
    change (R.normalizerMonoidHom _ )^3=1
    rw [←map_pow]
    exact (congrArg R.normalizerMonoidHom (show (⟨(t:G),hPR (hTP t.property)⟩:Subgroup.normalizer (R:Set G))^3=1 from Subtype.ext ht3)).trans (map_one _)
  have hffR (a:R) (ha:tR a=a) : a=1:=by
    have heq:=congrArg Subtype.val ha
    change (t:G)*(a:G)*(t:G)⁻¹=(a:G) at heq
    have hTc : T≤Subgroup.centralizer ({(a:G)}:Set G):=by
      rw [←hgen]
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp heq
    have hmem : (a:G)∈R⊓Subgroup.centralizer (T:Set G):=by
      refine ⟨a.property,?_⟩
      change (a:G)∈Subgroup.centralizer (T:Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (hTc hs)
    apply Subtype.ext
    change (a:G)=1
    simpa only [hfixedR,Subgroup.mem_bot] using hmem
  have htw3 : tw^3=1:=by
    change (W.normalizerMonoidHom tW)^3=1
    rw [←map_pow]
    have hh : tW^3=1:=Subtype.ext ht3
    rw [hh,map_one]
  have hffW (w:W) (hw:tw w=w) : w=1:=by
    have hh : tR ⟨(w:G),hWR w.property⟩=⟨(w:G),hWR w.property⟩:=
      Subtype.ext (congrArg (fun z:W=>(z:G)) hw)
    exact Subtype.ext (congrArg (fun z:R=>(z:G)) (hffR _ hh))
  have hcov (a:R) : ρ (tR a)=tw*ρ a*tw⁻¹:=by
    change W.normalizerMonoidHom (Subgroup.inclusion hRN (tR a)) =
      W.normalizerMonoidHom tW * W.normalizerMonoidHom (Subgroup.inclusion hRN a) *
        (W.normalizerMonoidHom tW)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
  have hnorm : ρ bR*(tw*ρ bR*tw⁻¹)*((tw^2)*ρ bR*(tw^2)⁻¹)=1:=by
    have hit : (tR:R → R)^[3]=id:=by
      funext a
      have hh:=congrArg (fun f:MulAut R=>f a) htR3
      simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply,
        pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply,Function.id_def] using hh
    have hnR : bR*tR bR*tR (tR bR)=1:=by
      simpa only [List.range_succ,List.range_zero,List.map_append,List.map_cons,
        List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,
        Function.iterate_succ_apply,Function.iterate_zero_apply,mul_one,one_mul]
        using (show MonoidHom.FixedPointFree tR from hffR).prod_pow_eq_one hit bR
    have hn := congrArg ρ hnR
    rw [map_one] at hn
    rw [map_mul,map_mul,hcov,hcov,hcov] at hn
    convert hn using 1
    group
  have hrC (c:W) (hc:c∈C) : ρ bR c=c:=by
    apply Subtype.ext
    rw [hρ]
    change b*(c:G)*b⁻¹=(c:G)
    have hbc : b*(c:G)=(c:G)*b:=Subgroup.mem_centralizer_iff.mp (hZC hc) b (hRQ bR.property)
    rw [hbc,mul_inv_cancel_right]
  have hEnot : ¬E≤Subgroup.normalizer (Za:Set G):=by
    intro hENZ
    have hUZ : U≤Za:=eight_six_conjugate_closure_le Za E Za le_rfl hENZ
    have hh:=Subgroup.card_le_of_le hUZ
    rw [hUcard,hcard] at hh
    omega
  obtain ⟨e,heE,heZ⟩:=SetLike.not_le_iff_exists.mp hEnot
  let eW:Subgroup.normalizer (W:Set G):=⟨e,hEN heE⟩
  let ew:=W.normalizerMonoidHom eW
  have heMove : C.map ew.toMonoidHom≠C:=by
    intro heq
    apply heZ
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hh:=congrArg (Subgroup.map W.subtype) heq
    rw [Subgroup.map_map] at hh
    have hhom : W.subtype.comp ew.toMonoidHom=(MulAut.conj e).toMonoidHom.comp W.subtype:=by
      ext w
      rfl
    rw [hhom,←Subgroup.map_map,Subgroup.map_subgroupOf_eq_of_le hZW] at hh
    exact hh
  have hCcard : Nat.card C=4:=by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv]
    exact hcard
  exact ⟨helem,hWcard,hCcard,ρ bR,tw,⟨Subgroup.inclusion hRN bR,rfl⟩,⟨tW,rfl⟩,
    hrne,hr2,htw3,hffW,(hcov bR ▸ hρcomm bR (tR bR)),hnorm,hrC,ew,⟨eW,rfl⟩,heMove⟩
end Stellmacher.SectionEight
