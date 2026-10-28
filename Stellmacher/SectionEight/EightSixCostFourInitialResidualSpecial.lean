module
public import Stellmacher.SectionEight.EightSixCostFourInitialResidualCore
public import Stellmacher.SectionEight.EightSixInitialThreeCard
public import Stellmacher.SectionEight.EightSixCostFourCentralQuotient
public import Stellmacher.SectionEight.EightSixCostFourModuleQuaternion
public import Theory.GroupAction.ThreeFixedFreeSpecial64

/-!
# The cost-four initial residual two-core is special

The actual initial residual two-core in the selected cost-four configuration
is special, with its full center equal to the initial vertex center Za. The
original local context, geometric data and selected actor are retained. Its
identification with the actual neighboring pair and its order sixty-four
come from previously proved source conclusions.

Choose an actual initial three-Sylow generator and restrict its conjugation
to the normal pair R. The proved fixed-free statement supplies the cubic
automorphism. The initial center is central of order four, and the actual
Q/Za elementary quotient gives R/Za elementary with the same native kernel.
The pair is nonabelian: if it were abelian, its next factor B of order sixteen
would centralize the selected elementary-eight U, contradicting C_V(U)=U.
The generic cubic special-sixty-four theorem then identifies center, derived
subgroup and Frattini subgroup with Za. Transport through the proved
R=O₂(Ea) gives the stated actual residual-core conclusions.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b1),
printed p.44. The center equality also supports the subsequent action on the
elementary-sixteen subgroup in (b3).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement Pointwise IsMulCommutative
universe u
public theorem eight_six_cost_four_initial_residual_special
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
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    CenterAmbient (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) = ZAt ctx.Γ ctx.criticalPath.a ∧
      IsSpecialTwo (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let F := EAt Γ cp.a
  let Z := ZAt Γ cp.a
  let U := conjugateClosure Z E
  let R := (VAt Γ previous ⊓ QAt Γ cp.a) ⊔ (VAt Γ cp.firstStep ⊓ QAt Γ cp.a)
  have hRQ : R ≤ Q := data.core_generation ▸ le_sup_left
  have hQL : Q ≤ L := hQ ▸ twoCoreIn_le L
  have hQP : Q ≤ P := hQL.trans data.closure_le
  have hRnormal := eight_six_initial_pair_normal ctx hquot hlength previous hprev
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRnormal.1).mp hRnormal.2
  let sylow : Sylow 3 P := default
  let T : Subgroup G := (sylow : Subgroup P).map P.subtype
  have hT : IsSylowIn 3 T P := ⟨sylow,rfl⟩
  have hTP : T ≤ P := Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T := sylow.isPGroup'.map P.subtype
  have hTF : T ≤ F := by
    change T ≤ Γ.twoResidualAt cp.a
    rw [Γ.twoResidualAt_def]
    exact eight_six_three_subgroup_le_residual T P hTP hTthree
  have hTcard : Nat.card T = 3 := eight_six_initial_three_card ctx hquot T hT
  let _ : IsCyclic T := isCyclic_of_prime_card hTcard
  obtain ⟨t,htgen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic T)
  have htorder : orderOf (t:G) = 3 := by
    rw [←T.subtype_apply,orderOf_injective T.subtype T.subtype_injective,
      orderOf_eq_card_of_zpowers_eq_top htgen,hTcard]
  have ht3 : (t:G)^3=1 := htorder ▸ pow_orderOf_eq_one (t:G)
  have hgen : Subgroup.zpowers (t:G) = T := by
    have hh := congrArg (Subgroup.map T.subtype) htgen
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,Subgroup.range_subtype,Subgroup.subtype_apply] using hh
  have hfixedR : R ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
    eight_six_cost_four_initial_pair_fixed_free ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost T hT
  have hfixedOne : R ⊓ Subgroup.centralizer ({(t:G)} : Set G) = ⊥ := by
    apply bot_unique
    intro r hr
    have hTR : T ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [←hgen]
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
    have hrt : r ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (hTR hs)
    have hh : r ∈ R ⊓ Subgroup.centralizer (T : Set G) := ⟨hr.1,hrt⟩
    simpa only [hfixedR,Subgroup.mem_bot] using hh
  let tN : Subgroup.normalizer (R : Set G) := ⟨t,hPR (hTP t.property)⟩
  let a : MulAut R := R.normalizerMonoidHom tN
  have haformula (r:R) : (a r:G) = (t:G)*r*(t:G)⁻¹ := rfl
  have hacube : a^3=1 := by
    have hh : tN^3=1 := Subtype.ext ht3
    change (R.normalizerMonoidHom tN)^3=1
    rw [←map_pow,hh,map_one]
  have hafixed : ∀ r:R, a r=r → r=1 := by
    intro r hr
    apply Subtype.ext
    have hh := congrArg Subtype.val hr
    change (t:G)*(r:G)*(t:G)⁻¹=(r:G) at hh
    have hrt : (r:G) ∈ Subgroup.centralizer ({(t:G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hx : (r:G) ∈ R ⊓ Subgroup.centralizer ({(t:G)} : Set G) := ⟨r.property,hrt⟩
    change (r:G)=1
    simpa only [hfixedOne,Subgroup.mem_bot] using hx
  have hZU : Z ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hUV : U ≤ VAt Γ cp.firstStep := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hUR : U ≤ R := (le_inf hUV hcore).trans le_sup_right
  have hZR : Z ≤ R := hZU.trans hUR
  have hUcard : Nat.card U = 8 := eight_six_selected_orbit_card_eight
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUelem : IsElementaryAbelian 2 U := eight_six_selected_orbit_elementary ctx E hcore
  let _ := hUelem
  have hZC : Z ≤ Subgroup.centralizer (Q : Set G) :=
    (eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data).2.2.2
  have hZcenter : Z.subgroupOf R ≤ Subgroup.center R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hZC hz) (r:G) (hRQ r.property)

  let Zi := Z.subgroupOf R
  have hN : Zi.Normal := by
    refine ⟨?_⟩
    intro z hz r
    have hc := Subgroup.mem_center_iff.mp (hZcenter hz) r
    simpa only [hc,mul_assoc,mul_inv_cancel,mul_one] using hz
  let _ := hN
  have hZicard : Nat.card Zi = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv).trans hcard
  have hpair := eight_six_cost_four_initial_pair_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hRcard : Nat.card R = 64 := hpair.2.2.2.2
  obtain ⟨quot,hquotElem⟩ := eight_six_cost_four_central_quotient ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  let _ := quot.groupX
  let _ := quot.finiteX
  let _ : IsElementaryAbelian 2 quot.X := hquotElem
  have hsquare (w : R ⧸ Zi) : w ^ 2 = 1 := by
    refine QuotientGroup.induction_on w ?_
    intro r
    change (QuotientGroup.mk' Zi) (r ^ 2) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    change (r:G)^2 ∈ Z
    have hrQ : (r:G) ∈ Q := hRQ r.property
    have hr2 : (⟨(r:G),hrQ⟩ : Q)^2 ∈ quot.projection.ker := by
      rw [MonoidHom.mem_ker,map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 quot.X) _
    rw [quot.kernel_eq] at hr2
    exact hr2
  let _ : IsElementaryAbelian 2 (R ⧸ Zi) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      have hinv (w : R ⧸ Zi) : w⁻¹ = w :=
        inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare w)
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
  let B := VAt Γ cp.firstStep ⊓ QAt Γ cp.a
  have hBcard : Nat.card B = 16 := hpair.2.1
  have hBR : B ≤ R := le_sup_right
  have hUB : U ≤ B := le_inf hUV hcore
  have hself : VAt Γ cp.firstStep ⊓ Subgroup.centralizer (U : Set G) = U :=
    (eight_six_cost_four_module_quaternion ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).2
  have hnoncomm : ¬ IsMulCommutative R := by
    intro hcomm
    let _ := hcomm
    have hBU : B ≤ U := by
      intro b hb
      rw [←hself]
      refine ⟨hb.1,Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      exact congrArg Subtype.val (mul_comm (⟨u,hUR hu⟩ : R) ⟨b,hBR hb⟩)
    have hcount := Subgroup.card_le_of_le hBU
    rw [hBcard,hUcard] at hcount
    omega
  obtain ⟨hcenterR,hderived,hPhi⟩ := three_fixed_free_special64 hRcard Zi hZcenter hZicard
    hnoncomm a hacube hafixed
  have hReq := eight_six_cost_four_initial_pair_eq_residual_core ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  rw [←hReq]
  change CenterAmbient R = Z ∧ IsSpecialTwo R
  refine ⟨?_,hcenterR.trans hderived.symm,hderived.trans hPhi.symm⟩
  change (Subgroup.center R).map R.subtype = Z
  rw [hcenterR,Subgroup.map_subgroupOf_eq_of_le hZR]
end Stellmacher.SectionEight
