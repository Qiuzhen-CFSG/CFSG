module
public import Stellmacher.SectionEight.EightSixHighCostModuleData
public import Stellmacher.SectionEight.EightSixHighCostExtraspecial
public import Stellmacher.SectionEight.EightSixActorImageNormalizer
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift
/-!
# Suitable representatives of the actual high-cost quotient involutions

In the original selected high-cost configuration with elementary D, every
involution coset of Q Qnext/Qnext has a representative centralizing a subgroup
of Qnext of order32. This is the user-approved suitable-representative
reading of the existing public `QuotientInvolutionCentralizes` predicate.

Construct the literal action on Vnext/Znext with exact two-core kernel.
Equation-one generation identifies the Q-image with the actual A-image,
so every outside quotient actor has the fixed-coset count16 from source19.
The fixed-space preimage C in Vnext has order32, since the kernel is the
central line of order2. The actual equality Qnext=Vnext makes Vnext
extraspecial with that exact center. The supplied action formula shows
conjugation by x is central on C modulo the center and fixes the center.
The generic extraspecial inner-twist theorem supplies r in Qnext such that
conjugation by x*r fixes C pointwise. Its literal subgroup image in G is
the subgroup required by the public predicate.

Source: Stellmacher (8.6)(c3), printed p.41, and (18)--(19), p.45, Journal
of Algebra 190 (1997). The fixed-coset/representative contract was audited
against these source passages and explicitly approved by the user before
integration in LaterDefs.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u
public theorem eight_six_high_cost_quotient_involution_centralizes
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
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D)
 :
    QuotientInvolutionCentralizes Q (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  classical
  obtain ⟨hN,hW,action,hformula,hkernel,_hF⟩ := eight_six_high_cost_residual_module_data
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  let _ := hN
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let Abar := (A.subgroupOf P).map action
  let π := QuotientGroup.mk' (Z.subgroupOf V)
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hRV : R = V := eight_six_high_cost_next_core_eq_v ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1 helementary
  have hextra := eight_six_high_cost_next_core_extraspecial ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  let _ : IsExtraspecial 2 V := hRV ▸ hextra.1
  have hc := eight_six_high_cost_next_core_center ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1
  have hZnative : Subgroup.center V = Z.subgroupOf V := by
    have hcv : CenterAmbient V = Z := hRV ▸ hc
    rw [←hcv]
    exact (Subgroup.comap_map_eq_self_of_injective V.subtype_injective _).symm
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQP : Q ≤ P :=
    ((le_sup_right.trans data.sylow_intersection.symm.le).trans inf_le_right).trans
      (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hRkill : (R.subgroupOf P).map action = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hRnative,hkernel]
  have hAcore := (eight_six_actor_image_eq_core_and_normalized ctx hlength previous D L Q
    hD hL hQ data action hkernel.ge).1
  have hQRimage : ((Q ⊔ R).subgroupOf P).map action = Abar := by
    rw [Subgroup.subgroupOf_sup hQP hRP,Subgroup.map_sup,hRkill,sup_bot_eq,←hAcore]
  have hprofile := eight_six_high_cost_fixed_displacement_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh hN hW action hformula hkernel.ge
  intro x hx hxR _hx2
  have hxP : x ∈ P := (sup_le hQP hRP) hx
  let xp : P := ⟨x,hxP⟩
  have hxnotker : xp ∉ action.ker := by
    intro hk
    apply hxR
    change xp ∈ R.subgroupOf P
    rw [hRnative,←hkernel]
    exact hk
  have hximage : action xp ∈ Abar := hQRimage ▸ Subgroup.mem_map_of_mem action hx
  obtain ⟨a,haA,haeq⟩ := hximage
  have haR : (a:G) ∉ R := by
    intro har
    have hak : a ∈ action.ker := by rw [hkernel,←hRnative]; exact har
    apply hxnotker
    rw [MonoidHom.mem_ker,←haeq]
    exact MonoidHom.mem_ker.mp hak
  have hfixedcard : Nat.card (FixedPoints.subgroup (Subgroup.zpowers (action xp)) W) = 16 := by
    rw [←haeq]
    exact (hprofile.2 a haA haR).1
  let J := FixedPoints.subgroup (Subgroup.zpowers (action xp)) W
  let C := J.comap π
  let α : MulAut V := V.normalizerMonoidHom ⟨x,stabilizer_le_normalizer_v Γ cp.firstStep hxP⟩
  have hαformula (v : V) : π (α v) = action xp (π v) := (hformula xp v).symm
  have hZC : Subgroup.center V ≤ C := by
    intro z hz
    change π z ∈ J
    have hz1 : π z = 1 := (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) z).mpr
      (hZnative ▸ hz)
    rw [hz1]
    exact J.one_mem
  have hαZ : ∀ z : V, z ∈ Subgroup.center V → α z = z := by
    intro z hz
    have hzZ : (z:G) ∈ Z := (show z ∈ Z.subgroupOf V from hZnative ▸ hz)
    have hcomm := Subgroup.mem_centralizer_iff.mp
      ((centerAmbient_le_centralizer P) (hcenter hzZ)) x hxP
    apply Subtype.ext
    change x*(z:G)*x⁻¹=(z:G)
    exact mul_inv_eq_iff_eq_mul.mpr hcomm
  have hαC : ∀ c : V, c ∈ C → α c * c⁻¹ ∈ Subgroup.center V := by
    intro c hc
    have hh := hc ⟨action xp,Subgroup.mem_zpowers (action xp)⟩
    change action xp (π c) = π c at hh
    rw [hZnative]
    apply (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) (α c*c⁻¹)).mp
    change π (α c*c⁻¹) = 1
    rw [map_mul,map_inv,hαformula,hh,mul_inv_cancel]
  have hCimage : C.map π = J :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J
  have hindex : (Z.subgroupOf V).relIndex C = 16 := by
    have hh := Subgroup.relIndex_ker (K := C) π
    rw [QuotientGroup.ker_mk',hCimage] at hh
    exact hh.trans hfixedcard
  have hCcard : Nat.card C = 32 := by
    have hh := ((Z.subgroupOf V).subgroupOf C).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZnative ▸ hZC)).toEquiv] at hh
    change (Z.subgroupOf V).relIndex C * Nat.card (Z.subgroupOf V) = Nat.card C at hh
    rw [hindex,←hZnative,IsExtraspecial.center_order_p 2 V] at hh
    omega
  obtain ⟨r,hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup C hZC α hαZ hαC
  refine ⟨(r:G),hRV.ge r.property,C.map V.subtype,?_,?_,?_⟩
  · exact (Subgroup.map_subtype_le C).trans hRV.ge
  · rw [Subgroup.card_map_of_injective V.subtype_injective,hCcard]
    decide
  · rintro c ⟨v,hv,rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (hr v hv)
    change x*((r:G)*(v:G)*(r:G)⁻¹)*x⁻¹=(v:G) at hh
    have heq : (x*(r:G))*(v:G)*(x*(r:G))⁻¹=(v:G) := by
      simpa only [mul_inv_rev,mul_assoc] using hh
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
end Stellmacher.SectionEight
