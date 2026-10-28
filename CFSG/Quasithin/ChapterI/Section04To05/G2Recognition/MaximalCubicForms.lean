module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCubicCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasCoreComparison
public import Theory.SpecificGroups.G2.TernaryCubicFormNormalization

/-!
# Simultaneous cubic and commutator coordinates on the original core

The original opposite cubic preserves the scalar commutator form. On the
previously constructed cubic coordinates that form has two coefficients.
Their sum is nonzero because the cubic acts nontrivially on D/Z(D). The
first is nonzero because it moves Z(D)/D′: trivial cubic action there would
force the opposite SL₂(3) factor to act trivially, contradicting its central
involution, which inverts the original plane of order nine.

The explicit normalization therefore constructs coordinates preserving both
the form and the cubic action. A possible sign is handled by replacing the
original cubic by its square; the original derived-line scalar generator
is fixed. Short and long versions preserve the actual opposite derived line,
and an inner GL₂ marking gives the first generator equation on these same
coordinates. Chapter14CubicForms applies this to the actual source completion.

This proves simultaneous form/cubic compatibility, not the Weyl generator
equation or agreement of endpoint maps on the whole common middle. Those,
the strongly-three-embedded exclusion and final earlier-source discharge
remain necessary for Aschbacher–Smith I.4.5, printed p.417.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)
noncomputable def cubicScalarCommutator (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →*
      ((cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →* Multiplicative (ZMod 3)) where
  toFun v := {
    toFun w := t.cubicLineScalar (t.cubicCommutatorLine hc v w)
    map_one' := by
      rw [←t.cubicLineScalar.map_one]
      apply congrArg t.cubicLineScalar
      apply Subtype.ext
      exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) ((t.cubicCommutatorPairing v).map_one)
    map_mul' w u := by
      rw [←map_mul]
      apply congrArg t.cubicLineScalar
      apply Subtype.ext
      exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) ((t.cubicCommutatorPairing v).map_mul w u) }
  map_one' := by
    apply MonoidHom.ext
    intro w
    change t.cubicLineScalar (t.cubicCommutatorLine hc 1 w)=1
    rw [←t.cubicLineScalar.map_one]
    apply congrArg t.cubicLineScalar
    apply Subtype.ext
    have h := DFunLike.congr_fun t.cubicCommutatorPairing.map_one w
    exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) h
  map_mul' v w := by
    apply MonoidHom.ext
    intro u
    change t.cubicLineScalar (t.cubicCommutatorLine hc (v*w) u)=
      t.cubicLineScalar (t.cubicCommutatorLine hc v u)*
      t.cubicLineScalar (t.cubicCommutatorLine hc w u)
    rw [←map_mul]
    apply congrArg t.cubicLineScalar
    apply Subtype.ext
    have h := DFunLike.congr_fun (t.cubicCommutatorPairing.map_mul v w) u
    exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) h

theorem cubicScalarCommutator_eq_one (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicScalarCommutator hc v w=1 ↔ t.cubicCommutatorPairing v w=1 := by
  change t.cubicLineScalar (t.cubicCommutatorLine hc v w)=1 ↔ _
  rw [map_eq_one_iff _ t.cubicLineScalar.injective]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : cubicCoreLine c t.x => (z:cubicOddCore c t.x)) h
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) h


/-- The whole endpoint action on its original center plane. -/
def cubicCenterPlaneAction : cubicNormalizer c t.x →* MulAut t.cubicCenterPlane where
  toFun a := ((t.cubicAbelianizationAction a).subgroupMap t.cubicCenterPlane).trans
    (MulEquiv.subgroupCongr (t.cubicCenterPlane_invariant a))
  map_one' := by ext v; change t.cubicAbelianizationAction 1 v=v; rw [map_one]; rfl
  map_mul' a b := by ext v; change t.cubicAbelianizationAction (a*b) v=_; rw [map_mul]; rfl

private def oppositePlaneAction : c.H₂ →* MulAut t.cubicCenterPlane :=
  t.cubicCenterPlaneAction.comp {
    toFun y := ⟨y,by
      exact t.cubicLevi_le_normalizer (mem_sup_left (mem_map_of_mem c.H.subtype y.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

/-- The original opposite SL₂(3) cubic moves the original center plane. -/
private theorem oppositePlaneAction_cubic_ne_one (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.oppositePlaneAction t.y≠1 := by
  intro hy
  let ρ := t.oppositePlaneAction
  have hd : 3∣Nat.card ρ.ker := by
    have hh := orderOf_dvd_natCard (⟨t.y,hy⟩:ρ.ker)
    have ho := (orderOf_injective ρ.ker.subtype ρ.ker.subtype_injective ⟨t.y,hy⟩).symm
    exact (ho.trans t.y_order) ▸ hh
  have hL : Nat.card c.H₂=24 := (Nat.card_congr c.H₂_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hi : ρ.ker.index∣8 := by
    have hh := ρ.ker.card_mul_index
    obtain ⟨k,hk⟩ := hd
    rw [hL,hk,mul_assoc] at hh
    have he : k*ρ.ker.index=8 := by omega
    exact ⟨k,by rw [mul_comm]; exact he.symm⟩
  have hp : IsPGroup 2 (c.H₂ ⧸ ρ.ker) := IsPGroup.of_card_dvd_pow (p:=2) (n:=3) (by
    rw [←index_eq_card]; exact hi)
  have hperfect : IsPPerfect 2 c.H₂ :=
    GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
      c.H₂_model.some.symm.toMonoidHom c.H₂_model.some.symm.surjective
  have htop := hperfect ρ.ker inferInstance hp
  let z : c.H₂ := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  have hz : ρ z=1 := by change z∈ρ.ker; rw [htop]; trivial
  have htriv : ∀ v : t.cubicCenterPlane,v=1 := by
    intro v
    have hfix := congrArg (fun a : MulAut t.cubicCenterPlane => (a v:
      cubicOddCore c t.x ⧸ cubicCoreLine c t.x)) hz
    have hinv : (ρ z v:cubicOddCore c t.x ⧸ cubicCoreLine c t.x)=(v:_ )⁻¹ := by
      obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v.val
      change t.cubicAbelianizationAction _ v.val=v.val⁻¹
      rw [←hw]
      exact t.left_oddCore_quotient_inverted w
    have htwo : (v:cubicOddCore c t.x ⧸ cubicCoreLine c t.x)^2=1 := by
      have he : (v:cubicOddCore c t.x ⧸ cubicCoreLine c t.x)=(v:_ )⁻¹ := hfix.symm.trans hinv
      rw [pow_two]
      calc
        _ = (v:cubicOddCore c t.x ⧸ cubicCoreLine c t.x)⁻¹*v := congrArg (fun w=>w*v.val) he
        _ = 1 := inv_mul_cancel _
    have hthree : (v:cubicOddCore c t.x ⧸ cubicCoreLine c t.x)^3=1 := by
      let := t.left_oddCore_quotient_elementary
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 _) _
    apply Subtype.ext
    change v.val=1
    simpa only [show 3=2+1 from rfl,pow_succ,htwo,one_mul] using hthree
  have hc1 : Nat.card t.cubicCenterPlane=1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨⟨fun v w=>(htriv v).trans (htriv w).symm⟩,inferInstance⟩
  rw [t.cubicCenterPlane_card hc] at hc1
  omega

/-- The whole GL₂ marking restricted to the original center plane. -/
noncomputable def cubicGLCenterPlaneAction (hc : Nat.card (cubicOddCore c t.x)=243) :
    Atlas.G2.TernaryLevi.GL23 →* MulAut t.cubicCenterPlane :=
  t.cubicCenterPlaneAction.comp ((inclusion t.cubicLevi_le_normalizer).comp
    (t.cubicLeviLinearEquiv hc).symm.toMonoidHom)

/-- No element of order three in the marked GL₂ actor fixes the original plane. -/
theorem cubicGLCenterPlaneAction_cubic_ne_one (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : Atlas.G2.TernaryLevi.GL23) (ha : orderOf a=3) :
    t.cubicGLCenterPlaneAction hc a≠1 := by
  let y : t.leftCubicLevi := ⟨t.y,mem_sup_left (mem_map_of_mem c.H.subtype t.y.property)⟩
  have hy : orderOf (t.cubicLeviLinearEquiv hc y)=3 := by
    rw [(t.cubicLeviLinearEquiv hc).orderOf_eq]
    exact (orderOf_coe y).symm.trans ((orderOf_coe t.y.val).trans
      ((orderOf_coe t.y).trans t.y_order))
  have hconj := (Atlas.G2.TernaryLevi.isConj_generator_of_order_three a ha).trans
    (Atlas.G2.TernaryLevi.isConj_generator_of_order_three _ hy).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  intro h
  have hh := congrArg (t.cubicGLCenterPlaneAction hc) hg
  rw [map_mul,map_mul,map_inv,h,mul_one,mul_inv_cancel] at hh
  apply t.oppositePlaneAction_cubic_ne_one hc
  change t.cubicCenterPlaneAction (inclusion t.cubicLevi_le_normalizer y)=1
  have he : t.cubicGLCenterPlaneAction hc (t.cubicLeviLinearEquiv hc y)=
      t.cubicCenterPlaneAction (inclusion t.cubicLevi_le_normalizer y) := by
    change t.cubicCenterPlaneAction (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv hc).symm (t.cubicLeviLinearEquiv hc y)))=_
    rw [MulEquiv.symm_apply_apply]
  exact he ▸ hh.symm

end CubicTorus
namespace AlignedCubicPair
variable {t : CubicTorus c} (p : AlignedCubicPair t)

private theorem right_core_le_middle : p.rightCore≤t.leftCubicBorel := by
  rw [←t.maximal_aligned_borels p.core_order p.aligner p.aligned]
  exact map_mono (le_sup_left.trans le_sup_left)


/-- Every escaping opposite cubic moves the original center plane in D/D′. -/
theorem oppositeActor_moves_center (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ v∈t.cubicCenterPlane,p.oppositeAbelianizationActor r v≠v := by
  let n : cubicNormalizer c t.x := ⟨r,t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩
  let a := t.cubicLinearAction p.core_order n
  have hr3 : (r:G)^3=1 := by
    obtain ⟨w,hw,he⟩ := r.property
    rw [←he,←map_pow]
    have hh := congrArg Subtype.val (t.swap.left_oddCore_cube ⟨w,hw⟩)
    change w^3=1 at hh
    rw [hh,map_one]
  have ha3 : a^3=1 := by
    rw [←map_pow,show n^3=1 from Subtype.ext hr3,map_one]
  have hane : a≠1 := by
    intro h
    have hk : n∈(t.cubicLinearAction p.core_order).ker := h
    rw [t.cubicLinearAction_kernel p.core_order] at hk
    exact hr hk
  by_contra hn
  push Not at hn
  apply t.cubicGLCenterPlaneAction_cubic_ne_one p.core_order a (orderOf_eq_prime ha3 hane)
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change t.cubicAbelianizationAction (inclusion t.cubicLevi_le_normalizer
    ((t.cubicLeviLinearEquiv p.core_order).symm a)) v=v.val
  rw [t.cubicAbelianizationAction_factor p.core_order]
  have hb : t.cubicLinearAction p.core_order (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv p.core_order).symm a))=a :=
    (t.cubicLeviLinearEquiv p.core_order).apply_symm_apply a
  rw [hb,←t.cubicAbelianizationAction_factor p.core_order n]
  exact hn v v.property

/-- The actual opposite cubic preserves the original scalar commutator, including its marking. -/
theorem oppositeActor_scalarForm (r : p.rightCore)
    (v w : p.leftCore ⧸ cubicCoreLine c t.x) :
    t.cubicScalarCommutator p.core_order (p.oppositeAbelianizationActor r v)
      (p.oppositeAbelianizationActor r w)=t.cubicScalarCommutator p.core_order v w := by
  change t.cubicLineScalar (t.cubicCommutatorLine p.core_order _ _)=
    t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)
  apply congrArg t.cubicLineScalar
  apply Subtype.ext
  change (t.cubicCommutatorPairing (t.cubicAbelianizationAction _ v)
    (t.cubicAbelianizationAction _ w):p.leftCore)=(t.cubicCommutatorPairing v w:p.leftCore)
  rw [t.cubicCommutatorPairing_equivariant]
  apply Subtype.ext
  let k : p.leftCore := t.cubicCommutatorPairing v w
  have hk : (k:G)∈⁅p.leftCore,p.leftCore⁆ := by
    rw [t.maximal_core_derived p.core_order]
    exact t.cubicCommutatorPairing_line p.core_order v w
  have hz := (p.aligned_left_derived_le_right_center hk).2 r r.property
  change (r:G)*(k:G)*(r:G)⁻¹=(k:G)
  rw [hz,mul_inv_cancel_right]

private noncomputable def transportedPairing
    (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V) :
    Atlas.G2.TernaryCore.V →* (Atlas.G2.TernaryCore.V →* Multiplicative (ZMod 3)) where
  toFun v := (t.cubicScalarCommutator p.core_order (e.symm v)).comp e.symm.toMonoidHom
  map_one' := by ext w; simp
  map_mul' v w := by ext u; simp

/-- The original commutator has two explicit coefficients on any constructed
short-root coordinates; both structures use this one equivalence. -/
theorem oppositeShortCoordinates_form (r : p.rightCore)
    (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (he : ∀ v,e (p.oppositeAbelianizationActor r v)=Atlas.G2.TernaryCore.shortRoot (e v)) :
    ∃ a b : ZMod 3, ∀ v w,t.cubicScalarCommutator p.core_order v w=
      Multiplicative.ofAdd (a*Atlas.G2.TernaryCore.shortForm (e v) (e w)+
        b*((e v).toAdd 2*(e w).toAdd 3-(e w).toAdd 2*(e v).toAdd 3)) := by
  have hactor (v : Atlas.G2.TernaryCore.V) :
      e.symm (Atlas.G2.TernaryCore.shortRoot v)=p.oppositeAbelianizationActor r (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  obtain ⟨a,b,hab⟩ := Atlas.G2.TernaryCore.shortRoot_invariant_pairing (p.transportedPairing e)
    (fun v => (t.cubicScalarCommutator_eq_one p.core_order _ _).mpr
      (t.cubicCommutatorPairing_self _))
    (by
      intro v w
      change t.cubicScalarCommutator p.core_order (e.symm _) (e.symm _)=_
      rw [hactor,hactor,p.oppositeActor_scalarForm]
      rfl)
  refine ⟨a,b,?_⟩
  intro v w
  have h := hab (e v) (e w)
  change t.cubicScalarCommutator p.core_order (e.symm (e v)) (e.symm (e w))=_ at h
  simpa only [e.symm_apply_apply] using h



/-- The sum of the two coefficients detects the nontrivial original action
on D/Z(D); it cannot vanish for an escaping opposite cubic. -/
theorem oppositeShortCoordinates_coefficient_sum_ne_zero (r : p.rightCore)
    (hr : (r:G)∉p.leftCore)
    (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (he : ∀ v,e (p.oppositeAbelianizationActor r v)=Atlas.G2.TernaryCore.shortRoot (e v))
    (a b : ZMod 3)
    (hform : ∀ v w,t.cubicScalarCommutator p.core_order v w=
      Multiplicative.ofAdd (a*Atlas.G2.TernaryCore.shortForm (e v) (e w)+
        b*((e v).toAdd 2*(e w).toAdd 3-(e w).toAdd 2*(e v).toAdd 3))) : a+b≠0 := by
  intro hab
  let := t.left_oddCore_quotient_elementary
  have hrad (v : p.leftCore ⧸ cubicCoreLine c t.x) :
      p.oppositeAbelianizationActor r v*v⁻¹∈t.cubicCenterPlane := by
    apply (t.cubicCommutatorPairing_radical _).mp
    intro w
    apply (t.cubicScalarCommutator_eq_one p.core_order _ _).mp
    rw [hform,map_mul,map_inv,he]
    apply Multiplicative.toAdd.injective
    change _=0
    simp only [Atlas.G2.TernaryCore.shortForm,Atlas.G2.TernaryCore.shortRoot,
      toAdd_mul,toAdd_inv,toAdd_ofAdd,Pi.add_apply,Pi.neg_apply,
      Matrix.cons_val_zero,Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [Matrix.head_cons,Matrix.tail_cons]
    calc
      _ = -(a+b)*(e v).toAdd 3*(e w).toAdd 3 := by ring
      _ = 0 := by rw [hab]; ring
  let n : cubicNormalizer c t.x := ⟨r,t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩
  have hn : n∈t.cubicCentralQuotientAction.ker := by
    apply MulEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := t.cubicCentralProjection_surjective v
    rw [←t.cubicCentralProjection_equivariant]
    have hw := hrad w
    rw [←t.cubicCentralProjection_kernel,MonoidHom.mem_ker,map_mul,map_inv,
      mul_inv_eq_one] at hw
    exact hw
  rw [t.cubicCentralQuotientAction_kernel p.core_order] at hn
  exact hr hn


/-- The coefficient controlling motion of the radical is nonzero, using the
original opposite SL₂(3) action and its marked central involution. -/
theorem oppositeShortCoordinates_first_coefficient_ne_zero (r : p.rightCore)
    (hr : (r:G)∉p.leftCore)
    (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (he : ∀ v,e (p.oppositeAbelianizationActor r v)=Atlas.G2.TernaryCore.shortRoot (e v))
    (a b : ZMod 3)
    (hform : ∀ v w,t.cubicScalarCommutator p.core_order v w=
      Multiplicative.ofAdd (a*Atlas.G2.TernaryCore.shortForm (e v) (e w)+
        b*((e v).toAdd 2*(e w).toAdd 3-(e w).toAdd 2*(e v).toAdd 3))) : a≠0 := by
  intro ha
  have hb : b≠0 := by simpa only [ha,zero_add] using
    p.oppositeShortCoordinates_coefficient_sum_ne_zero r hr e he a b hform
  obtain ⟨v,hv,hn⟩ := p.oppositeActor_moves_center r hr
  have hz (w) : t.cubicScalarCommutator p.core_order v w=1 :=
    (t.cubicScalarCommutator_eq_one p.core_order _ _).mpr
      ((t.cubicCommutatorPairing_radical v).mpr hv w)
  have h2 := hz (e.symm (Multiplicative.ofAdd ![0,0,0,1]))
  have h3 := hz (e.symm (Multiplicative.ofAdd ![0,0,1,0]))
  rw [hform,e.apply_symm_apply,ha] at h2 h3
  have h2' : b*(e v).toAdd 2=0 := by
    simpa using congrArg Multiplicative.toAdd h2
  have h3' : b*(-(e v).toAdd 3)=0 := by
    simpa using congrArg Multiplicative.toAdd h3
  have hv2 : (e v).toAdd 2=0 := (mul_eq_zero.mp h2').resolve_left hb
  have hv3 : (e v).toAdd 3=0 := neg_eq_zero.mp ((mul_eq_zero.mp h3').resolve_left hb)
  apply hn
  apply e.injective
  rw [he]
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [Atlas.G2.TernaryCore.shortRoot,hv2,hv3]


/-- The original opposite-core marking is a literal homomorphism of actors. -/
theorem oppositeAbelianizationActor_mul (r s : p.rightCore) :
    p.oppositeAbelianizationActor (r*s)=p.oppositeAbelianizationActor r*p.oppositeAbelianizationActor s := by
  exact t.cubicAbelianizationAction.map_mul
    ⟨r,t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩
    ⟨s,t.leftCubicBorel_le (p.right_core_le_middle s.property)⟩

/-- Simultaneous form and cubic coordinates are constructed from the original
cores. Reversing the original cubic, when necessary, respects the fixed scalar
marking and leaves the actual opposite derived line in its literal coordinate. -/
theorem exists_oppositeShortFormCoordinates (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (s : p.rightCore) (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
      (s=r ∨ s=r*r) ∧ (s:G)∉p.leftCore ∧
      (∀ v,e (p.oppositeAbelianizationActor s v)=Atlas.G2.TernaryCore.shortRoot (e v)) ∧
      (∀ v w,t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  obtain ⟨e,he,hline⟩ := p.exists_oppositeShortCoordinates r hr
  obtain ⟨a,b,hform⟩ := p.oppositeShortCoordinates_form r e he
  have ha := p.oppositeShortCoordinates_first_coefficient_ne_zero r hr e he a b hform
  have hab := p.oppositeShortCoordinates_coefficient_sum_ne_zero r hr e he a b hform
  obtain ⟨n,flip,hn,hf,hl⟩ := Atlas.G2.TernaryCore.exists_shortRoot_form_normalization a b ha hab
  have hnewform (v w) : t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm ((e.trans n) v) ((e.trans n) w)) := by
    change t.cubicScalarCommutator p.core_order v w=_
    rw [hform,hf]
    rfl
  have hnewline (v) : v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
      (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
      ((e.trans n) v).toAdd 0=0 ∧ ((e.trans n) v).toAdd 2=0 ∧ ((e.trans n) v).toAdd 3=0 :=
    (hline v).trans (hl (e v)).symm
  cases flip with
  | false =>
    refine ⟨r,e.trans n,Or.inl rfl,hr,?_,hnewform,hnewline⟩
    intro v
    change n (e (p.oppositeAbelianizationActor r v))=Atlas.G2.TernaryCore.shortRoot (n (e v))
    rw [he]
    exact hn (e v)
  | true =>
    have hr3 : (r:G)^3=1 := by
      obtain ⟨w,hw,hh⟩ := r.property
      rw [←hh,←map_pow]
      have hh := congrArg Subtype.val (t.swap.left_oddCore_cube ⟨w,hw⟩)
      change w^3=1 at hh
      rw [hh,map_one]
    have hs : ((r*r:p.rightCore):G)∉p.leftCore := by
      intro h
      have hh : (r:G)*(r:G)=(r:G)⁻¹ := by
        apply mul_eq_one_iff_eq_inv.mp
        simpa only [pow_succ,pow_zero,one_mul] using hr3
      apply hr
      have hi := p.leftCore.inv_mem h
      change ((r:G)*(r:G))⁻¹∈p.leftCore at hi
      simpa only [hh,inv_inv] using hi
    refine ⟨r*r,e.trans n,Or.inr rfl,hs,?_,hnewform,hnewline⟩
    intro v
    change n (e (p.oppositeAbelianizationActor (r*r) v))=Atlas.G2.TernaryCore.shortRoot (n (e v))
    rw [p.oppositeAbelianizationActor_mul]
    change n (e (p.oppositeAbelianizationActor r (p.oppositeAbelianizationActor r v)))=_
    rw [he,he]
    exact hn (e v)


/-- Simultaneous coordinates with the literal long-root convention and the
same scalar marking, constructed from the original opposite cubic. -/
theorem exists_oppositeLongFormCoordinates (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (s : p.rightCore) (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
      (s=r ∨ s=r*r) ∧ (s:G)∉p.leftCore ∧
      (∀ v,e (p.oppositeAbelianizationActor s v)=Atlas.G2.TernaryCore.longRoot (e v)) ∧
      (∀ v w,t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w))) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 1=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  obtain ⟨s,e,hs,hsD,he,hform,hline⟩ := p.exists_oppositeShortFormCoordinates r hr
  refine ⟨s,e.trans Atlas.G2.TernaryCore.shortLongCoordinates,hs,hsD,?_,?_,?_⟩
  · intro v
    change Atlas.G2.TernaryCore.shortLongCoordinates (e (p.oppositeAbelianizationActor s v))=_
    rw [he,Atlas.G2.TernaryCore.shortLongCoordinates_root]
    rfl
  · intro v w
    change t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=Multiplicative.ofAdd
      (Atlas.G2.TernaryCore.longForm (Atlas.G2.TernaryCore.shortLongCoordinates (e v))
        (Atlas.G2.TernaryCore.shortLongCoordinates (e w)))
    rw [Atlas.G2.TernaryCore.shortLongCoordinates_form,hform]
  · intro v
    exact (hline v).trans (Atlas.G2.TernaryCore.shortLongCoordinates_line (e v)).symm

/-- The constructed first generator equation and the original commutator form
hold on one set of coordinates, with an actual inner GL₂ marking. -/
theorem exists_shortRoot_form_comparison (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (s : p.rightCore) (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
      (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
      (s=r ∨ s=r*r) ∧ (s:G)∉p.leftCore ∧
      t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor s ∧
      (∀ v,e (t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false)) v)=
          Atlas.G2.TernaryLevi.shortQuotientAction
            (Atlas.G2.TernaryLevi.generator false) (e v)) ∧
      (∀ v w,t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  obtain ⟨s,e,hs,hsD,he,hform,hline⟩ := p.exists_oppositeShortFormCoordinates r hr
  obtain ⟨κ,hκ⟩ := p.opposite_root_actor_marking s hsD
  exact ⟨s,κ,e,hs,hsD,hκ,
    fun v=>by rw [hκ,he,Atlas.G2.TernaryLevi.shortQuotientAction_root],hform,hline⟩

/-- The simultaneous comparison with the long-root convention. -/
theorem exists_longRoot_form_comparison (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (s : p.rightCore) (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
      (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
      (s=r ∨ s=r*r) ∧ (s:G)∉p.leftCore ∧
      t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor s ∧
      (∀ v,e (t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false)) v)=
          Atlas.G2.TernaryLevi.longQuotientAction
            (Atlas.G2.TernaryLevi.generator false) (e v)) ∧
      (∀ v w,t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w))) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 1=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  obtain ⟨s,e,hs,hsD,he,hform,hline⟩ := p.exists_oppositeLongFormCoordinates r hr
  obtain ⟨κ,hκ⟩ := p.opposite_root_actor_marking s hsD
  exact ⟨s,κ,e,hs,hsD,hκ,
    fun v=>by rw [hκ,he,Atlas.G2.TernaryLevi.longQuotientAction_root],hform,hline⟩

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
