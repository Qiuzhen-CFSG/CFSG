module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LayerCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FrattiniRadical

/-!
# Faithful action on the Section 10 Frattini-center layer

The corrected actual root reflection exchanges the two middle linear roots.
The central simple Suzuki involution fixes one of them by (10.2)(iii).
Their product therefore moves Phi(U_s2)/Z(U_s2): a fixed coset would give
two different middle-root coordinates for the same element. A nontrivial
normal kernel is impossible. For m>0 this uses Suzuki simplicity; at m=0
it uses the proved order-five product and the normal subgroups of Sz(2).

The resulting binary representation uses the same marked rank-one
isomorphism and retains its conjugation formula on quotient representatives.
No natural-module identification or field-twist synchronization is assumed.
Source: Fong--Seitz II (1974), printed p.224, before (10.11), and I (5D).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
/-- A moving source reflection--involution product detects faithfulness,
including the full solvable actor Sz(2). -/
theorem sectionAction_injective_of_mover (d : RootSection Q split 1)
    (hmove : d.action (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) ≠ 1) :
    Function.Injective d.action := by
  let e := suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel
  apply d.action.ker_eq_bot_iff.mp
  by_cases hm : m = 0
  · subst m
    by_contra hn
    let K := d.action.ker
    have hk : K.comap e.symm.toMonoidHom ≠ ⊥ := by
      intro hz
      have he := congrArg (Subgroup.map e.symm.toMonoidHom) hz
      rw [map_comap_eq_self_of_surjective e.symm.surjective,Subgroup.map_bot] at he
      exact hn he
    let r := frattiniMover Q split 1 0 c.suzuki c.suzukiBorel
    have hcomm : ⁅omegaOneAmbient (simpleRoot Q split 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥ := by
      simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,U,Uat,
        Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega]
        using c.relations.ten_two_ii_right 1
    have ho : orderOf r = 5 := binary_frattiniMover_order Q split 1
      (remainder_le_kernel Q split c) c.suzuki c.suzukiBorel
        c.rotation_eight 0 (by decide) hcomm
    have hr := binary_suzuki_normal_contains_fifth (K.comap e.symm.toMonoidHom) hk (e r)
      (by rw [←map_pow,←ho,pow_orderOf_eq_one,map_one])
    change e.symm (e r) ∈ K at hr
    rw [e.symm_apply_apply] at hr
    exact hmove hr
  · let : IsSimpleGroup (SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    let : IsSimpleGroup (rankOne Q split 1) := e.isSimpleGroup
    exact (inferInstance : d.action.ker.Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => hmove (show _ ∈ d.action.ker from ht ▸ mem_top _))

include c in
theorem phiCenter_mover_moves : (phiCenterSection Q split c).action
    (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) ≠ 1 := by
  let A := positiveRoot Q split (.inl 3)
  let B := positiveRoot Q split (.inl 2)
  let C := positiveRoot Q split (.inr 1)
  let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
  let u : rankOne Q split 1 := inclusion le_sup_left (suzukiParameter Q split 1 m c.suzuki c.suzukiBorel 0 1)
  let d := phiCenterSection Q split c
  obtain ⟨a,ha⟩ : ∃ a : A, a ≠ 1 :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (rootAt_ne_bot Q split 0 _)
  have haPhi : (a : X ⧸ Q.D) ∈ phi (simpleRemainder Q split 1) := by
    change (a : X ⧸ Q.D) ∈ (phi (simpleRemainder Q split 1) : Set _)
    rw [←phiProduct_range Q split c]
    exact ⟨(1,a,1,1,1,PUnit.unit), by
      simp only [phiFactors,rootProduct,OneMemClass.coe_one,one_mul,mul_one]⟩
  let v : d.numerator := ⟨a,haPhi⟩
  have huΩ : (u : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split 1) := by
    rw [←suzukiOmegaParameter_range Q split 1 m c.suzuki c.suzukiBorel]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have hcomm : ⁅omegaOneAmbient (simpleRoot Q split 1),A⁆ = ⊥ := by
    change ⁅omegaOneAmbient (simpleRoot Q split 1),
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥
    simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,U,Uat,
      Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega]
      using c.relations.ten_two_iii_right 1
  have huc : Commute (u : X ⧸ Q.D) (a : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm huΩ) _ a.property).symm
  have hsq : (s.val : X ⧸ Q.D)*(s.val : X ⧸ Q.D) = 1 := by
    simpa only [pow_two] using involutoryRootReflection_sq Q split 1 (UnitarySource.actorReflection Q split 1)
  have hinv : (s.val : X ⧸ Q.D)⁻¹ = (s.val : X ⧸ Q.D) := inv_eq_of_mul_eq_one_right hsq
  have hAB : rightConjugate A (s.val : X ⧸ Q.D) = B := by
    change rightConjugate (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1))
      (s.val : X ⧸ Q.D) = rootAt Q split 0 (Q.simple 1*Q.simple 0)
    rw [rootAt_right Q split 0 _ _ s.val s.class_eq,mul_assoc (Q.simple 1*Q.simple 0)]
    have ht : Q.simple 1*Q.simple 1 = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 1)).2
    rw [ht,mul_one]
  let y : B := ⟨(s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹,by
    rw [←hAB]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ A
    simpa only [hinv,mul_assoc,←mul_assoc (s.val : X ⧸ Q.D) (s.val : X ⧸ Q.D),
      hsq,one_mul,mul_one] using a.property⟩
  have hv : (d.numeratorAction (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) v : X ⧸ Q.D) = y := by
    change ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))*a*
      ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))⁻¹ = (s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹
    calc
      _ = (s.val : X ⧸ Q.D)*((u : X ⧸ Q.D)*a*(u : X ⧸ Q.D)⁻¹)*
          (s.val : X ⧸ Q.D)⁻¹ := by simp only [mul_inv_rev,mul_assoc]
      _ = _ := by rw [huc.eq,mul_inv_cancel_right]
  intro he
  have hz : d.numeratorAction (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) v / v ∈ d.denominator := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact (d.action_mk _ v).symm.trans (congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk v)) he)
  have hz' : (y : X ⧸ Q.D)/(a : X ⧸ Q.D) ∈ omegaOneAmbient C := by
    have hzmap := mem_map_of_mem d.numerator.subtype hz
    rw [phiCenterSection_denominator_image Q split c] at hzmap
    change (d.numeratorAction _ v : X ⧸ Q.D)/(v : X ⧸ Q.D) ∈ omegaOneAmbient C at hzmap
    simpa only [hv] using hzmap
  let z : C := ⟨(y : X ⧸ Q.D)/(a : X ⧸ Q.D),omegaOneAmbient_le _ hz'⟩
  have hh := middleProduct_injective Q split c
    (a₁ := (1,a,1,1,1,PUnit.unit)) (a₂ := (1,1,z⁻¹,y,1,PUnit.unit)) (by
      simp only [middleFactors,rootProduct,Subgroup.coe_inv,OneMemClass.coe_one,one_mul,mul_one]
      change (a : X ⧸ Q.D) = ((y : X ⧸ Q.D)/(a : X ⧸ Q.D))⁻¹*y
      rw [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one])
  exact ha (congrArg (fun p => p.2.1) hh)

include c in
theorem phiCenter_action_injective : Function.Injective (phiCenterSection Q split c).action :=
  sectionAction_injective_of_mover Q split c _ (phiCenter_mover_moves Q split c)

/-- The original conjugation action on Phi(U_s2)/Z(U_s2), as a binary representation. -/
def phiCenterRepresentation : Representation (ZMod 2) (rankOne Q split 1)
    (Additive (phiCenterSection Q split c).Carrier) where
  toFun r := ((phiCenterSection Q split c).action r).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext x; simp only [map_one]; rfl
  map_mul' r s := by ext x; simp only [map_mul]; rfl

@[simp] theorem phiCenterRepresentation_mk (r : rankOne Q split 1)
    (x : (phiCenterSection Q split c).numerator) :
    phiCenterRepresentation Q split c r (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk ((phiCenterSection Q split c).numeratorAction r x)) := rfl

include c in
theorem phiCenterRepresentation_injective : Function.Injective (phiCenterRepresentation Q split c) := by
  intro r s he
  apply phiCenter_action_injective Q split c
  ext v
  exact Additive.ofMul.injective (congrArg
    (fun f : Module.End (ZMod 2) (Additive (phiCenterSection Q split c).Carrier) => f (Additive.ofMul v)) he)

/-- The actor transport is the original marked Suzuki equivalence. -/
def suzukiPhiCenterRepresentation : Representation (ZMod 2) (SuzukiMatrixGroup m)
    (Additive (phiCenterSection Q split c).Carrier) :=
  (phiCenterRepresentation Q split c).comp
    (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel).symm.toMonoidHom

include c in
theorem suzukiPhiCenterRepresentation_injective : Function.Injective (suzukiPhiCenterRepresentation Q split c) :=
  (phiCenterRepresentation_injective Q split c).comp
    (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel).symm.injective

@[simp] theorem suzukiPhiCenterRepresentation_source (r : rankOne Q split 1)
    (x : (phiCenterSection Q split c).numerator) :
    suzukiPhiCenterRepresentation Q split c (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r)
      (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk ((phiCenterSection Q split c).numeratorAction r x)) := by
  change phiCenterRepresentation Q split c
    ((suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel).symm
      (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r)) _ = _
  rw [MulEquiv.symm_apply_apply,phiCenterRepresentation_mk]

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
