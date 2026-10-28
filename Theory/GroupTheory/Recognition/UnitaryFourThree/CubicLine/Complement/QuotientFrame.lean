module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.QuaternionFrame
public import Theory.Representation.QuaternionSixteenTernary.ActionFrame

/-!
# The marked action on the literal source central quotient

The actual complement acts on D/Z(D), whose distinguished involution is -1.
Choose the quaternion generator supplied by the original reflected marking.
Its fourth power, the marked rotation square, the actual cubic and its
normalization of the right quaternion factor satisfy the structural action
classifier. Both directions of the quaternion-word correspondence retain
the original right factor and the literal complement quotient action.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

instance sourceQuotientElementary : IsElementaryAbelian 3 (c.D ⧸ center c.D) :=
  c.odd_extraspecial.quotient_elementary_abelian

noncomputable def complementLinearAction (k : c.K) :
    Additive (c.D ⧸ center c.D) ≃ₗ[ZMod 3] Additive (c.D ⧸ center c.D) :=
  { (c.complementQuotientAction k).toAdditive with
    map_smul' := ZMod.map_smul (c.complementQuotientAction k).toAdditive }

omit [Finite G] in
@[simp] theorem complementLinearAction_apply (k : c.K) (v : Additive (c.D ⧸ center c.D)) :
    c.complementLinearAction k v=Additive.ofMul (c.complementQuotientAction k v.toMul) := by rfl

omit [Finite G] in
theorem complementLinearAction_mul (k l : c.K) (v : Additive (c.D ⧸ center c.D)) :
    c.complementLinearAction (k*l) v=c.complementLinearAction k (c.complementLinearAction l v) := by
  simp only [complementLinearAction_apply,map_mul,MulAut.mul_apply]
  rfl

omit [Finite G] in
theorem complementLinearAction_involution (v : Additive (c.D ⧸ center c.D)) :
    c.complementLinearAction ⟨z,c.involution_mem_complement⟩ v= -v := by
  obtain ⟨d,hd⟩ := QuotientGroup.mk'_surjective (center c.D) v.toMul
  apply Additive.toMul.injective
  change c.complementQuotientAction ⟨z,c.involution_mem_complement⟩ v.toMul = v.toMul⁻¹
  rw [←hd]
  exact c.involutionAction_inverts d

theorem exists_marked_quotient_action :
    ∃ M : Theory.Representation.QuaternionSixteenTernary.MarkedAction (Additive (c.D ⧸ center c.D)),
      (∀ v, M.reflection v=c.complementLinearAction
        ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩ v) ∧
      (∀ v, M.cubic v=c.complementLinearAction
        ⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩ v) ∧
      (∀ k : Fin 8, ∃ g : c.K, (g:G)∈h.toCentralizerHypothesis.factorData.rightCore ∧
        ∀ v, Theory.Representation.QuaternionSixteenTernary.quaternionWord
          M.rotation M.reflection k v=c.complementLinearAction g v) ∧
      (∀ g : c.K, (g:G)∈h.toCentralizerHypothesis.factorData.rightCore → ∃ k : Fin 8,
        ∀ v, Theory.Representation.QuaternionSixteenTernary.quaternionWord
          M.rotation M.reflection k v=c.complementLinearAction g v) := by
  obtain ⟨a,ha,ha4,har,hw,hwords⟩ := c.exists_complement_quaternion_generator
  let A : c.K := ⟨a,ha⟩
  let R : c.K := ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩
  let Y : c.K := ⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩
  let Z : c.K := ⟨z,c.involution_mem_complement⟩
  let L := c.complementLinearAction
  have hZ (v) : L Z v= -v := c.complementLinearAction_involution v
  have hmul (g t : c.K) (v) : L (g*t) v=L g (L t v) := c.complementLinearAction_mul g t v
  have hA4 : A^4=Z := Subtype.ext ha4
  have hR2 : R^2=Z := Subtype.ext c.marking.rotation_square
  have hRA : R*A=A⁻¹*R := Subtype.ext har
  have hY3 : Y^3=1 := Subtype.ext (c.actors.y_order ▸ pow_orderOf_eq_one (c.actors.y:G))
  have hRY : R*Y=Y^2*R := by
    apply Subtype.ext
    have hy := c.marking.rotation_inverts (c.actors.y:G) (c.actors_eq ▸ c.actors.y.property)
    have hyI : (c.actors.y:G)⁻¹=(c.actors.y:G)^2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [←pow_succ',show 2+1=3 from rfl]
      exact c.actors.y_order ▸ pow_orderOf_eq_one (c.actors.y:G)
    have hh := congrArg (fun x=>x*(c.marking.s*c.marking.t)) hy
    change (c.marking.s*c.marking.t)*(c.actors.y:G)=(c.actors.y:G)^2*(c.marking.s*c.marking.t)
    simpa only [mul_assoc,inv_mul_cancel,mul_one,hyI] using hh
  have h1 (v) : L 1 v=v := by
    simp only [L,complementLinearAction_apply,map_one,MulAut.one_apply]
    rfl
  have hword (k : Fin 8) (v) : L (quaternionMarkedWord A R Z k) v=
      Theory.Representation.QuaternionSixteenTernary.quaternionWord (L A) (L R) k v := by
    fin_cases k <;> simp [quaternionMarkedWord,Theory.Representation.QuaternionSixteenTernary.quaternionWord,
      pow_two,hmul,h1,hZ]
  have hwordG (k : Fin 8) : ((quaternionMarkedWord A R Z k : c.K):G)=quaternionMarkedWord a (c.marking.s*c.marking.t) z k :=
    map_quaternionMarkedWord c.K.subtype A R Z k
  let M : Theory.Representation.QuaternionSixteenTernary.MarkedAction (Additive (c.D ⧸ center c.D)) := {
    rotation := L A
    reflection := L R
    cubic := L Y
    quaternion := {
      a_four := fun v=> by
        have hh := congrArg (fun k=>L k v) hA4
        simpa only [show (4:Nat)=2+1+1 from rfl,pow_succ,pow_zero,pow_two,hmul,h1,hZ] using hh
      r_square := fun v=> by
        have hh := congrArg (fun k=>L k v) hR2
        simpa only [pow_two,hmul,hZ] using hh
      reverse := fun v=> by
        apply (L A).injective
        rw [LinearEquiv.apply_symm_apply]
        have hh : A*(R*A)=R := by rw [hRA]; group
        have hh' := congrArg (fun k=>L k v) hh
        simpa only [hmul] using hh' }
    cubic_cube := fun v=>by
      have hh := congrArg (fun k=>L k v) hY3
      simpa only [show (3:Nat)=2+1 from rfl,pow_succ,pow_zero,pow_two,hmul,h1] using hh
    inverts_cubic := fun v=>by
      have hh := congrArg (fun k=>L k v) hRY
      simpa only [pow_two,hmul] using hh
    cubic_nontrivial := by
      by_contra hh
      push Not at hh
      have he : c.complementQuotientAction Y=1 := by
        apply MulEquiv.ext
        intro v
        exact congrArg Additive.toMul (hh (Additive.ofMul v))
      have hY : Y=1 := c.complementQuotientAction_injective (he.trans c.complementQuotientAction.map_one.symm)
      have hy : (c.actors.y:G)=1 := congrArg Subtype.val hY
      have ho := c.actors.y_order
      simp [hy] at ho
    normalizes := by
      intro k
      let w := quaternionMarkedWord A R Z k
      have hwC : (w:G)∈h.toCentralizerHypothesis.factorData.rightCore := by
        rw [hwordG]
        exact hw k
      have hconj : (c.actors.y:G)*(w:G)*(c.actors.y:G)⁻¹ ∈ h.toCentralizerHypothesis.factorData.rightCore :=
        (mem_normalizer_iff.mp (c.actors.normalizes_right c.actors.y.property) (w:G)).mp hwC
      obtain ⟨j,hj⟩ := hwords _ hconj
      have he : Y*w=quaternionMarkedWord A R Z j*Y := by
        apply Subtype.ext
        have hh := congrArg (fun x=>x*(c.actors.y:G)) hj
        change (c.actors.y:G)*(w:G)=((quaternionMarkedWord A R Z j:c.K):G)*(c.actors.y:G)
        rw [hwordG j]
        simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
      refine ⟨j,?_⟩
      intro v
      rw [←hword,←hword,←hmul,←hmul]
      exact congrArg (fun g=>L g v) he }
  refine ⟨M,fun _=>rfl,fun _=>rfl,?_,?_⟩
  · intro k
    refine ⟨quaternionMarkedWord A R Z k,?_,fun v=>(hword k v).symm⟩
    rw [hwordG]
    exact hw k
  · intro g hg
    obtain ⟨k,hk⟩ := hwords g hg
    have he : g=quaternionMarkedWord A R Z k := Subtype.ext (hk.trans (hwordG k).symm)
    exact ⟨k,fun v=>by rw [he]; exact (hword k v).symm⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
