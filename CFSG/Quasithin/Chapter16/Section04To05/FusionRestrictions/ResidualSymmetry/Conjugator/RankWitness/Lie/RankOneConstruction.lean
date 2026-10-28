module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Lie.RankOneReduction
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import Theory.GroupAction.PPerfectFixedLifting

/-!
# The marked quotient obstruction for rank-one residual constructions

The inverse normalizer action is compared with the image of the actual
forward modified residual under a specified central-quotient marking.
Two-perfectness kills any central two-valued displacement. Consequently
fixation in this model is equivalent to equality of the two embedded
residuals upstairs, even for a nontrivial central cover and without any
assumption that the inverse actor normalizes the forward residual.

In the unequal case, the actual quotient action therefore moves an
odd-order element of the marked forward residual. This supplies the
faithful quotient obstruction needed by the remaining PSL₂ field and
PSU₃ constructions. It does not construct their ambient rank-three
witnesses or assert the missing fixation statement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.1–4, printed pp.1169–1171, and 16.5.5–6, printed p.1197.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
variable {S : Type*} [Group S]

/-- The image of the literal modified residual, with its component embedding retained. -/
noncomputable def markedResidual (e : (L ⧸ center L) ≃* S) (t : G) : Subgroup S :=
  ((modifiedCentralizerResidual L t).subgroupOf L).map
    (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))

/-- The actual action induced by the inverse selected actor on the specified model. -/
def inverseModelAction (d : ResidualInputs T z L g R)
    (e : (L ⧸ center L) ≃* S) : MulAut S :=
  MulAut.centralQuotientAction e (L.normalizerMonoidHom
    ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩)

/-- The forward action uses the conjugate of the distinguished involution in R. -/
def forwardModelAction (d : ResidualInputs T z L g R)
    (e : (L ⧸ center L) ≃* S) : MulAut S :=
  MulAut.centralQuotientAction e (L.normalizerMonoidHom
    ⟨MulAut.conj g z, d.setup.sylow_normalizes
      (d.setup.le_sylow (forward_actor d.setup d.transport).1)⟩)

/-- Both actions lie in one actual two-subgroup of the model automorphism group. -/
theorem model_actions_in_two_subgroup (d : ResidualInputs T z L g R)
    (e : (L ⧸ center L) ≃* S) :
    ∃ A : Subgroup (MulAut S), IsPGroup 2 A ∧
      forwardModelAction d e ∈ A ∧ inverseModelAction d e ∈ A := by
  let f := (MulAut.centralQuotientAction e).comp
    (L.normalizerMonoidHom.comp (inclusion d.setup.sylow_normalizes))
  refine ⟨f.range, T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective,
    ?_, ?_⟩
  · exact ⟨⟨MulAut.conj g z, d.setup.le_sylow (forward_actor d.setup d.transport).1⟩, rfl⟩
  · exact ⟨⟨MulAut.conj g⁻¹ z,
      (inverse_actor_mem_sylow d.setup d.selected d.transport).1⟩, rfl⟩

/-- Tight embedding makes the forward quotient action a genuine involution. -/
theorem forwardModelAction_order (d : ResidualInputs T z L g R)
    (e : (L ⧸ center L) ≃* S) : orderOf (forwardModelAction d e) = 2 := by
  let := d.setup.component.quasisimple
  obtain ⟨hu, hu2⟩ := forward_actor d.setup d.transport
  exact (OrderTwo.CentralizerCases.modelAction_order L e d.setup hu).trans hu2

/-- The inverse quotient action is a genuine involution in the unequal case. -/
theorem inverseModelAction_order (d : ResidualInputs T z L g R)
    (e : (L ⧸ center L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    orderOf (inverseModelAction d e) = 2 := by
  let := d.setup.component.quasisimple
  exact (orderOf_injective _ (MulAut.centralQuotientAction_injective e) _).trans
    (d.inverse_action_order hne)

/-- The forward action also has a non-two-group fixed subgroup. -/
theorem forward_fixed_not_two (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ¬ IsPGroup 2 (OuterResidual.involutionAction d.setup
      (forward_actor d.setup d.transport).1).fixedSubgroup := by
  intro hp
  let u := MulAut.conj g z
  let a := OuterResidual.involutionAction d.setup (forward_actor d.setup d.transport).1
  have hb : pResidual 2 a.fixedSubgroup = ⊥ :=
    le_bot_iff.mp (sInf_le ⟨inferInstance, hp.to_quotient ⊥⟩)
  let e := OuterResidual.involutionResidualEquivFixed d.setup
    (forward_actor d.setup d.transport).1
  have hc : Nat.card (involutionTwoResidual L u) = 1 :=
    (Nat.card_congr e.toEquiv).trans (by change Nat.card (pResidual 2 a.fixedSubgroup) = 1; rw [hb, card_bot])
  have hm : modifiedCentralizerResidual L u = ⊥ :=
    eq_bot_iff.mpr ((modifiedCentralizerResidual_le L u).trans
      (eq_bot_of_card_eq _ hc).le)
  have hc' := d.residual_card_eq
  rw [hm, card_bot] at hc'
  exact inverse_ne_bot d hne (eq_bot_of_card_eq _ hc')

/-- Both selected actions are outer in the surviving binary PSL₂ branch. -/
theorem forward_outer_of_binary_psl2 (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n) :
    ¬ ∃ x : L, OuterResidual.involutionAction d.setup
      (forward_actor d.setup d.transport).1 = MulAut.conj x := by
  intro hi
  let := d.setup.component.quasisimple
  obtain ⟨hu, hu2⟩ := forward_actor d.setup d.transport
  have ho := OuterResidual.involutionAction_order d.setup
    (disjoint_iff.mp (OrderTwo.faithful d.setup)) hu hu2
  obtain ⟨_, _, _, _, _, _, _, _, _, hp, _⟩ :=
    LiePreliminaries.psl2_inner_involution_roots (component_oddCore hG d) hn e _ ho hi
  exact forward_fixed_not_two d hne hp

omit [Finite G] in
private theorem modified_le_component (t : G) : modifiedCentralizerResidual L t ≤ L :=
  (modifiedCentralizerResidual_le L t).trans
    ((involutionTwoResidual_le L t).trans inf_le_left)

/-- The marked image remains two-perfect; no injectivity of the quotient is asserted. -/
theorem markedResidual_twoPerfect (d : ResidualInputs T z L g R)
    (e : (L ⧸ center L) ≃* S) :
    IsPPerfect 2 (markedResidual e (MulAut.conj g z)) := by
  let X := modifiedCentralizerResidual L (MulAut.conj g z)
  let c := subgroupOfEquivOfLe (modified_le_component (L := L) (MulAut.conj g z))
  have hp : IsPPerfect 2 (X.subgroupOf L) :=
    d.forward_perfect.of_surjective c.symm.toMonoidHom c.symm.surjective
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  exact hp.of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)

/-- A model involution in the unmodified fixed residual survives the
three-residual modification, including through a central two-cover. -/
theorem involution_mem_markedResidual (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ center L) ≃* S)
    {v : S} (hv : v ∈ LiePreliminaries.fixedTwoResidual S (forwardModelAction d e))
    (hv2 : v ^ 2 = 1) : v ∈ markedResidual e (MulAut.conj g z) := by
  let := d.setup.component.quasisimple
  let u := MulAut.conj g z
  let hn := d.setup.sylow_normalizes (d.setup.le_sylow (forward_actor d.setup d.transport).1)
  have he := OrderTwo.CentralizerCases.modelResidual_eq_fixedTwoResidual L e u hn
    (component_oddCore hG d)
  have hv' : v ∈ OrderTwo.CentralizerCases.modelResidual L e u := by
    rw [he]
    exact hv
  obtain ⟨x, hx, rfl⟩ := hv'
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hk : f.ker = center L := by
    ext y
    change e (QuotientGroup.mk' (center L) y) = 1 ↔ y ∈ center L
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff y
  have hp : IsPGroup 2 f.ker := by
    rw [hk, IsQuasisimple.center_eq_pCore (component_oddCore hG d)]
    exact pCore_isPGroup
  have hxk : x ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hv2
  obtain ⟨k, hpow⟩ := hp ⟨x ^ 2, hxk⟩
  have hxpow : x ^ (2 ^ (k + 1)) = 1 := by
    have h := congrArg (fun y : f.ker => (y : L)) hpow
    simpa only [coe_pow, coe_one, pow_succ', pow_mul] using h
  have hxcoprime : Nat.Coprime 3 (orderOf x) :=
    ((by decide : Nat.Coprime 3 2).pow_right (k + 1)).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hxpow)
  refine ⟨x, ?_, rfl⟩
  change (x : G) ∈ modifiedCentralizerResidual L u
  classical
  rw [modifiedCentralizerResidual]
  split_ifs
  · let y : involutionTwoResidual L u := ⟨x, hx⟩
    refine ⟨y, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    have hy : orderOf y = orderOf x := by
      rw [← orderOf_coe y, ← orderOf_coe x]
    exact hy ▸ hxcoprime
  · exact hx

/-- Fixation of the marked image lifts through the full central two-core.
This is an equivalence of obligations, not a proof that either side holds. -/
theorem residuals_eq_iff_model_fixes (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ center L) ≃* S) :
    modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) =
        modifiedCentralizerResidual L (MulAut.conj g z) ↔
      markedResidual e (MulAut.conj g z) ≤ (inverseModelAction d e).fixedSubgroup := by
  let := d.setup.component.quasisimple
  let t := MulAut.conj g⁻¹ z
  let a := L.normalizerMonoidHom ⟨t, d.inverse_mem_normalizer⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let X := modifiedCentralizerResidual L (MulAut.conj g z)
  have hk : f.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := by
    rw [hk, IsQuasisimple.center_eq_pCore (component_oddCore hG d)]
    exact pCore_isPGroup
  let c := subgroupOfEquivOfLe (modified_le_component (L := L) (MulAut.conj g z))
  have hX : IsPPerfect 2 (X.subgroupOf L) :=
    d.forward_perfect.of_surjective c.symm.toMonoidHom c.symm.surjective
  have he := MulAut.fixes_image_iff_of_central_pgroup_ker
    a (inverseModelAction d e) f hk.le hp
    (fun x => (MulAut.centralQuotientAction_apply e a x).symm) (X.subgroupOf L) hX
  rw [d.eq_iff_centralizes]
  change X ≤ centralizer ({t} : Set G) ↔ (X.subgroupOf L).map f ≤ _
  rw [he]
  constructor
  · intro h x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change t * (x : G) * t⁻¹ = x
    have hc : (x : G) * t = t * (x : G) := mem_centralizer_singleton_iff.mp (h hx)
    rw [← hc, mul_inv_cancel_right]
  · intro h x hx
    let y : L := ⟨x, modified_le_component _ hx⟩
    have hy := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp
      (h (show y ∈ X.subgroupOf L from hx)))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hy).symm

/-- Unequal residuals give genuine motion of an odd-order element in the marked quotient. -/
theorem exists_moved_odd_model_element (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ center L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ x ∈ markedResidual e (MulAut.conj g z), Odd (orderOf x) ∧
      inverseModelAction d e x ≠ x := by
  classical
  let X := markedResidual e (MulAut.conj g z)
  let a := inverseModelAction d e
  let : Finite S := Finite.of_equiv (L ⧸ center L) e.toEquiv
  by_contra! hfixed
  apply hne
  apply (residuals_eq_iff_model_fixes hG d e).mpr
  let C := a.fixedSubgroup.subgroupOf X
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 X).mpr (markedResidual_twoPerfect d e))
  have hle : closure {x : X | Nat.Coprime 2 (orderOf x)} ≤ C := by
    apply (closure_le C).mpr
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply hfixed x x.property
    rw [orderOf_coe]
    exact Nat.coprime_two_left.mp hx
  rw [hgen] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) from mem_top _)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie
