module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.OddLinear
public import Theory.GroupAction.FixedResidualFixerTransport

/-!
# The two selected actors on the full PSL₃(3) model

A full component equivalence transports the actions of g z g⁻¹ and
g⁻¹ z g to the same concrete PSL₃(3). Tight embedding gives the order
of the forward action, and a moved element gives that of the inverse
action. The model-order comparison excludes the exceptional residual
modification. Thus the actual embedded residual maps to the embedded
fixed two-residual, with a pointwise formula for this equivalence.

Inverse transport gives equal orders of the two model residuals. In the
unequal case an odd-order element of the forward residual is moved by
the actual inverse action. This neither assumes that the inverse action
normalizes the forward residual nor constructs a two-local rank witness.
That construction must use the earlier centralizer rows and ambient geometry.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(1), 16.4.2(4), 16.4.8, 16.4.11(3), and 16.5.5–6,
printed pp.1171, 1183, 1187–1188, 1193–1194 and 1197.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.OddCharacteristic
open OuterResidual ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g t : G} {L R : Subgroup G}

/-- The forward actor, through the specified full component isomorphism. -/
abbrev forwardAction (d : ResidualInputs T z L g R) (e : L ≃* Matrix.PSL3Three.PSL) :
    MulAut Matrix.PSL3Three.PSL :=
  MulAut.congr e (involutionAction d.setup (forward_actor d.setup d.transport).1)

/-- The inverse actor on the same full model, without any change of conjugator. -/
abbrev inverseAction (d : ResidualInputs T z L g R) (e : L ≃* Matrix.PSL3Three.PSL) :
    MulAut Matrix.PSL3Three.PSL :=
  MulAut.congr e (action d.inverse_mem_normalizer)

/-- Faithfulness of R gives order two for the forward model action. -/
theorem forwardAction_order (d : ResidualInputs T z L g R)
    (e : L ≃* Matrix.PSL3Three.PSL) : orderOf (forwardAction d e) = 2 :=
  ((MulAut.congr e).orderOf_eq _).trans
    (involutionAction_order d.setup (disjoint_iff.mp (OrderTwo.faithful d.setup))
      (forward_actor d.setup d.transport).1 (forward_actor d.setup d.transport).2)

/-- Unequal residuals make the inverse model action an involution. -/
theorem inverseAction_order (d : ResidualInputs T z L g R)
    (e : L ≃* Matrix.PSL3Three.PSL)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    orderOf (inverseAction d e) = 2 :=
  ((MulAut.congr e).orderOf_eq _).trans (d.inverse_action_order hne)

/-- Identify the actual embedded modified residual with the model fixed
two-residual. The full component equivalence, not a quotient label, defines the image. -/
theorem pslThree_residual_image (e : L ≃* Matrix.PSL3Three.PSL)
    (hn : t ∈ normalizer (L : Set G)) :
    ((modifiedCentralizerResidual L t).subgroupOf L).map e.toMonoidHom =
      MulAut.embeddedFixedResidual 2 (MulAut.congr e (action hn)) := by
  have hL : ClassicalGroup.IsPSL L 3 3 :=
    ⟨ZMod 3, inferInstance, inferInstance, by simp, ⟨e⟩⟩
  have he := Centrality.OtherRows.OddLinear.pslThree_not_evenLinearThree hL
  rw [modifiedCentralizerResidual, if_neg he]
  have hr : (involutionTwoResidual L t).subgroupOf L =
      MulAut.embeddedFixedResidual 2 (action hn) :=
    SylowSymmetry.ReverseDelta.Comparison.residual_subgroupOf_eq hn
  rw [hr, MulAut.map_embeddedFixedResidual]

/-- Restrict the component isomorphism to the actual embedded residual. -/
noncomputable def pslThree_residualEquiv (e : L ≃* Matrix.PSL3Three.PSL)
    (hn : t ∈ normalizer (L : Set G)) :
    modifiedCentralizerResidual L t ≃*
      MulAut.embeddedFixedResidual 2 (MulAut.congr e (action hn)) :=
  (subgroupOfEquivOfLe ((modifiedCentralizerResidual_le L t).trans
    ((involutionTwoResidual_le L t).trans inf_le_left))).symm.trans
      ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (pslThree_residual_image e hn)))

/-- The residual equivalence is the given component map pointwise. -/
theorem pslThree_residualEquiv_apply (e : L ≃* Matrix.PSL3Three.PSL)
    (hn : t ∈ normalizer (L : Set G)) (x : modifiedCentralizerResidual L t) :
    (pslThree_residualEquiv e hn x : Matrix.PSL3Three.PSL) =
      e ⟨x, ((modifiedCentralizerResidual_le L t).trans
        ((involutionTwoResidual_le L t).trans inf_le_left)) x.property⟩ := rfl

/-- The model residuals have the same order by inverse ambient transport. -/
theorem pslThree_model_residual_card_eq (d : ResidualInputs T z L g R)
    (e : L ≃* Matrix.PSL3Three.PSL) :
    Nat.card (MulAut.embeddedFixedResidual 2 (inverseAction d e)) =
      Nat.card (MulAut.embeddedFixedResidual 2 (forwardAction d e)) := by
  rw [← Nat.card_congr (pslThree_residualEquiv e d.inverse_mem_normalizer).toEquiv,
    ← Nat.card_congr (pslThree_residualEquiv e
      (d.setup.sylow_normalizes (d.setup.le_sylow (forward_actor d.setup d.transport).1))).toEquiv]
  exact d.residual_card_eq

/-- Transport an odd-order moved element while retaining its membership in
the forward fixed residual and the action of the inverse involution. -/
theorem pslThree_exists_moved_odd_element (d : ResidualInputs T z L g R)
    (e : L ≃* Matrix.PSL3Three.PSL)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ x ∈ MulAut.embeddedFixedResidual 2 (forwardAction d e),
      Odd (orderOf x) ∧ inverseAction d e x ≠ x := by
  obtain ⟨x, hx, hodd, hmove⟩ := d.exists_moved_odd_order_element hne
  have hxL := ((modifiedCentralizerResidual_le L (MulAut.conj g z)).trans
    ((involutionTwoResidual_le L (MulAut.conj g z)).trans inf_le_left)) hx
  let xL : L := ⟨x, hxL⟩
  refine ⟨e xL, ?_, ?_, ?_⟩
  · rw [← pslThree_residual_image e
      (d.setup.sylow_normalizes (d.setup.le_sylow (forward_actor d.setup d.transport).1))]
    exact mem_map_of_mem e.toMonoidHom hx
  · rwa [e.orderOf_eq, ← Subgroup.orderOf_coe xL]
  · intro he
    have hfix : action d.inverse_mem_normalizer xL = xL := e.injective (by
      change e (action d.inverse_mem_normalizer (e.symm (e xL))) = e xL at he
      simpa only [e.symm_apply_apply] using he)
    exact hmove (congrArg Subtype.val hfix)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.OddCharacteristic
