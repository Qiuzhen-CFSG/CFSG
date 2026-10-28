module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Lie.RankOneReduction
public import Theory.GroupTheory.CentralCoprimeLiftUnique
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupAction.PGroupFixedLift
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local

/-!
# Actual model actions for the rank-two witness construction

Both distinguished actors act through the same two-subgroup, the image of
T on an actual model of L/O₂(L). Their actions have order two in the unequal
case. Passing through the full central covering kernel preserves the exclusion
of a two-group inverse fixed subgroup and the movement of an odd-order element.
The latter follows from uniqueness of coprime torsion lifts through a central
two-kernel; it does not require normalization of the forward residual.

The projected modified residual is the model fixed two-residual, followed by
O³ exactly when the full component has even-degree PSL₃ type. The forward
and inverse projected residuals are distinct. This retains exceptional covers
and does not replace the full-component test by a quotient-family test.

These reductions apply to the actual model equivalences in all eight rank-two
constructors of Theorem C, with their original parameters. They do not yet
construct the ambient nontrivial two-subgroup, odd-prime plane, and independent
commuting actor required by `OddRankThreeWitness`. That construction and the
use of the full covering/Frattini restrictions remain obligations of this task.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, (E1)–(E2)
and 16.1.2–4, printed pp.1169–1172; 16.4.2(4), 16.4.8, 16.4.11(3), and
16.5.5–6(3), printed pp.1183, 1187–1188, 1193–1194, and 1197.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie.RankTwoConstruction

variable {G S : Type*} [Group G] [Finite G] [Group S]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The actual component projection, followed by the specified model equivalence. -/
def modelMap (e : (L ⧸ pCore 2 L) ≃* S) : L →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

omit [Finite G] in
/-- The projection retains precisely the original two-core kernel. -/
theorem modelMap_ker (e : (L ⧸ pCore 2 L) ≃* S) :
    (modelMap e).ker = pCore 2 L := by
  ext x
  change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [← map_one e, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- The genuine induced action, using the proved equality Z(L) = O₂(L). -/
noncomputable def modelAction (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    MulAut L →* MulAut S :=
  MulAut.centralQuotientAction
    ((QuotientGroup.quotientMulEquivOfEq
      (hG.component_center_eq_twoCore d.setup.involution d.setup.component)).trans e)

/-- Compatibility with the original quotient map, on each component element. -/
theorem modelAction_apply (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    (a : MulAut L) (x : L) :
    modelAction hG d e a (modelMap e x) = modelMap e (a x) :=
  MulAut.centralQuotientAction_apply _ a x

/-- The action of the original inverse actor; the conjugator is unchanged. -/
noncomputable abbrev inverseModelAction (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) : MulAut S :=
  modelAction hG d e
    (L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩)

/-- The forward actor normalizes L because it lies in R ≤ T. -/
theorem forward_mem_normalizer (d : ResidualInputs T z L g R) :
    MulAut.conj g z ∈ normalizer (L : Set G) :=
  d.setup.sylow_normalizes (d.setup.le_sylow (forward_actor d.setup d.transport).1)

/-- The forward actor acts on the same specified model as the inverse actor. -/
noncomputable abbrev forwardModelAction (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) : MulAut S :=
  modelAction hG d e
    (L.normalizerMonoidHom ⟨MulAut.conj g z, forward_mem_normalizer d⟩)

/-- Faithfulness of R on L preserves the forward involution in the model. -/
theorem forwardModelAction_order (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    orderOf (forwardModelAction hG d e) = 2 := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  unfold forwardModelAction modelAction
  rw [MulAut.orderOf_centralQuotientAction]
  let a : R := ⟨MulAut.conj g z, (forward_actor d.setup d.transport).1⟩
  have ho := orderOf_injective
    (L.normalizerMonoidHom.comp
      (inclusion (d.setup.le_sylow.trans d.setup.sylow_normalizes)))
    d.setup.faithful_on_component a
  exact ho.trans ((orderOf_coe a).symm.trans (forward_actor d.setup d.transport).2)

/-- The action of the given ambient Sylow subgroup on the model. -/
noncomputable def sylowModelAction (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    (T : Subgroup G) →* MulAut S :=
  (modelAction hG d e).comp
    (L.normalizerMonoidHom.comp (inclusion d.setup.sylow_normalizes))

/-- The common ambient Sylow action has a two-group image. -/
theorem sylowModelAction_range_two (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    IsPGroup 2 (sylowModelAction hG d e).range :=
  T.isPGroup'.of_surjective _ (sylowModelAction hG d e).rangeRestrict_surjective

/-- The forward action belongs to the actual common two-group image. -/
theorem forward_mem_sylowModelAction (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    forwardModelAction hG d e ∈ (sylowModelAction hG d e).range :=
  ⟨⟨MulAut.conj g z, d.setup.le_sylow (forward_actor d.setup d.transport).1⟩, rfl⟩

/-- Selected Sylow transport places the inverse action in the same image. -/
theorem inverse_mem_sylowModelAction (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    inverseModelAction hG d e ∈ (sylowModelAction hG d e).range :=
  ⟨⟨MulAut.conj g⁻¹ z, (inverse_actor_mem_sylow d.setup d.selected d.transport).1⟩, rfl⟩

/-- Perfectness makes the central quotient action faithful, preserving order two. -/
theorem inverseModelAction_order (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    orderOf (inverseModelAction hG d e) = 2 := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  exact (MulAut.orderOf_centralQuotientAction _ _).trans (d.inverse_action_order hne)

/-- A two-group model fixed subgroup would lift to a two-group fixed subgroup
in the cover, contradicting the unequal-residual hypothesis. -/
theorem inverseModelAction_fixed_not_two (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ¬ IsPGroup 2 (inverseModelAction hG d e).fixedSubgroup := by
  intro hp
  apply inverse_fixed_not_two d hne
  apply MulAut.isPGroup_fixedSubgroup_of_compatible
    (f := modelMap e) (b := inverseModelAction hG d e)
  · rw [modelMap_ker]
    exact pCore_isPGroup
  · intro x
    exact (modelAction_apply hG d e _ x).symm
  · exact hp

/-- An actual odd-order element of the forward residual remains moved in the
quotient model, and its order is unchanged by the central two-kernel. -/
theorem exists_moved_odd_model_element (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ x : L, (x : G) ∈ modifiedCentralizerResidual L (MulAut.conj g z) ∧
      Odd (orderOf x) ∧ orderOf (modelMap e x) = orderOf x ∧
      inverseModelAction hG d e (modelMap e x) ≠ modelMap e x := by
  obtain ⟨x, hx, ho, hm⟩ := d.exists_moved_odd_order_element hne
  have hxL : x ∈ L := ((modifiedCentralizerResidual_le _ _).trans
    ((involutionTwoResidual_le _ _).trans inf_le_left)) hx
  let y : L := ⟨x, hxL⟩
  let a := L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩
  have hy : Odd (orderOf y) := by simpa only [← orderOf_coe y] using ho
  have hcop : Nat.Coprime 2 (orderOf y) := Nat.coprime_two_left.mpr hy
  have hp : IsPGroup 2 (modelMap e).ker := by
    rw [modelMap_ker]
    exact pCore_isPGroup
  refine ⟨y, hx, hy, (modelMap e).orderOf_map_eq_of_coprime_of_isPGroup_ker
    hp y hcop, ?_⟩
  intro hf
  have hf' : modelMap e (a y) = modelMap e y := by
    rw [← modelAction_apply hG d e]
    exact hf
  have he : a y = y :=
    (modelMap e).eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker
      (by rw [modelMap_ker, hG.component_center_eq_twoCore
        d.setup.involution d.setup.component]) hp hcop hf'
      (by rw [← map_pow, pow_orderOf_eq_one, map_one]) (pow_orderOf_eq_one y)
  exact hm (congrArg Subtype.val he)

/-- The embedded image of the full modified residual in this particular model. -/
noncomputable def modelResidual (e : (L ⧸ pCore 2 L) ≃* S) (t : G) : Subgroup S :=
  ((modifiedCentralizerResidual L t).subgroupOf L).map (modelMap e)

private theorem subgroupOf_embedded_residual (p : ℕ) {H : Subgroup G} (hHL : H ≤ L) :
    ((pResidual p H).map H.subtype).subgroupOf L =
      (pResidual p (H.subgroupOf L)).map (H.subgroupOf L).subtype := by
  apply (map_injective L.subtype_injective)
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hHL),
    map_embedded_pResidual, map_subgroupOf_eq_of_le hHL]

open Classical in
/-- Identify the embedded residual image with the model fixed residual,
retaining the O³ test on the full component, including in covered cases. -/
theorem modelResidual_eq (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    {t : G} (ht : t ∈ normalizer (L : Set G)) :
    modelResidual e t =
      if HasEvenLinearThreeType L then
        (pResidual 3 (LiePreliminaries.fixedTwoResidual S
          (modelAction hG d e (L.normalizerMonoidHom ⟨t, ht⟩)))).map
            (LiePreliminaries.fixedTwoResidual S
              (modelAction hG d e (L.normalizerMonoidHom ⟨t, ht⟩))).subtype
      else LiePreliminaries.fixedTwoResidual S
        (modelAction hG d e (L.normalizerMonoidHom ⟨t, ht⟩)) := by
  classical
  let : IsQuasisimple L := d.setup.component.quasisimple
  have ht' : (involutionTwoResidual L t).subgroupOf L =
      LiePreliminaries.fixedTwoResidual L (L.normalizerMonoidHom ⟨t, ht⟩) :=
    SylowSymmetry.ReverseDelta.Comparison.residual_subgroupOf_eq ht
  have hm : ((involutionTwoResidual L t).subgroupOf L).map (modelMap e) =
      LiePreliminaries.fixedTwoResidual S
        (modelAction hG d e (L.normalizerMonoidHom ⟨t, ht⟩)) := by
    rw [ht']
    exact LiePreliminaries.map_fixedTwoResidual (component_oddCore hG d)
      ((QuotientGroup.quotientMulEquivOfEq
        (hG.component_center_eq_twoCore d.setup.involution d.setup.component)).trans e) _
  unfold modelResidual modifiedCentralizerResidual
  split_ifs with he
  · rw [subgroupOf_embedded_residual 3 ((involutionTwoResidual_le L t).trans inf_le_left),
      map_embedded_pResidual, hm]
  · exact hm

/-- The inverse model action cannot fix the forward embedded residual pointwise. -/
theorem forward_modelResidual_not_fixed (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ¬ modelResidual e (MulAut.conj g z) ≤ (inverseModelAction hG d e).fixedSubgroup := by
  intro h
  obtain ⟨x, hx, _, _, hm⟩ := exists_moved_odd_model_element hG d e hne
  exact hm ((MulAut.mem_fixedSubgroup _ _).mp (h (mem_map_of_mem _ hx)))

/-- The inverse embedded residual consists of actual inverse-action fixed points. -/
theorem inverse_modelResidual_fixed (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S) :
    modelResidual e (MulAut.conj g⁻¹ z) ≤ (inverseModelAction hG d e).fixedSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  rw [MulAut.mem_fixedSubgroup, modelAction_apply]
  congr 1
  apply Subtype.ext
  have hc := ((modifiedCentralizerResidual_le _ _).trans
    ((involutionTwoResidual_le _ _).trans inf_le_right)) hx
  change (x : G) ∈ centralizer ({MulAut.conj g⁻¹ z} : Set G) at hc
  change MulAut.conj g⁻¹ z * (x : G) * (MulAut.conj g⁻¹ z)⁻¹ = x
  rw [← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

/-- The covering quotient cannot conceal the difference between the two
embedded modified residuals. No equality of abstract row orders is used. -/
theorem modelResidual_ne (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) (e : (L ⧸ pCore 2 L) ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    modelResidual e (MulAut.conj g⁻¹ z) ≠ modelResidual e (MulAut.conj g z) := by
  intro he
  apply forward_modelResidual_not_fixed hG d e hne
  rw [← he]
  exact inverse_modelResidual_fixed hG d e

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie.RankTwoConstruction
