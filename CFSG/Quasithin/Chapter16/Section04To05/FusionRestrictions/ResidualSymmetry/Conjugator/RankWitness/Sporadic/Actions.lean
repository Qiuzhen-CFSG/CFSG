module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.PResidual.MapInjectivity
public import Theory.GroupAction.PPerfectCentralQuotientFixed
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The selected residuals in an actual sporadic central quotient

The genuine (E1) hypothesis identifies the component center with its two-core.
Passing through that central kernel detects equality of the two-perfect
selected residuals and detects pointwise fixation without assuming residual
invariance. Consequently unequal residuals give a moved odd-order element
in their actual model image, under the actual involutory inverse action.
All maps retain the full component and its quotient map.

These are reductions for the nine E2(iii) cases of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
16.1.2 and 16.1.5 on printed pp.1170–1172, I.2.2 on pp.409–412, and
Notation 16.5.5 and 16.5.6(3) on p.1197. They do not construct an ambient
odd-rank-three witness. Such a construction needs the marked model geometry,
not merely the abstract isomorphism types or the orders of the residuals.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic

/-- The five Mathieu names in E2(iii). A family construction must also
supply an isomorphism with the named carrier. -/
def IsMathieuName (name : ClassificationModels.SporadicName) : Prop :=
  name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24

/-- The J₂ and HS names, including their permitted central covers. -/
def IsJankoTwoHigmanSimsName (name : ClassificationModels.SporadicName) : Prop :=
  name = .j2 ∨ name = .hs

/-- The remaining J₄ and Ru names. -/
def IsJankoFourRudvalisName (name : ClassificationModels.SporadicName) : Prop :=
  name = .j4 ∨ name = .ru

/-- These branches exhaust exactly the sporadic names allowed by E2(iii).
This is catalogue bookkeeping, not a group recognition theorem. -/
theorem name_cases {name : ClassificationModels.SporadicName}
    (hj3 : name ≠ .j3) (hhe : name ≠ .he) :
    IsMathieuName name ∨ IsJankoTwoHigmanSimsName name ∨ IsJankoFourRudvalisName name := by
  cases name <;> simp_all [IsMathieuName, IsJankoTwoHigmanSimsName, IsJankoFourRudvalisName]

variable {G S : Type*} [Group G] [Group S]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The actual component-to-model map, through its full center. -/
def modelProjection (e : L ⧸ center L ≃* S) : L →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center L))

/-- The full covering kernel is retained by the model projection. -/
theorem modelProjection_ker (e : L ⧸ center L ≃* S) :
    (modelProjection e).ker = center L := by
  ext x
  change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
  rw [← e.map_one, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- The actual image of the embedded residual, restricted to the component. -/
noncomputable def residualImage (e : L ⧸ center L ≃* S) (u : G) : Subgroup S :=
  ((modifiedCentralizerResidual L u).subgroupOf L).map (modelProjection e)

private theorem residual_le_component (u : G) : modifiedCentralizerResidual L u ≤ L :=
  (modifiedCentralizerResidual_le L u).trans ((involutionTwoResidual_le L u).trans inf_le_left)

private theorem residual_subgroupOf_twoPerfect {u : G}
    (hu : IsPPerfect 2 (modifiedCentralizerResidual L u)) :
    IsPPerfect 2 ((modifiedCentralizerResidual L u).subgroupOf L) := by
  let e := (subgroupOfEquivOfLe (residual_le_component (L := L) u)).symm
  exact hu.of_surjective e.toMonoidHom e.surjective

/-- Two-perfectness survives passage to the actual model image. -/
theorem residualImage_twoPerfect (e : L ⧸ center L ≃* S) {u : G}
    (hu : IsPPerfect 2 (modifiedCentralizerResidual L u)) :
    IsPPerfect 2 (residualImage e u) :=
  (residual_subgroupOf_twoPerfect hu).of_surjective
    ((modelProjection e).subgroupMap _)
    ((modelProjection e).subgroupMap_surjective _)

/-- A central two-core cannot identify distinct two-perfect residuals. -/
theorem residualImage_eq_iff (hZ : center L = pCore 2 L)
    (e : L ⧸ center L ≃* S) {u v : G}
    (hu : IsPPerfect 2 (modifiedCentralizerResidual L u))
    (hv : IsPPerfect 2 (modifiedCentralizerResidual L v)) :
    residualImage e u = residualImage e v ↔
      modifiedCentralizerResidual L u = modifiedCentralizerResidual L v := by
  have hp : IsPGroup 2 (modelProjection e).ker := by
    rw [modelProjection_ker, hZ]
    exact pCore_isPGroup
  rw [residualImage, residualImage,
    map_eq_map_iff_of_isPPerfect_of_central_kernel (modelProjection e)
      (residual_subgroupOf_twoPerfect hu) (residual_subgroupOf_twoPerfect hv)
      hp (modelProjection_ker e ▸ le_rfl)]
  constructor
  · intro he
    have hm := congrArg (fun A : Subgroup L => A.map L.subtype) he
    simpa only [map_subgroupOf_eq_of_le (residual_le_component u),
      map_subgroupOf_eq_of_le (residual_le_component v)] using hm
  · intro he
    rw [he]

variable [Finite G]

/-- E1 identifies the two-core quotient with the central quotient,
retaining the full covering component. -/
noncomputable def centralModelEquiv
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ pCore 2 L ≃* S) :
    L ⧸ center L ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore d.setup.involution d.setup.component)).trans e

/-- The unequal-residual case remains unequal in every actual model. -/
theorem selected_residualImages_ne
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    residualImage e (MulAut.conj g⁻¹ z) ≠ residualImage e (MulAut.conj g z) :=
  fun he => hne ((residualImage_eq_iff
    (hG.evenType.component_center_eq_twoCore d.setup.involution d.setup.component)
    e d.inverse_perfect d.forward_perfect).mp he)

/-- Transport the inverse actor on L without assuming residual invariance. -/
noncomputable def inverseModelAction (d : ResidualInputs T z L g R)
    (e : L ⧸ center L ≃* S) : MulAut S :=
  MulAut.centralQuotientAction e
    (L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩)

/-- Faithfulness of the central quotient action retains the involution order. -/
theorem inverseModelAction_order (d : ResidualInputs T z L g R)
    (e : L ⧸ center L ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    orderOf (inverseModelAction d e) = 2 := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  exact (orderOf_injective (MulAut.centralQuotientAction e)
    (MulAut.centralQuotientAction_injective e) _).trans (d.inverse_action_order hne)

/-- Nonfixation survives the full covering kernel, without residual invariance. -/
theorem residualImage_not_fixed
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ¬ residualImage e (MulAut.conj g z) ≤ (inverseModelAction d e).fixedSubgroup := by
  intro hfixed
  let a := L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩
  have hp : IsPGroup 2 (modelProjection e).ker := by
    rw [modelProjection_ker,
      hG.evenType.component_center_eq_twoCore d.setup.involution d.setup.component]
    exact pCore_isPGroup
  have hfix := MulAut.fixed_of_fixed_mod_central_p_kernel (modelProjection e) a
    ((modifiedCentralizerResidual L (MulAut.conj g z)).subgroupOf L)
    (residual_subgroupOf_twoPerfect d.forward_perfect) hp
    (modelProjection_ker e ▸ le_rfl) (by
      intro x hx
      have he := (MulAut.mem_fixedSubgroup _ _).mp
        (hfixed (mem_map_of_mem (modelProjection e) hx))
      simpa only [inverseModelAction, modelProjection, MonoidHom.coe_comp,
        Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.centralQuotientAction_apply]
        using he)
  apply hne
  apply d.eq_iff_centralizes.mpr
  intro x hx
  let xL : L := ⟨x, residual_le_component (MulAut.conj g z) hx⟩
  have he := congrArg Subtype.val (hfix xL hx)
  change MulAut.conj (MulAut.conj g⁻¹ z) x = x at he
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The actual model residual has an odd-order element moved by the
actual inverse involution. No commuting rank witness is asserted. -/
theorem exists_moved_odd_model_element
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ x ∈ residualImage e (MulAut.conj g z), Odd (orderOf x) ∧
      inverseModelAction d e x ≠ x := by
  classical
  let : Finite S := Finite.of_equiv (L ⧸ center L) e.toEquiv
  by_contra! hfixed
  apply residualImage_not_fixed hG d e hne
  let X := residualImage e (MulAut.conj g z)
  let C := (inverseModelAction d e).fixedSubgroup.subgroupOf X
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 X).mpr (residualImage_twoPerfect e d.forward_perfect))
  have hle : closure {x : X | Nat.Coprime 2 (orderOf x)} ≤ C := by
    apply (closure_le C).mpr
    intro x hx
    change (x : S) ∈ (inverseModelAction d e).fixedSubgroup
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply hfixed x x.property
    rw [orderOf_coe]
    exact Nat.coprime_two_left.mp hx
  rw [hgen] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) from mem_top _)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic
