module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.Upper
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.Residual.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.ResidualAction
public import Theory.Representation.BinaryConjugationSection.Homogeneous

/-!
# Residual generation on the two literal SL₃ layers

Given genuine homogeneous natural and dual models, their quotient coordinate
equations identify their actions with the canonical source actions. The actual
solvable residual E.L₁ moves every natural copy. On a dual copy its displacements
contain the marked point annihilator, supplemented by the opposite-pair line.
The binary calculations lift to S=[S,E.L₁](Uˣ∩Uʸ), including zero multiplicities.

The homogeneous models remain explicit inputs. Their construction and the
Cartan fixed-space bridges belong to the final assembly owner
`qt-d-1222-sl3-layer-generation`; these conditional results do not complete
11.5.7. No recognition implication or generation identity is assumed.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782; G.2.5, pp.335--336.
-/

@[expose] public section
open Matrix Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
open Recognition Recognition.Hypothesis
attribute [local instance] ZMod.algebra

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
  (hUT : E.W ≤ (T : Subgroup G))
  (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)

variable [((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal]
  [((triple E x y).subgroupOf (thirdLayer E x y)).Normal]
  [IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y))]
  [IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y))]

local instance residualUpperNormal :
    ((S₃ (setup E) x y).subgroupOf (S (setup E) x y)).Normal :=
  inferInstanceAs (((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal)
local instance residualLowerNormal :
    ((S₂ (setup E) x y).subgroupOf (S₃ (setup E) x y)).Normal :=
  inferInstanceAs (((triple E x y).subgroupOf (thirdLayer E x y)).Normal)
local instance residualUpperElementary : IsElementaryAbelian 2 (UpperQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y)))
local instance residualLowerElementary : IsElementaryAbelian 2 (LowerQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y)))

namespace UpperActions
variable {E} (a : UpperActions E x y) {r s : ℕ}

/-- The model action agrees with the literal upper action through the quotient map. -/
theorem upperAction_eq_model
    (m : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r) :
    a.upperAction = m.representation.comp (d.sourceStarComparison hUT hf).projection := by
  apply a.upperSection.action_eq_of_coordinates_eq m.actionSection
  ext b
  exact (congrArg Multiplicative.toAdd (a.upper_coordinates b)).trans
    (m.coordinate_eq b).symm

/-- The model action agrees with the literal lower action through the quotient map. -/
theorem lowerAction_eq_model
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s) :
    a.lowerAction = m.representation.comp (d.sourceStarComparison hUT hf).projection := by
  apply a.lowerSection.action_eq_of_coordinates_eq m.actionSection
  ext b
  exact (congrArg Multiplicative.toAdd (a.lower_coordinates b)).trans
    (m.coordinate_eq b).symm

/-- The original solvable residual acts naturally on the upper coordinates. -/
theorem upper_residual_equivariant
    (m : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r)
    (l : E.L₁) (v) (i : Fin r) :
    m.equivalence (a.upperAction (inclusion (pointResidual_le_threeGroup E d hUT hf) l) v) i =
      (Block.Special.componentModel E d ⟨l, E.L₁_le l.property⟩).val *ᵥ
        (m.equivalence v i) := by
  rw [a.upperAction_eq_model d hUT hf m]
  change m.equivalence (m.representation ((d.sourceStarComparison hUT hf).projection
    (inclusion (d.L_le_I hUT hf) ⟨l, E.L₁_le l.property⟩)) v) i = _
  rw [(d.sourceStarComparison hUT hf).projection_on_L]
  exact m.equivariant _ v i

/-- The original solvable residual acts contragrediently on the lower coordinates. -/
theorem lower_residual_equivariant
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s)
    (l : E.L₁) (v) (i : Fin s) :
    m.equivalence (a.lowerAction (inclusion (pointResidual_le_threeGroup E d hUT hf) l) v) i =
      FrameGeometry.natural.dual
        (Block.Special.componentModel E d ⟨l, E.L₁_le l.property⟩) (m.equivalence v i) := by
  rw [a.lowerAction_eq_model d hUT hf m]
  change m.equivalence (m.representation ((d.sourceStarComparison hUT hf).projection
    (inclusion (d.L_le_I hUT hf) ⟨l, E.L₁_le l.property⟩)) v) i = _
  rw [(d.sourceStarComparison hUT hf).projection_on_L]
  exact (m.equivariant _ v i).trans (DualGeometry.ModelGeometry.dualAction_model d _ _)

/-- The original solvable residual moves the entire upper binary module. -/
theorem upper_residual_full
    (m : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r) :
    Coinvariants.ker (a.upperAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) = ⊤ := by
  let : Algebra (ZMod 2) E.input.field.Carrier := ZMod.algebra _ _
  have hF : 4 ≤ Nat.card E.input.field.Carrier := by
    rw [d.field_card]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) E.input.nonbinary
  apply top_unique
  intro v _
  let ρ := a.upperAction.comp (inclusion (pointResidual_le_threeGroup E d hUT hf))
  let γ (l : E.L₁) := (FrameGeometry.natural
    (Block.Special.componentModel E d ⟨l, E.L₁_le l.property⟩)).toAddMonoidHom
  have he : ∀ l v i, m.equivalence (ρ l v) i = γ l (m.equivalence v i) :=
    a.upper_residual_equivariant d hUT hf m
  have hfull (C : AddSubgroup (Fin 3 → E.input.field.Carrier))
      (hc : ∀ l w, γ l w - w ∈ C) : (⊤ : AddSubgroup _) ≤ C := by
    have hC := Block.Special.parabolic_residual_full hF d.point d.point_dimension C (by
      intro b hb w
      obtain ⟨l, hl, rfl⟩ := (Block.Special.original_residual_model E d).ge hb
      exact hc ⟨l, hl⟩ w)
    exact hC.ge
  have hm := copies_mem_coinvariants ρ m.equivalence.toAddEquiv γ he ⊤ hfull
    (m.equivalence v) (fun _ => AddSubgroup.mem_top _)
  exact (m.equivalence.toAddEquiv.symm_apply_apply v) ▸ hm

/-- All copies of the marked point annihilator are lower residual displacements. -/
theorem lower_residual_contains_annihilator
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s)
    (v : Fin s → Module.Dual E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hv : ∀ i, v i ∈ d.point.dualAnnihilator) :
    m.equivalence.symm v ∈ Coinvariants.ker (a.lowerAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) := by
  let : Algebra (ZMod 2) E.input.field.Carrier := ZMod.algebra _ _
  have hF : 4 ≤ Nat.card E.input.field.Carrier := by
    rw [d.field_card]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) E.input.nonbinary
  let ρ := a.lowerAction.comp (inclusion (pointResidual_le_threeGroup E d hUT hf))
  let γ (l : E.L₁) := (FrameGeometry.natural.dual
    (Block.Special.componentModel E d ⟨l, E.L₁_le l.property⟩)).toAddMonoidHom
  have he : ∀ l v i, m.equivalence (ρ l v) i = γ l (m.equivalence v i) :=
    a.lower_residual_equivariant d hUT hf m
  apply copies_mem_coinvariants ρ m.equivalence.toAddEquiv γ he
    d.point.dualAnnihilator.toAddSubgroup ?_ v hv
  intro C hc f hf
  obtain ⟨b, hb, e, he⟩ := Block.Special.exists_parabolic_residual_dual_displacement
    hF d.point d.point_dimension f hf
  obtain ⟨l, hl, rfl⟩ := (Block.Special.original_residual_model E d).ge hb
  rw [← he]
  exact hc ⟨l, hl⟩ e

/-- The original opposite pair supplies the complementary dual line in every copy. -/
theorem lower_image_oppositePair
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s)
    (v : Fin s → Module.Dual E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hv : ∀ i, v i ∈ (DualGeometry.dualPointGH d).val) :
    m.equivalence.symm v ∈ a.lowerSection.image (oppositePair E x y) := by
  have hm := (m.dual_marks hUT hf (DualGeometry.marked_model_bridges d
    (d.sourceStarComparison hUT hf) (sourceUpperRadicalIdentification E d hUT hf))).2.2
  rw [← oppositePair_eq_core_pair E d hUT hf] at hm
  have hv' : Multiplicative.ofAdd v ∈ DualGeometry.MarkedModel.copies
      (DualGeometry.dualPointGH d).val s := hv
  obtain ⟨q, hq, he⟩ := hm.ge hv'
  obtain ⟨b, hb, rfl⟩ := hq
  apply (a.lowerSection.mem_image _ _).mpr
  refine ⟨b, hb, ?_⟩
  apply m.equivalence.injective
  rw [m.equivalence.apply_symm_apply, a.lower_coordinates b]
  exact congrArg Multiplicative.toAdd he

/-- Residual displacements and the literal opposite-pair image span the lower layer. -/
theorem lower_residual_sup_oppositePair
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s) :
    Coinvariants.ker (a.lowerAction.comp
      (inclusion (pointResidual_le_threeGroup E d hUT hf))) ⊔
        a.lowerSection.image (oppositePair E x y) = ⊤ := by
  have hcomp : IsCompl d.point (DualGeometry.pairPlaneGH d) := by
    refine ⟨(DualGeometry.natural_points_disjoint d).disjoint_sup_right_of_disjoint_sup_left
      (DualGeometry.natural_third_disjoint d), ?_⟩
    apply codisjoint_iff.mpr
    simpa only [DualGeometry.pairPlaneGH, pairPlane, sup_assoc] using
      DualGeometry.natural_points_span d
  have hspan : d.point.dualAnnihilator ⊔ (DualGeometry.dualPointGH d).val = ⊤ :=
    (Subspace.isCompl_dualAnnihilator hcomp).codisjoint.eq_top
  apply top_unique
  intro v _
  have hsplit (i : Fin s) : ∃ u ∈ d.point.dualAnnihilator,
      ∃ w ∈ (DualGeometry.dualPointGH d).val, u + w = m.equivalence v i :=
    Submodule.mem_sup.mp (hspan.ge (Submodule.mem_top))
  choose u hu w hw huw using hsplit
  apply Submodule.mem_sup.mpr
  refine ⟨m.equivalence.symm u,
    a.lower_residual_contains_annihilator d hUT hf m u hu,
    m.equivalence.symm w, a.lower_image_oppositePair d hUT hf m w hw, ?_⟩
  apply m.equivalence.injective
  exact (m.equivalence.map_add _ _).trans
    ((congrArg₂ (· + ·) (m.equivalence.apply_symm_apply u)
      (m.equivalence.apply_symm_apply w)).trans (funext huw))

include a in
/-- Both residual calculations lift to the original subgroup identity, conditional on the two models. -/
theorem threeCore_eq_of_homogeneous_layers
    (upper : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r)
    (lower : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s) :
    threeCore E x y = ⁅threeCore E x y, E.L₁⁆ ⊔ oppositePair E x y :=
  a.threeCore_eq_of_residual_calculations d hUT hf
    (a.upper_residual_full d hUT hf upper)
    (a.lower_residual_sup_oppositePair d hUT hf lower)

end UpperActions
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
