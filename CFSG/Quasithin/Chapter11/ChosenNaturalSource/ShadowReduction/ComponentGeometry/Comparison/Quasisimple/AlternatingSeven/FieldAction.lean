module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FixedSeed
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
import Mathlib.Tactic.Group

/-!
# The literal field-action obstruction at the end of 11.4.2

The field action is an equation on the marked L1 image in the original
centralizer quotient. An element of that image times its centralizer acts
inner. The trace calculation for SL2, transported through PSL2 in
characteristic two, proves that a nontrivial field automorphism cannot be
inner. We then apply this to an actual maximum elementary subgroup of T.

The existence of the maximum elementary subgroup with field action and
the inner-image containment from the original natural L-module remain
separate source obligations. These conditional assembly lemmas do not
assert either obligation or the completed source contradiction.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- A nontrivial field automorphism on the marked image, retaining the
original element of KzT, the quotient map and the actual PSL2 coordinates. -/
def IsFieldElement (a : localGroup E) : Prop :=
  ∃ (e : seedImage E ≃* PSL(2,E.input.field.Carrier))
    (σ : E.input.field.Carrier ≃+* E.input.field.Carrier), σ ≠ 1 ∧
    ∀ k : seedImage E,
      projection E a * (k : ActionQuotient E) * (projection E a)⁻¹ =
        (e.symm (Atlas.fieldEquivPSL 2 σ (e k)) : ActionQuotient E)

/-- The original natural-module calculation must place Thompson elements
normalizing L1 in the inner-action preimage on that same marked image. -/
def ThompsonInnerImage : Prop :=
  ∀ a : localGroup E,
    (a : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) →
    (a : G) ∈ normalizer (E.L₁ : Set G) →
    projection E a ∈ seedImage E ⊔ centralizer (seedImage E : Set (ActionQuotient E))

/-- The A7 geometry must construct this actual maximum elementary witness,
including normalization of the original seed and the literal field action. -/
def HasMaximalFieldWitness : Prop :=
  ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
    ∃ a : localGroup E, (a : G) ∈ A ∧
      (a : G) ∈ normalizer (E.L₁ : Set G) ∧ IsFieldElement E a

/-- Trace invariance rules out membership in the inner-action preimage. -/
theorem fieldElement_not_inner (a : localGroup E) (ha : IsFieldElement E a) :
    projection E a ∉ seedImage E ⊔ centralizer (seedImage E : Set (ActionQuotient E)) := by
  obtain ⟨e,σ,hσ,hact⟩ := ha
  intro hmem
  change projection E a ∈ ((seedImage E ⊔
    centralizer (seedImage E : Set (ActionQuotient E)) : Subgroup (ActionQuotient E)) :
      Set (ActionQuotient E)) at hmem
  rw [coe_mul_of_right_le_normalizer_left _ _ (Subgroup.centralizer_le_normalizer _)] at hmem
  obtain ⟨b,hb,c,hc,hbc⟩ := hmem
  let b' : seedImage E := ⟨b,hb⟩
  apply hσ
  apply Atlas.RankOneFieldAutomorphisms.field_eq_one_of_PSL_inner σ (e b')
  apply MulEquiv.ext
  intro x
  obtain ⟨k,rfl⟩ := e.surjective x
  have hconj : projection E a * (k : ActionQuotient E) * (projection E a)⁻¹ =
      b * (k : ActionQuotient E) * b⁻¹ := by
    rw [←hbc, mul_inv_rev]
    have hck : c * (k : ActionQuotient E) = (k : ActionQuotient E) * c :=
      (hc k k.property).symm
    calc
      b * c * (k : ActionQuotient E) * (c⁻¹ * b⁻¹) =
          b * (c * (k : ActionQuotient E)) * c⁻¹ * b⁻¹ := by group
      _ = b * ((k : ActionQuotient E) * c) * c⁻¹ * b⁻¹ := by rw [hck]
      _ = b * (k : ActionQuotient E) * b⁻¹ := by group
  have he : e.symm (Atlas.fieldEquivPSL 2 σ (e k)) = b' * k * b'⁻¹ :=
    Subtype.ext ((hact k).symm.trans hconj)
  have hh := congrArg e he
  simpa only [e.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply] using hh

/-- Conditional final assembly: maximum-elementary membership gives actual
Thompson membership, and the field-action equation contradicts innerness.
Both independent source inputs must still be constructed by their owners. -/
theorem false_of_inner_image_and_field_witness
    (hinner : ThompsonInnerImage E) (hfield : HasMaximalFieldWitness E) : False := by
  obtain ⟨A,hA,a,ha,hn,hfield⟩ := hfield
  exact fieldElement_not_inner E a hfield (hinner a ((le_sSup hA) ha) hn)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
