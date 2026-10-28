module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Definitions
public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Output specifications for the ordered factors and orthogonal action

The projection retains the literal quotient Y/P and the ordered images of
K and L₂. The matrix action is left-right multiplication on 2 by 2 matrices;
its determinant supplies the split quadratic form preserved by the original
conjugation action. The coefficient field is independent of the marking on V.
These are output specifications, not existence proofs. Their constructors
remain with the component and representation arguments.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
last paragraph of printed p.774; compatibility is proved later in 11.3.8.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G]

/-- The literal quotient and its two ordered source factors. This is the
output of the relative component argument, before representation recognition. -/
structure ProductQuotientMarking (Y P K L₂ : Subgroup G) (F : BinaryField) where
  core_le : P ≤ Y
  first_le : K ≤ Y
  second_le : L₂ ≤ Y
  normalizes : Y ≤ normalizer (P : Set G)
  projection : Y →* (SpecialLinearGroup (Fin 2) F.Carrier ×
    SpecialLinearGroup (Fin 2) F.Carrier)
  surjective : Function.Surjective projection
  kernel : projection.ker = P.subgroupOf Y
  first_factor : (K.subgroupOf Y).map projection =
    (MonoidHom.snd (SpecialLinearGroup (Fin 2) F.Carrier)
      (SpecialLinearGroup (Fin 2) F.Carrier)).ker
  second_factor : (L₂.subgroupOf Y).map projection =
    (MonoidHom.fst (SpecialLinearGroup (Fin 2) F.Carrier)
      (SpecialLinearGroup (Fin 2) F.Carrier)).ker

/-- A marked plus-four action on the literal P. Every matrix action is
original conjugation. The field is independent of the marking on V. -/
structure OrthogonalMarking (Y P K L₂ : Subgroup G) (F : BinaryField)
    extends ProductQuotientMarking Y P K L₂ F where
  coordinates : P ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F.Carrier)
  intertwines : ∀ (y : Y) (p : P),
    (coordinates (P.normalizerMonoidHom (inclusion normalizes y) p)).toAdd =
      ClassicalOrthogonal.FourPlusMatrix.matrixAction (projection y) (coordinates p).toAdd

variable {Y P K L₂ : Subgroup G} {F : BinaryField}
namespace ProductQuotientMarking
variable (d : ProductQuotientMarking Y P K L₂ F)

include d in
/-- Normality is relative to the actual group acting on P. -/
theorem coreNormal : (P.subgroupOf Y).Normal :=
  d.kernel ▸ (inferInstance : d.projection.ker.Normal)

/-- The matrix marking identifies the literal quotient, via its original projection. -/
noncomputable def quotientEquiv :
    letI := d.coreNormal
    (Y ⧸ P.subgroupOf Y) ≃* ClassicalOrthogonal.FourPlusMatrix.PairSL (F := F.Carrier) := by
  letI := d.coreNormal
  exact (QuotientGroup.quotientMulEquivOfEq d.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.projection d.surjective)

/-- No abstract isomorphism replaces the original quotient map. -/
theorem quotientEquiv_mk (y : Y) :
    letI := d.coreNormal
    d.quotientEquiv (QuotientGroup.mk' (P.subgroupOf Y) y) = d.projection y := rfl

/-- In characteristic two the same literal quotient is the product of the
actual projective special-linear groups. -/
noncomputable def quotientPSLEquiv :
    letI := d.coreNormal
    (Y ⧸ P.subgroupOf Y) ≃* (PSL(2,F.Carrier) × PSL(2,F.Carrier)) := by
  letI := d.coreNormal
  exact d.quotientEquiv.trans
    (MulEquiv.prodCongr (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier))
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier)))

/-- The projective identification still has its prescribed value on every
original Y-element; no unmarked abstract quotient is substituted. -/
theorem quotientPSLEquiv_mk (y : Y) :
    letI := d.coreNormal
    d.quotientPSLEquiv (QuotientGroup.mk' (P.subgroupOf Y) y) =
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (d.projection y).1,
        Atlas.RankOneFieldAutomorphisms.slEquivPSL (d.projection y).2) := rfl

end ProductQuotientMarking

namespace OrthogonalMarking
variable (d : OrthogonalMarking Y P K L₂ F)

/-- The split four-dimensional quadratic form in the marked coordinates. -/
def quadraticValue (p : P) : F.Carrier := Matrix.det (d.coordinates p).toAdd

/-- The actual Y-conjugation action preserves that quadratic form. -/
theorem quadraticValue_conjugation (y : Y) (p : P) :
    d.quadraticValue (P.normalizerMonoidHom (inclusion d.normalizes y) p) =
      d.quadraticValue p := by
  unfold quadraticValue
  rw [d.intertwines]
  exact ClassicalOrthogonal.FourPlusMatrix.matrixAction_det _ _

end OrthogonalMarking
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
