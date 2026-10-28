module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Sections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.CompatibleFields

/-!
# The common-core orthogonal geometry on the original groups

Odd degree and the genuine local-family conditions identify K and L₂ with
their normal containing components in G_P. Their distinct quotient factors
then yield Y = O^{2′}(G_P), the ordered product marking of Y/P, and the
original determinant-preserving action on P. Prime-rank control places the
original X in Y and proves its Cartan property.

These applications discharge every component premise of the representation,
Cartan and compatible-field constructions. The only input is the earlier
source state OrthogonalInput, constructed by the common-core assembly owner
from 11.3.7 and the preceding core/block calculations.

Source: Aschbacher--Smith, combined manuscript, printed p.774, from
“Assume n is even” to the paragraph preceding 11.3.8. The corrected natural
L₂-sections V₂ and P/V₂ are supplied by Representation.Sections.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- The original source join is the product of the two factors and the
odd-index residual of its actual common-core normalizer. -/
theorem source_factorJoin_and_residual :
    orthogonalJoin (f.Li 1) V h = outsideResidual H ⊔ f.Li 1 ∧
      orthogonalJoin (f.Li 1) V h =
        (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype :=
  source_factorJoin_and_residual_of_components d
    (source_residual_normal_component d).1 (source_local_normal_component d).1

/-- The literal quotient Y/P, with its ordered original factors. -/
theorem source_product_quotient :
    Nonempty (ProductQuotientMarking (orthogonalJoin (f.Li 1) V h)
      (pairCore V H h) (outsideResidual H) (f.Li 1) S.field) :=
  source_product_quotient_of_components d
    (source_residual_normal_component d).1 (source_local_normal_component d).1

/-- The independent K-field carries the original orthogonal action on P. -/
theorem source_orthogonal_marking :
    Nonempty (OrthogonalMarking (orthogonalJoin (f.Li 1) V h)
      (pairCore V H h) (outsideResidual H) (f.Li 1) d.pair_field) :=
  source_orthogonal_marking_of_components d
    (source_residual_normal_component d).1 (source_local_normal_component d).1

/-- Determinant invariance under the literal Y-conjugation action. -/
theorem source_quadratic_invariance :
    ∃ a : OrthogonalMarking (orthogonalJoin (f.Li 1) V h)
        (pairCore V H h) (outsideResidual H) (f.Li 1) d.pair_field,
      d.pair_field.degree = S.field.degree ∧
      ∀ (y : orthogonalJoin (f.Li 1) V h) (p : pairCore V H h),
        a.quadraticValue ((pairCore V H h).normalizerMonoidHom
          (inclusion a.normalizes y) p) = a.quadraticValue p :=
  source_quadratic_invariance_of_components d
    (source_residual_normal_component d).1 (source_local_normal_component d).1

/-- The source's original X is a Cartan of the original Y. -/
theorem source_orthogonal_cartan : IsCartan T (orthogonalJoin (f.Li 1) V h) X :=
  source_cartan_of_components d
    (source_residual_normal_component d).1 (source_local_normal_component d).1

open scoped IsMulCommutative

/-- Application to the existing common-plane consumer: its independent
orthogonal marking is constructed from the original source state. -/
theorem source_compatible_fields
    :
    let := D.elementary
    let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
    let := CompatibleCartan.originalModule D (.sl3 m) d.seed_fixed
    ∃ mP : Module S.field.Carrier (Additive (pairCore V H h)),
      let := mP
      (∀ (a : S.field.Carrier) (b : f.Vi 1),
        ((a • Additive.ofMul
          (⟨b,(show (b : G) ∈ pairCore V H h ⊓ V from d.intersection_eq_plane.symm ▸ b.property).1⟩ :
            pairCore V H h)).toMul : G) =
        ((a • Additive.ofMul
          (⟨b,(show (b : G) ∈ pairCore V H h ⊓ V from d.intersection_eq_plane.symm ▸ b.property).2⟩ :
            V)).toMul : G)) ∧
      ∃ ρ : Representation S.field.Carrier (orthogonalJoin (f.Li 1) V h)
          (Additive (pairCore V H h)),
        ∀ (y : orthogonalJoin (f.Li 1) V h) (p : Additive (pairCore V H h)),
          ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G) :=
  source_compatible_fields_of_components d
    (source_residual_normal_component d).1 (source_local_normal_component d).1

/-- The assembled source paragraph, without component, parity, Sylow,
residual, orthogonal-action or Cartan-placement callbacks. -/
theorem source_orthogonal_conclusions :
    let := source_pairCore_normal_sylow d
    Odd S.field.degree ∧ oddCartanPart A = A ∧ A ≤ X ∧
      sourceTL T L = (T : Subgroup G) ∧ (T : Subgroup G) ≤ L ∧
      (∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G)) ∧
      IsElementaryAbelian 2 ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) ∧
      Nat.card ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) =
        (2 ^ S.field.degree) ^ 2 ∧
      Source.NormalComponentIn (coreNormalizer V H h) (outsideResidual H) ∧
      Source.NormalComponentIn (coreNormalizer V H h) (f.Li 1) ∧
      orthogonalJoin (f.Li 1) V h =
        (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype ∧
      Nonempty (OrthogonalMarking (orthogonalJoin (f.Li 1) V h)
        (pairCore V H h) (outsideResidual H) (f.Li 1) d.pair_field) ∧
      IsCartan T (orthogonalJoin (f.Li 1) V h) X := by
  let := source_pairCore_normal_sylow d
  exact ⟨source_degree_odd d,source_hall_eq_oddCartanPart d,source_hall_le_cartan d,
    (source_original_sylow_placement d).1,(source_original_sylow_placement d).2.1,
    (source_original_sylow_placement d).2.2,
    (source_original_sylow_quotient d).1,(source_original_sylow_quotient d).2,
    source_residual_normal_component d,source_local_normal_component d,
    (source_factorJoin_and_residual d).2,source_orthogonal_marking d,
    source_orthogonal_cartan d⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
