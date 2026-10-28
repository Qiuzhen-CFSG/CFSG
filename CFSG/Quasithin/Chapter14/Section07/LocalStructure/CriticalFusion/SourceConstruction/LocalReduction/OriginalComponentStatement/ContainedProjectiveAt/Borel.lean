module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.CenterCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Inverter

/-!
# The original Borel torus supplement at the fixed group and Sylow

The same marked point cubic and fixed centralizer residual generate the odd
torus image. This uses the existing same-G,T kernel supplement and keeps the
actual maps. Source: Aschbacher--Smith 14.7.41, printed p.1061.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_mk coreAction_eq_one_iff)
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- For the original Borel, the torus is the product of the point cubic
and the fixed image of the actual centralizer residual. -/
theorem point_borel_torus_supplement_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (B₀ : Subgroup G) (hBM : B₀ ≤ normalizer (L : Set G))
    (hAB : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype)
    (hBA : B₀ ≤ normalizer (F.Li L 1 : Set G))
    {E : Type*} [Group E] [Finite E] (f : B₀ →* E)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card E))
    (t : G) (htL : t ∈ L) (htB : t ∈ normalizer (B₀ : Set G))
    (α : MulAut E) (heq : ∀ b : B₀, α (f b) = f (B₀.normalizerMonoidHom ⟨t,htB⟩ b)) :
    let B := (pResidual 2 B₀).map B₀.subtype
    let hB := (map_subtype_le (pResidual 2 B₀)).trans hBM
    let C := binaryBorelCentralResidual L B hB
    let P := SourceActions.Markings.image B₀ (F.Li L 1) f
    let D := SourceActions.Markings.image B₀ C f
    P ⊔ D = ⊤ ∧ (∀ x ∈ D, α x = x) := by
  let B := (pResidual 2 B₀).map B₀.subtype
  have hBB : B ≤ B₀ := map_subtype_le _
  have hB := hBB.trans hBM
  let C := binaryBorelCentralResidual L B hB
  have hCB : C ≤ B := map_subtype_le _
  have hgen := AlternatingSevenSource.point_borel_kernel_supplement_at h structural B hB
    (isPPerfect_embedded_pResidual 2 B₀) hAB (hBB.trans hBA)
  have hsup : (F.Li L 1).subgroupOf B₀ ⊔ C.subgroupOf B₀ = B.subgroupOf B₀ := by
    apply map_injective B₀.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (hAB.trans hBB),
      map_subgroupOf_eq_of_le (hCB.trans hBB),map_subgroupOf_eq_of_le hBB]
    exact hgen
  have honto : (B.subgroupOf B₀).map f = ⊤ := by
    have hh := MonoidHom.range_eq_top.mpr (SourceActions.Markings.residual_surjective B₀ f hf ho)
    rwa [MonoidHom.range_comp,inclusion_range] at hh
  refine ⟨?_,?_⟩
  · change ((F.Li L 1).subgroupOf B₀).map f ⊔ (C.subgroupOf B₀).map f = ⊤
    rw [←Subgroup.map_sup,hsup,honto]
  · have htB' : t ∈ normalizer (B : Set G) :=
      normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀) htB
    exact SourceActions.Markings.image_fixed B₀ C (hCB.trans hBB) f hk ho ⟨t,htB⟩
      (binaryBorelCentralResidual_normalized L B hB ⟨htB',L.le_normalizer htL⟩)
      α heq (binaryBorelCentralResidual_fixed L B hB htL htB')

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
