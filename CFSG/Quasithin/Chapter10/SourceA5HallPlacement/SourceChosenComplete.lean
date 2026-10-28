module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourcePlacementComplete
public import CFSG.Quasithin.Chapter10.SourceA5PointControlComplete

/-!
# Hall placement on the actual minimal setup after tensor exclusion

The original multiple-overgroup hypothesis supplies both cubic bounds.
Excluding the same setup's tensor model forces a proper seed, whose support
is separated by D.3.5. The completed point-centralizer theorem and Hall
placement then give w=n(H)=2 and the natural SL₂(4) marking. In particular
n(H)>1 is proved, so the full Hall witness is available for every H* group.

These are applications on the original chosen fundamental setup, with all
numerical, support, point and Hall inputs discharged. The independent tensor
exclusion remains explicit for the Chapter 10 normalization assembly owner.
Source: Aschbacher--Smith D.3.5, 10.2.3 and 10.2.9--13,
printed pp.195--196,744--745,750--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance sourceChosenMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance sourceChosenFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The chosen source weak-closure endpoint retains only the independent
tensor exclusion; the setup, quotient map and natural marking are literal. -/
theorem source_a5_natural_and_parameters_eq_two_after_tensor_exclusion
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧ generationParameter H = 2 ∧
      ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  have hproper := source_a5_seed_ne_local_of_no_tensor D e hn hD hmany hnot
  have hsep := source_a5_moved_seed_separated D e hn ht htn hproper
    (source_local_module_cubic_bound_of_many D hmany)
  have hcent := (source_a5_point_control_after_tensor_exclusion_of_many
    D e hn ht htn hD hmany hnot).1
  exact source_a5_natural_and_parameters_eq_two D e hn ht htn hD
    (source_full_module_cubic_bound_of_many D hmany) hsep hcent hH

/-- Every actual H* group now has a faithful full Hall witness inside L₀.
The source lower bound supplies n(H)>1; it is not an additional hypothesis. -/
theorem source_a5_hstar_hall_placement_after_tensor_exclusion
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ ∧
      B.map H.subtype ≤ localOrbit T L := by
  obtain ⟨_,hgen,_⟩ := source_a5_natural_and_parameters_eq_two_after_tensor_exclusion
    D e hn ht htn hD hmany hnot hH
  have hproper := source_a5_seed_ne_local_of_no_tensor D e hn hD hmany hnot
  have hsep := source_a5_moved_seed_separated D e hn ht htn hproper
    (source_local_module_cubic_bound_of_many D hmany)
  exact source_a5_hstar_hall_placement D e hn ht htn
    (source_a5_original_bounded_separated_coordinates D e hn ht htn hD
      (source_full_module_cubic_bound_of_many D hmany) hsep) hH (by omega)

end CFSG.Quasithin.Chapter10
