module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Selection
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SmallClassification
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSelection

/-!
# Thompson centralization from the actual small chief actions

The original source supplies one minimal maximum elementary actor with the
balanced rank equalities. Its image is a sharp offender on every noncentral
chief factor. The source residual-centralizer hypothesis forces those factors
to be small natural actions. Their concrete cubic selections, retained on the
same actor and prescribed Sylow image, lift through the actual action kernel.
Thompson replacement then centralizes the full original two-residual.

Every finite-action marking and normalizer, index, commutator, and generation
premise is discharged here. The proof permits an odd part in the chief kernel;
it uses the subgroup geometry needed by replacement rather than an additional
claim that the selected overgroup has symmetric-three quotient.

Source: Aschbacher–Smith, original3.1.9(5) and15.1.12(4), printed pp.578,1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
theorem QrcHypotheses.sqtk_thompson_omega_centralizes_residual
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G)) :
    omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
      centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  have hp := source_intrinsic_minimalParabolic_of_notFF d hne
    (source_notFF_of_ratio_two d hq) S hS
  have hsmall := h.sqtk_chief_small_natural_alternatives hG hM hu hJ hne hV hdual hq hres
  apply h.sqtk_thompson_omega_centralizes_residual_of_chief_geometry hG hM hu hJ hne hV hdual hq
  dsimp only
  intro A hA hAR hquad hmin h1 h2 hc s i hi hoff hr
  let := s.factorRepresentation_irreducible i
  exact ChapterB.minimalParabolic_chief_small_selection
    (s.factorRepresentation i) S hp A hA.1 hoff (hsmall s i hi).1
end CFSG.Quasithin.Chapter3
