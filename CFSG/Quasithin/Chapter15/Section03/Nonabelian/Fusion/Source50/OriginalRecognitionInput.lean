module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.SourceInputAdapter
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.Multiplicity
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Fields

/-!
# Recognition inputs from the original marked pair

The same marked G.2.6 hypothesis and source module witness determine the
pair quotient and its common multiplicity. Source55 makes the literal U/Z
elementary and constructs its power form. The original V image has order
two, so it supplies the marked generator. Combining these facts with the
source56 fields constructs the earlier recognition, action and power inputs
on the original Sylow subgroup, without a multiplicity-one assumption.

The source56 record is the sole independent earlier-source output left to
its geometry producer. Source: Aschbacher–Smith, 15.3.54–58, pp.1146–1149.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open ChapterA.Section05To06
open ChapterG.Section02 OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
open Recognition Recognition.NormalReduction
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
  (hempty : MainForward.faithfulLocalComponents d.T = ∅)
  (hM : IsOrderingMaximal d.T d.M)
  (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
  (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
include hG hempty hM hu hmany hfixed

/-- The original central point is normal in its actual closure U. -/
theorem original_vector_normal : (d.Z.subgroupOf (closureU d.Z d.ZS)).Normal :=
  denominator_normal (original_hypothesis hG d hempty hM hu hmany hfixed).plus_le_H

/-- The pair generation, module inclusion and nonorthogonal point all use
the chosen marked G.2.6 witness. -/
theorem original_pair_scalar_fields
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g) :
    pairI d.Z d.ZS g = d.Y ⊔ closureU d.Z d.ZS ∧
      pairI d.Z d.ZS g ≤ d.M ∧
      d.V ≤ pairP d.Z d.ZS g ⊓ centralizer (pairP d.Z d.ZS g : Set G) ∧
      ¬ rightConjugate d.Z g ≤ d.V ⊓ closureU d.Z d.ZS := by
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hs := original_residual_span hG d hempty hM hu hmany
  have hi := h26.I_eq_LU
  rw [Chapter15.I_eq g hh.1 inf_le_right,Chapter15.closure_eq hh.1 inf_le_right] at hi
  have hv := h26.central_first_layer
  rw [Chapter15.VL_eq hs,Chapter15.S_eq g hh.1 inf_le_right] at hv
  refine ⟨hi,?_,hv,h26.nonorthogonal⟩
  rw [hi]
  exact sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
    (h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le))

/-- Source55 supplies elementarity on the exact quotient used in recognition. -/
theorem original_vector_elementary
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g) :
    IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS) := by
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hs := original_residual_span hG d hempty hM hu hmany
  obtain ⟨he,hz,_⟩ := PairGeometry.literal_extraspecial hh.1 inf_le_right hs h26 rfl
  let := he
  let := IsExtraspecial.quotient_elementary_abelian 2 (closureU d.Z d.ZS)
  let e := QuotientGroup.quotientMulEquivOfEq hz
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

/-- The exact source56 fields discharge the remaining normal-reduction
inputs, preserving the chosen g, f, common multiplicity and Sylow group. -/
theorem original_recognition_inputs
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g) :
    letI := moduleSectionNormal h26 h26.I_eq_LU
    letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
    ∀ (f : SourceModuleData h26),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity →
    letI := original_vector_normal hG d hempty hM hu hmany hfixed
    letI := original_vector_elementary hG d hempty hM hu hmany hfixed hnon g h26
    letI := d.action.elementary
    ∀ r : PartnerGeometry.RecognitionFields d.T d.Z d.ZS d.V f.decomposition.leftMultiplicity,
      ∃ v : ActorQuotient d.Z,
      ∃ e : EarlierSourceInputs d.Z d.ZS d.V d.M KnownSimple.IsKnownSimple v f.decomposition.leftMultiplicity,
        e.T = d.T ∧ e.g = g ∧ e.Y = d.Y ∧
        ∃ a : EarlierActionInputs e, a.X = partnerX d.Z d.ZS r.y ∧ EarlierPowerInputs e a := by
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  intro f hcommon
  let := original_vector_normal hG d hempty hM hu hmany hfixed
  let := original_vector_elementary hG d hempty hM hu hmany hfixed hnon g h26
  let := d.action.elementary
  intro r
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hf := original_conjugates_centralize hG d hM hfixed
  have hab := original_U_nonabelian hG d hempty hM hu hmany hfixed hnon
  have hcard : Nat.card (Recognition.actorImage d.Z d.V) = 2 :=
    (nonabelian_intersections d (centralizerH d.Z) h hf hnon hab).2.2
  obtain ⟨v,hv⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top
    (Recognition.actorImage d.Z d.V)).mp (isCyclic_of_prime_card hcard)
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hs := original_residual_span hG d hempty hM hu hmany
  have hp := original_pair_scalar_fields hG d hempty hM hu hmany hfixed hnon g h26
  have hc := hp.2.2.1.trans inf_le_right
  let := LocalRestrictions.pair_denominator_normal d.Z d.ZS d.V g hc
  have hdec := PairGeometry.LayerAdapters.literal_common_quotient hh.1 inf_le_right hs h26 f rfl hcommon
  let e := original_earlierSourceInputs hG d hempty hM hu hmany hfixed hnon v hv
    f.decomposition.leftMultiplicity
    ((partnerX d.Z d.ZS r.y ⊔ zpowers r.t).subgroupOf (centralizerH d.Z))
    r.J_le_T r.fixed_line r.dimension g hp.1 hc hdec r.extraspecial_product
  obtain ⟨hextra,hcenter,_⟩ := PairGeometry.literal_extraspecial hh.1 inf_le_right hs h26 rfl
  have hT : e.T = d.T := by
    dsimp only [e,original_earlierSourceInputs]
  have hT' : (e.T : Subgroup G) = (d.T : Subgroup G) := congrArg Sylow.toSubgroup hT
  exact ⟨v,e,hT,rfl,rfl,r.action_power e hT' hextra hcenter⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
