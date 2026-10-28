module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalSquares
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedTransverse
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedSource
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedCoordinates

/-!
# The original source56 partner inputs

One selected cubic and one exchanging Sylow element construct the paired
polar coordinates, the literal fixed line, and the marked extraspecial
actor. At multiplicity one the same coordinates construct the actual
fusion partner, with any supplied recognized action retained unchanged.
Every premise is discharged from the original source hypotheses and the
same marked source54 witness and module multiplicity.

Source: Aschbacher–Smith 15.3.54–56, printed pp.1146–1148.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open ChapterA.Section05To06 ChapterG.Section02
open OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open Core.ResidualGeneration
variable {G : Type*} [Group G] [Finite G]

theorem source56_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS)]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g) :
    letI := moduleSectionNormal h26 h26.I_eq_LU
    letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
    ∀ (f : SourceModuleData h26),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity →
      (∀ v : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).VL,
        ClassicalOrthogonal.FourPlusMatrix.determinantForm (h26.coordinates v).toAdd =
          FusionCore.orthogonalCoordinateValue (d.action.coordinates
            ((MulEquiv.subgroupCongr (original_residual_span hG d hempty hM hu hmany)) v))) →
    ∃ r56 : RecognitionFields (d.T : Subgroup G) d.Z d.ZS d.V
        f.decomposition.leftMultiplicity,
      r56.Y₁ ≤ d.Y ∧
      (f.decomposition.leftMultiplicity=1 →
        ∀ r : RecognizedAction (d.T : Subgroup G) d.Z d.ZS d.V r56.t,
          Nonempty {p : Partner.EarlierGeometry (d.T : Subgroup G) d.Z d.ZS d.V
            r56.Y₁ r56.y r56.t // p.recognized=r}) := by
  let := moduleSectionNormal h26 h26.I_eq_LU
  let := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
  intro f hcommon hmark
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hspan := original_residual_span hG d hempty hM hu hmany
  have hSyl : ∃ P : Sylow 2 d.M, (P : Subgroup d.M).map d.M.subtype = d.T :=
    ⟨d.T.subtype d.sylow_le,map_subgroupOf_eq_of_le d.sylow_le⟩
  obtain ⟨y,hy,hyc,hy3,hyout⟩ := exists_left_cubic_order_three h26
  obtain ⟨t,ht,hex,hout,hjoin⟩ := selected_exchanging_partner
    d.action d.sylow_le hSyl hh.1 inf_le_right hspan h26 y hy hyc
  have hcap := selected_intersection_conjugate_eq_point d (d.V ⊓ closureU d.Z d.ZS)
    g hh.1 rfl hspan h26 rfl f hmark y hy hyc t ht hex hjoin
  have hsquarePlane := original_partner_square_normalizes_plane
    hG d hempty hM hu hmany hfixed hnon g h26 y hy hyc t ht
  have hsquareE := original_partner_square_normalizes
    hG d hempty hM hu hmany hfixed hnon g h26 y hy hyc t ht
  have hk := AbelianExclusion.source_kernel d.T d.Y d.V d.ZS d.Z h
  have hlinecard := card_distinguishedLine d.Z d.ZS h.point_lt.le h.point_card
    (d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1)
  have hseed := FusionCore.CosetSetup.OriginalSource.source_seed_commutator d
  have hVstar := (nonabelian_intersections d (centralizerH d.Z) h
    (original_conjugates_centralize hG d hM hfixed) hnon
    (original_U_nonabelian hG d hempty hM hu hmany hfixed hnon)).2.2
  have hTH : (d.T : Subgroup G) ≤ centralizerH d.Z := le_sup_right.trans h26.base.local_le
  let tH : centralizerH d.Z := ⟨t,hTH ht⟩
  obtain ⟨b⟩ := PairedCoordinates.selected_data hh.1 inf_le_right hspan h26 rfl f hcommon
    y hy hy3 hyc tH ht hcap hsquarePlane hsquareE hk
  exact selected_source56_inputs hh.1 inf_le_right hspan h26 rfl f hcommon
    y hy hy3 hyc hyout tH ht hout hcap hk h.point_lt.le hlinecard hseed hh.2.symm hVstar b


end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
