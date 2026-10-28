module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedGeometry

/-!
# Sylow squares preserve the selected source-56 geometry

The actual U action has index two in the Sylow action on V, so every
Sylow square lies in U C_T(V). Both factors normalize the selected plane;
its normalizer also normalizes the selected elementary subgroup E. This
supplies the second half of the exchange by the same source element t.

Source: Aschbacher–Smith, 15.3.53 and 15.3.56, printed pp.1146–1147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open ChapterA.Section05To06 ChapterG.Section02
open OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
  (hempty : MainForward.faithfulLocalComponents d.T = ∅)
  (hM : IsOrderingMaximal d.T d.M)
  (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
  (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
  (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
include hG hempty hM hu hmany hfixed hnon

theorem original_sylow_square_mem (t : G) (ht : t ∈ d.T) :
    t^2 ∈ closureU d.Z d.ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) := by
  have h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hi := nonabelian_span_centralizer_index d (centralizerH d.Z) h
    (original_U_nonabelian hG d hempty hM hu hmany hfixed hnon)
  exact ((closureU d.Z d.ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G))).subgroupOf
    (d.T : Subgroup G)).sq_mem_of_index_two hi ⟨t,ht⟩

theorem original_sylow_square_normalizes (A : Subgroup G) (hAV : A ≤ d.V)
    (hUA : closureU d.Z d.ZS ≤ normalizer (A : Set G))
    (t : G) (ht : t ∈ d.T) : t^2 ∈ normalizer (A : Set G) := by
  exact (sup_le hUA (inf_le_right.trans ((centralizer_le hAV).trans
    (Subgroup.centralizer_le_normalizer _))))
    (original_sylow_square_mem hG d hempty hM hu hmany hfixed hnon t ht)

theorem original_partner_square_normalizes_plane
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g)
    (y : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).I g)
    (hy : (y : G) ∈ PartnerGeometry.leftResidual h26)
    (hyc : PartnerGeometry.matrixSection h26 y = PartnerGeometry.MatrixOrbit.leftCubic)
    (t : G) (ht : t ∈ d.T) :
    t^2 ∈ normalizer (localSpan d.Z (PartnerGeometry.leftResidual h26) : Set G) := by
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hp := (PartnerGeometry.selected_plane h26 y hy hyc).2.1
  have hn := PartnerGeometry.selected_pair_normalizes_plane h26 y hy hyc
  rw [Chapter15.I_eq _ hh.1 inf_le_right] at hn
  exact original_sylow_square_normalizes hG d hempty hM hu hmany hfixed hnon _
    (hp.trans inf_le_left) (le_sup_left.trans hn) t ht

theorem original_partner_square_normalizes
    (g : G) (h26 : Hypothesis (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T) g)
    (y : (Chapter15.setup d.Z (d.V ⊓ closureU d.Z d.ZS) d.Y d.T).I g)
    (hy : (y : G) ∈ PartnerGeometry.leftResidual h26)
    (hyc : PartnerGeometry.matrixSection h26 y = PartnerGeometry.MatrixOrbit.leftCubic)
    (t : G) (ht : t ∈ d.T) :
    t^2 ∈ normalizer (intersectionE d.Z d.ZS (y : G) : Set G) := by
  have hh := original_pair_hyperplane hG d hempty hM hu hmany hfixed hnon
  have hs := original_residual_span hG d hempty hM hu hmany
  obtain ⟨sg⟩ := PartnerGeometry.selected_geometry hh.1 inf_le_right hs h26 rfl y hy hyc
  exact sg.E_normalizer (original_partner_square_normalizes_plane
    hG d hempty hM hu hmany hfixed hnon g h26 y hy hyc t ht)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
