module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PerpendicularKernel
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.TransverseUpper
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.TransverseLower

/-!
# The actual complementary source-56 intersections

The elementary partner planes place E∩Eᵗ in the old pair core. Both cubic
residual factors then kill its image modulo V; the marked determinant
perpendicular calculation cuts the remaining natural-space intersection
to Z. All midpoint statements are constructed on the same selected pair.
Source: Aschbacher–Smith 15.3.56(5), printed p.1148.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor ClassicalOrthogonal.FourPlusMatrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]

/-- The selected original E and its exchanged conjugate intersect precisely
in the original central involution subgroup. -/
theorem selected_intersection_conjugate_eq_point
    (d : CharacteristicTwo.LocalData G) (Zperp : Subgroup G) (g : G)
    (hZS : d.ZS ≤ Zperp) (hperp : Zperp = d.V ⊓ closureU d.Z d.ZS)
    (hspan : localSpan d.Z d.Y = d.V)
    (h26 : Hypothesis (Chapter15.setup d.Z Zperp d.Y d.T) g)
    (hΩ : omegaCenter d.T = d.Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup d.Z Zperp d.Y d.T) g).subgroupOf
      ((Chapter15.setup d.Z Zperp d.Y d.T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup d.Z Zperp d.Y d.T) g)]
    (f : SourceModuleData h26)
    (hmark : ∀ v : (Chapter15.setup d.Z Zperp d.Y d.T).VL,
      determinantForm (h26.coordinates v).toAdd =
        FusionCore.orthogonalCoordinateValue
          (d.action.coordinates ((MulEquiv.subgroupCongr hspan) v)))
    (y : (Chapter15.setup d.Z Zperp d.Y d.T).I g)
    (hy : (y : G) ∈ leftResidual h26)
    (hyc : matrixSection h26 y = MatrixOrbit.leftCubic)
    (t : G) (ht : t ∈ d.T)
    (hex : conjugate (leftResidual h26) t = rightResidual h26)
    (hjoin : localSpan d.Z (leftResidual h26) ⊔
      rightConjugate (localSpan d.Z (leftResidual h26)) t = Zperp) :
    intersectionE d.Z d.ZS (y:G) ⊓ rightConjugate (intersectionE d.Z d.ZS (y:G)) t = d.Z := by
  let D := Chapter15.setup d.Z Zperp d.Y d.T
  let V₀ := localSpan d.Z (leftResidual h26)
  have hperpU : Zperp ≤ closureU d.Z d.ZS := hperp.symm ▸ inf_le_right
  have hu : D.U = closureU d.Z d.ZS := Chapter15.closure_eq hZS hperpU
  have hUH : closureU d.Z d.ZS ≤ centralizerH d.Z := hu ▸ h26.base.U_le_H
  have hZH : d.ZS ≤ centralizerH d.Z := (hZS.trans hperpU).trans hUH
  have hp : IsPGroup 2 (closureU d.Z d.ZS) := hu ▸ U_isPGroup h26.base h26.closure
  have hf : (frattini (closureU d.Z d.ZS)).map (closureU d.Z d.ZS).subtype ≤ d.Z := by
    have hh := h26.closure.frattini
    rw [hu] at hh
    exact hh
  obtain ⟨hplane,hV₀V,hcard,hyn,hdis⟩ := selected_plane h26 y hy hyc
  have hl := rank_one_intersection_layer d.Z d.ZS V₀ (y:G) hZH hp hf hplane
    (hV₀V.trans hperpU) hyn hdis
  have hE := intersectionE_eq d.Z d.ZS V₀ (y:G) hZH hplane hyn
  have hZE : d.Z ≤ intersectionE d.Z d.ZS (y:G) :=
    (le_conjugateSpanBy _ _).trans hl.1
  have hcore := intersectionE_transverse_le_core h26 d.Z d.ZS (y:G) t hu.symm
    hl.1 hl.2.2.2.2 hjoin
  have hYJ : leftResidual h26 ≤ pairI d.Z d.ZS (y:G) := by
    rw [← Chapter15.I_eq (y:G) hZS hperpU,
      selected_pair_eq_residual_join h26 y hy hyc]
    exact le_sup_left
  have hcomm : ⁅intersectionE d.Z d.ZS (y:G),leftResidual h26⁆ ≤ D.VL :=
    ((commutator_mono le_rfl hYJ).trans hl.2.2.2.1).trans
      (hV₀V.trans h26.V_le_VL)
  have hΩV : omegaCenter D.T ≤ D.VL := by
    change omegaCenter d.T ≤ D.VL
    rw [hΩ]
    exact point_le_VL D
  have hupper := partner_intersection_le_natural h26 f hΩV
    (intersectionE d.Z d.ZS (y:G)) t ht hcore hcomm hex
  change intersectionE d.Z d.ZS (y:G) ⊓ rightConjugate (intersectionE d.Z d.ZS (y:G)) t ≤
    localSpan d.Z d.Y at hupper
  rw [hspan] at hupper
  have hyM : (y:G) ∈ d.M :=
    Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc (leftResidual_le_L h26 hy)
  exact source_intersection_conjugate_eq_point d Zperp g h26 hspan hmark hperp V₀
    (y:G) t hyM ht hE hZE hplane hjoin hupper

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
