module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction.Source
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedGeometry
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner

/-!
# The literal selected earlier-partner record

The selected cubic and its geometric and action conclusions supply all
ordinary group fields of the final partner record. The remaining paired
marking and order-eight actor are passed on their literal quotient maps;
the independent recognized action is retained unchanged.

Source: Aschbacher–Smith, 15.3.56 and 15.3.59, pp.1147–1150.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
open Core.ResidualGeneration
variable {G : Type*} [Group G] [Finite G]
  {Z ZS Zperp V Y T : Subgroup G} {g : G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- Every field except the independently produced marking and pair order
is constructed from the selected source pair. -/
theorem selected_earlierGeometry_of_marked
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y:G)∈leftResidual d)
    (hy3 : orderOf y=3) (hyc : matrixSection d y=MatrixOrbit.leftCubic)
    (hyout : (y:G)∉(leftResidual d).pCoreIn 2)
    (t : G) (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (hZ : Z ≤ ZS) (hXH : partnerX Z ZS (y:G) ≤ centralizerH Z)
    (marked : Partner.MarkedAction Z ZS (localSpan Z (leftResidual d)) (y:G) t hXH)
    (hcard : Nat.card (CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.actorImage Z
      (partnerX Z ZS (y:G) ⊔ rightConjugate (partnerX Z ZS (y:G)) t))=8)
    (r : RecognizedAction T Z ZS V t) :
    Nonempty {p : Partner.EarlierGeometry T Z ZS V (leftResidual d) (y:G) t //
      p.recognized=r} := by
  obtain ⟨sg⟩ := selected_geometry hZS hperp hspan d hΩ y hy hyc
  obtain ⟨a⟩ := ExtraspecialAction.selected_action_data hZS hperp hspan d hΩ f hsame
    y hy hy3 hyc hk
  obtain ⟨S,hS⟩ := d.base.sylow_H
  have hu : (Chapter15.setup Z Zperp Y T).U=closureU Z ZS :=
    Chapter15.closure_eq hZS hperp
  have hUH : closureU Z ZS ≤ centralizerH Z := hu ▸ d.base.U_le_H
  have hU2 : IsPGroup 2 (closureU Z ZS) := hu ▸ U_isPGroup d.base d.closure
  have hUQ : closureU Z ZS ≤ coreQ Z := le_pCoreIn_of_normalizes hU2 hUH
    (H_normalizes_closureU Z ZS)
  exact ⟨⟨{
    sylow := S
    sylow_map := hS
    X_le_T := sg.X_le_T
    Z_le_ZS := hZ
    ZS_le_H := (hZS.trans hperp).trans hUH
    U_le_Q := hUQ
    X_inf_Q := a.X_inf_Q
    y_mem := hy
    y_outside := hyout
    V₀_eq := sg.V₀_eq
    V₀_le_U := sg.V₀_le_U
    J_normalizer := sg.J_normalizer
    E_normalizer := sg.E_normalizer
    J_core := sg.J_core
    actor_kernel := hk
    recognized := r
    marked := marked
    actor_pair_card := hcard },rfl⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
