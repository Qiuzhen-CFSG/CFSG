module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedUse
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.QuotientPlanes
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.NaturalPartner
public import Theory.GroupTheory.SubgroupAutomorphismImages

/-!
# Recognition and fusion from one selected paired datum

The actual polar coordinates feed both the source fixed-line and extraspecial
fields and the final marked partner. Every scalar and ordinary geometric
field is derived from the same selected cubic and common source module.
Source: Aschbacher–Smith, 15.3.56–59, pp.1147–1150.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open Core.ResidualGeneration
variable {G : Type*} [Group G] [Finite G]
  {Z ZS Zperp V Y T : Subgroup G} {g : G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The selected coordinate datum discharges every source56 field required
by the final original-scope consumer, with the same y and t throughout. -/
theorem selected_source56_inputs
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
    (t : centralizerH Z) (ht : (t:G)∈T)
    (hout : (t:G)∉closureU Z ZS ⊔ (T ⊓ centralizer (V:Set G)))
    (hcap : intersectionE Z ZS (y:G) ⊓ rightConjugate (intersectionE Z ZS (y:G)) (t:G)=Z)
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (hZ : Z≤ZS) (hlinecard : Nat.card (distinguishedLine Z ZS)=2)
    (hseed : ⁅ZS,T⁆≤Z) (hVQ : V ⊓ coreQ Z=Zperp)
    (hVstar : Nat.card (Recognition.actorImage Z V)=2)
    (b : PairedCoordinates.Data Z ZS (localSpan Z (leftResidual d)) (y:G) t hk) :
    ∃ r56 : RecognitionFields T Z ZS V f.decomposition.leftMultiplicity,
      r56.Y₁ ≤ Y ∧
      (f.decomposition.leftMultiplicity=1 → ∀r:RecognizedAction T Z ZS V r56.t,
        Nonempty {p : Partner.EarlierGeometry T Z ZS V r56.Y₁ r56.y r56.t // p.recognized=r}) := by
  have hu : (Chapter15.setup Z Zperp Y T).U=closureU Z ZS :=
    Chapter15.closure_eq hZS hperp
  have hVX : Recognition.actorImage Z V ≤ Recognition.actorImage Z (partnerX Z ZS (y:G)) := by
    have hh := natural_actor_le_partner d Z ZS rfl hu y hyc
      (by change localSpan Z Y ⊓ coreQ Z=Zperp; rw [hspan]; exact hVQ)
      (by simpa only [Chapter15.VL_eq hspan] using hVstar)
    simpa only [Chapter15.VL_eq hspan] using hh
  have hdim := literal_vector_dimension hZS hperp hspan d hΩ f hsame
  have hplanes := selected_quotient_planes hZS hperp hspan d hΩ f hsame y hy hy3 hyc (t:G) ht hcap
  obtain ⟨a⟩ := ExtraspecialAction.selected_action_data hZS hperp hspan d hΩ f hsame y hy hy3 hyc hk
  have hVN : (t:G)∈normalizer (V:Set G) := by
    rw [← hspan]
    exact normalizer_inf_le_normalizer_conjugateSpan Z Y
      ⟨d.base.T_normalizes_point ht,d.base.T_normalizes_L ht⟩
  have hVH : V≤centralizerH Z := by
    let : IsElementaryAbelian 2 (localSpan Z Y) := d.VL_elementary
    rw [← hspan]
    exact (localSpan Z Y).le_centralizer.trans (centralizer_le (le_conjugateSpanBy Z Y))
  let r56 : RecognitionFields T Z ZS V f.decomposition.leftMultiplicity := {
    Y₁ := leftResidual d
    y := (y:G)
    t := (t:G)
    X_le_T := a.X_le_T
    t_mem_T := ht
    t_outside := hout
    fixed_line := b.fixed_line T a.X_le_T ht hseed hlinecard
    dimension := hdim
    Vstar_le_Xstar := hVX
    elementary := a.actor_elementary
    card_actor := a.actor_card
    extraspecial_product := b.extraspecial_product V hVH hVN hVX hVstar
      f.decomposition.leftMultiplicity hplanes.2.1 }
  refine ⟨r56,leftResidual_le_L d,?_⟩
  intro hone r
  have he3 : Module.finrank (ZMod 2) (PairedCoordinates.ESpace Z ZS (y:G))=3 := by
    rw [hplanes.2.1,hone]
  obtain ⟨marked⟩ := b.marked he3
  exact selected_earlierGeometry_of_marked hZS hperp hspan d hΩ f hsame y hy hy3 hyc hyout
    (t:G) hk hZ b.X_le_H marked (b.actor_pair_card he3) r

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
