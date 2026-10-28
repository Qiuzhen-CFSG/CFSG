module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Core

/-!
# Source-56 partner action assembly

The selected cubic retains the same G.2.6 witness and source module as the
multiplicity proof. Earlier closure data provide U ≤ O₂(H) and the literal
commutator bound [U,O₂(H)] ≤ Z. The preceding group and action modules then
assemble the actual X containment, elementary actor, center centralizer and
full transvection image.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction
open Recognition LocalRestrictions
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]

private theorem source_commutator_bound {D : Setup G} {g : G} (d : Hypothesis D g) :
    ⁅D.U,D.QH⁆ ≤ D.V₁ := by
  apply commutator_le.mpr
  intro a ha b hb
  let a₁ : D.G₁ := ⟨a,d.base.H_le (d.base.U_le_H ha)⟩
  let b₁ : D.G₁ := ⟨b,d.base.H_le (pCoreIn_le 2 D.H hb)⟩
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
  have ha' : q a₁ ∈ D.tilde D.U := ⟨a₁,ha,rfl⟩
  have hb' : q b₁ ∈ D.tilde D.QH := ⟨b₁,hb,rfl⟩
  have hc := omegaOneAmbient_le _ (d.closure.central.2 ha')
  obtain ⟨z,hz,hze⟩ := hc
  have hh := congrArg Subtype.val (mem_center_iff.mp hz (⟨q b₁,hb'⟩:D.tilde D.QH))
  change q b₁*(z:D.Tilde)=(z:D.Tilde)*q b₁ at hh
  change (z:D.Tilde)=q a₁ at hze
  rw [hze] at hh
  have hcomm : q ⁅a₁,b₁⁆=1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hh.symm
  have hm := (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.G₁) ⁅a₁,b₁⁆).mp hcomm
  exact hm

variable (T Z ZS V₀ : Subgroup G) (y : G) (s : ℕ)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))

/-- The actual source partner, its actor image, and its full action on E/Z.
All markings use the original subgroup inclusions and recognition action. -/
structure Data where
  X_le_T : partnerX Z ZS y ≤ T
  X_inf_Q : partnerX Z ZS y ⊓ coreQ Z=intersectionE Z ZS y
  actor_elementary : IsElementaryAbelian 2 (actorImage Z (partnerX Z ZS y))
  actor_card : Nat.card (actorImage Z (partnerX Z ZS y))=2^(s+1)
  centralizer_eq : intersectionE Z ZS y ⊓ centralizer (partnerX Z ZS y:Set G)=V₀
  centerVector : vectorSubspace Z ZS (intersectionE Z ZS y)
  center_ne_zero : (centerVector:Space Z ZS) ≠ 0
  center_span : Submodule.span (ZMod 2) {(centerVector:Space Z ZS)}=vectorSubspace Z ZS V₀
  is_transvection : ∀ x : actorImage Z (partnerX Z ZS y),
    ∃ φ : Module.Dual (ZMod 2) (vectorSubspace Z ZS (intersectionE Z ZS y)), φ centerVector=0 ∧
      ∀ e : vectorSubspace Z ZS (intersectionE Z ZS y),
        actorRepresentation Z ZS hk x e=(e:Space Z ZS)+φ e • (centerVector:Space Z ZS)
  full : ∀ φ : Module.Dual (ZMod 2) (vectorSubspace Z ZS (intersectionE Z ZS y)), φ centerVector=0 →
    ∃ x : actorImage Z (partnerX Z ZS y),
      ∀ e : vectorSubspace Z ZS (intersectionE Z ZS y),
        actorRepresentation Z ZS hk x e=(e:Space Z ZS)+φ e • (centerVector:Space Z ZS)

variable {T Z ZS V₀ y s hk} {Zperp V Y : Subgroup G} {g : G}

/-- Source 15.3.56(4) for the very same selected cubic and source multiplicity.
The only action-kernel input is the genuine preceding 15.3.48 kernel theorem;
the group orders, rank-one geometry and full transvection image are proved. -/
theorem selected_action_data
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y:G)∈leftResidual d)
    (hy3 : orderOf y=3) (hyc : matrixSection d y=MatrixOrbit.leftCubic)
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z)) :
    Nonempty (Data T Z ZS (localSpan Z (leftResidual d)) (y:G)
      f.decomposition.leftMultiplicity hk) := by
  let D := Chapter15.setup Z Zperp Y T
  let V₀ := localSpan Z (leftResidual d)
  have hu : D.U=closureU Z ZS := Chapter15.closure_eq hZS hperp
  have hUH : closureU Z ZS ≤ centralizerH Z := hu ▸ d.base.U_le_H
  have hZH : ZS ≤ centralizerH Z := (hZS.trans hperp).trans hUH
  have hU2 : IsPGroup 2 (closureU Z ZS) := hu ▸ U_isPGroup d.base d.closure
  have hf : (frattini (closureU Z ZS)).map (closureU Z ZS).subtype ≤ Z := by
    have hh := d.closure.frattini
    rwa [hu] at hh
  have hUQ : closureU Z ZS ≤ coreQ Z := le_pCoreIn_of_normalizes hU2 hUH
    (H_normalizes_closureU Z ZS)
  have hcomm : ⁅closureU Z ZS,coreQ Z⁆ ≤ Z := by
    have hh := source_commutator_bound d
    rw [hu] at hh
    exact hh
  obtain ⟨hplane,hplaneV,hcard,hyn,hdis⟩ := selected_plane d y hy hyc
  change V₀=Z ⊔ rightConjugate Z (y:G) at hplane
  have hVU : V₀ ≤ closureU Z ZS := hplaneV.trans hperp
  have hl := rank_one_intersection_layer Z ZS V₀ (y:G) hZH hU2 hf hplane hVU hyn hdis
  let := hl.2.2.2.2
  obtain ⟨hex,hcenter,_⟩ := PairGeometry.literal_extraspecial hZS hperp hspan d hΩ
  let := hex
  have hUcard := literal_closure_card hZS hperp hspan d hΩ f hsame
  have hEcard := selected_intersectionE_card hZS hperp hspan d hΩ f hsame y hy hy3 hyc
  obtain ⟨hkernel,helem,hactor,hcentral,hderived⟩ :=
    partner_group_action_data Z ZS V₀ (y:G) f.decomposition.leftMultiplicity hcenter
      hZH d.point_card hplane hVU hyn hdis hcard hUQ hcomm hUcard hEcard
  obtain ⟨⟨e⟩,hcore,_,hKT⟩ := literal_selected_core hZS hperp d y hy hyc
  have hyJ := selected_y_mem_pair d y hy hyc
  rw [Chapter15.I_eq _ hZS hperp] at hyJ
  have hZyU : rightConjugate Z (y:G) ≤ closureU Z ZS :=
    (show rightConjugate Z (y:G) ≤ V₀ by rw [hplane]; exact le_sup_right).trans hVU
  have hi := intersectionF_index Z ZS (y:G) hcenter d.point_card hZyU hdis
  have hK := partner_core_product Z ZS V₀ Y T (y:G) hZH hplane hcore hyJ e hi
  have hXT : partnerX Z ZS (y:G) ≤ T := (hK ▸ le_sup_right).trans hKT
  have hXH : partnerX Z ZS (y:G) ≤ centralizerH Z :=
    (partner_le_plane_centralizer Z ZS V₀ (y:G) hZH hplane hyn).trans
      (centralizer_le (show Z ≤ V₀ by rw [hplane]; exact le_sup_left))
  obtain ⟨v,hv,hline,htrans,hfull⟩ := full_center_transvections Z ZS hk V₀ (y:G)
    hXH hplane hVU hdis d.point_card hcard hderived hcentral
  exact ⟨⟨hXT,hkernel,helem,hactor,hcentral,v,hv,hline,htrans,hfull⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction
