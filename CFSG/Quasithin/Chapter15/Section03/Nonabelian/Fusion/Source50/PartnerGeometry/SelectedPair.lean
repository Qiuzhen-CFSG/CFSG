module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.RankOneCore
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.RankOneGeneration
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Multiplicity
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Exchange

/-!
# The selected source-56 pair and its order

The original cubic choice supplies all rank-one inputs of the multiplicity
comparison on the same G.2.6 witness. Thus the order of E and the transverse
factor exchange retain no independent local quotient or chief-length premise.
Source: Aschbacher–Smith 15.3.56(2–5), printed pp.1147–1148.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]
  {Z ZS Zperp V Y T : Subgroup G} {g : G}

/-- The actual selected pair has symmetric-three quotient, the correct plane
centralizer core, the index-two comparison, and core containment in T. -/
theorem literal_selected_core
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    Nonempty ((pairI Z ZS (y:G) ⧸ pCore 2 (pairI Z ZS (y:G))) ≃* S₃) ∧
      pairP Z ZS (y:G) = pairI Z ZS (y:G) ⊓
        centralizer (localSpan Z (leftResidual d) : Set G) ∧
      (pairP Z ZS g ⊓ pairI Z ZS (y:G)).relIndex (pairP Z ZS (y:G)) = 2 ∧
      pairP Z ZS (y:G) ≤ T := by
  let D := Chapter15.setup Z Zperp Y T
  have hJ : D.I (y:G)=pairI Z ZS (y:G) := Chapter15.I_eq _ hZS hperp
  obtain ⟨he,hcore,hbridge⟩ := selected_rank_one_core d y hy hyc
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  have hT := selected_pair_core_le_T d z hz y hyc
  change (D.I (y:G)).pCoreIn 2 = _ at hcore
  change (D.S g ⊓ D.I (y:G)).relIndex ((D.I (y:G)).pCoreIn 2) = 2 at hbridge
  rw [hJ] at he hcore hT
  rw [Chapter15.S_eq g hZS hperp,hJ] at hbridge
  exact ⟨he,hcore,hbridge,hT⟩

/-- The chosen cubic has E of order 2^(s+3), with every midpoint premise
proved from this same h26 and its canonical source module. -/
theorem selected_intersectionE_card
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y : G) ∈ leftResidual d)
    (hy3 : orderOf y=3) (hyc : matrixSection d y=MatrixOrbit.leftCubic) :
    Nat.card (intersectionE Z ZS (y:G))=2^(f.decomposition.leftMultiplicity+3) := by
  obtain ⟨hplane,hplaneV,hcard,hyn,hdis⟩ := selected_plane d y hy hyc
  obtain ⟨⟨e⟩,hcore,hbridge,_⟩ := literal_selected_core hZS hperp d y hy hyc
  have hyJ := selected_y_mem_pair d y hy hyc
  rw [Chapter15.I_eq _ hZS hperp] at hyJ
  exact literal_intersectionE_card hZS hperp hspan d hΩ f hsame y hy3 hyc
    (localSpan Z (leftResidual d)) hplane (hplaneV.trans hperp) hyn hdis hcard hyJ
    e hcore hbridge

/-- The same selected pair provides the actual outside factor exchange. -/
theorem selected_exchanging_partner
    {M : Subgroup G} (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y=MatrixOrbit.leftCubic) :
    ∃ t ∈ T, conjugate (leftResidual d) t = rightResidual d ∧
      t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) ∧
      localSpan Z (leftResidual d) ⊔ conjugate (localSpan Z (leftResidual d)) t = Zperp := by
  have hnorm := selected_pair_normalizes_plane d y hy hyc
  have h := literal_exchanging_partner a hTM hSyl hspan d (le_sup_left.trans hnorm)
  rw [Chapter15.closure_eq hZS hperp] at h
  exact h

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
