module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceLargeChosenCatalogue
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineConstrained

/-!
# The selected-component catalogue from its own residual control

The source catalogue uses global residual centralization only to establish
its rank-one Borel bound. The normalizer bound for the literal residual
O²(M_Z) supplies that bound directly. Every other reduced FF row uses its
original block construction, including the actual six-point MS pair and
its central seed. This retains the same selected component throughout.

Source: Aschbacher--Smith 15.1.19--22, printed pp.1093--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private noncomputable def fiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm

private noncomputable def eightLinearEquiv :
    alternatingGroup (Fin 8) ≃* SL(4,ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm

/-- The actual constrained catalogue follows from normalization control
of its own marked residual, without global residual centralization. -/
theorem PreExclusionSource.constrained_catalogue_of_local_residual
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ConstrainedAlternatives := by
  have six (c : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) : d.ConstrainedAlternatives := by
    obtain ⟨hms,t,_⟩ := s.constrained_six_msPair (h := h) hG hempty hM hJ hu hf c
    have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
    have hi := (s.constrained_alternating_central_input (h := h) hG hu hf (by decide)
      ((a.coreCenterQuotientEquiv s.quasisimple).trans c)).2
    let e := t.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (F := ZMod 2) (by simp)).symm
    rcases hms.alternating_center_cases e with hz | hz
    · obtain ⟨he,hc,hm⟩ := naturalCore_of_distanceFour_knownSimple
        SixteenClosure.distanceFourInput_knownSimple G d.L d.Q1 hms e hz
      have hs := hms.short_of_core he hc s.quasisimple hm.alternating_six_irreducible
      have hb : IsAlternatingBlock d.L 6 := ⟨by decide,hs,hm⟩
      obtain ⟨_,_,_,_,_,_,_,_,_,_,ha⟩ :=
        s.constrained_six_of_block (h := h) hG hempty hM hJ hu hfull hb
      exact ha
    · have hx := s.original_cubic_coreExhaustion (h := h) hG hM.1.2 hu hi hms t hz
      obtain ⟨he,hc,hirr,h64,hfaith⟩ := core_facts_of_exhaustion hms e hz hx
      have hs := hms.short_of_core he hc s.quasisimple hirr
      have hb : IsExceptionalAhat6Block d.L :=
        ⟨hs,s.quasisimple,hz,
          ⟨(centralPreimageQuotientEquiv (pCore 2 d.L)).symm.trans t⟩,h64,hfaith⟩
      exact (s.not_constrained_exceptionalSix (h := h) hG hM hu hb).elim
  have noRankOne (F : Type) [Field F] [Finite F] [CharP F 2]
      (e : d.normalizerImage d.L ≃* Matrix.SpecialLinearGroup (Fin 2) F) : False :=
    s.no_rankOne_blocks_of_local_residual (h := h) hp hG hempty hM hJ hu hbound
      (d.localFamily_rankOne_block hG hempty hM hJ hu h
        ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf F e)
  cases s.constrained_reduced_ff_model (h := h) hG hempty hM hJ hu hf with
  | linearTwo F e => exact (noRankOne F.Carrier e).elim
  | linearThree e =>
    obtain ⟨_,_,_,_,_,_,ha⟩ := s.constrained_binaryThree (h := h)
      hG hempty hM hJ hu hfull hf e
    exact ha
  | g2DerivedTwo e =>
    exact (s.constrained_g2 (h := h) hG hempty hM hJ hfull hu hf e).2.2.2
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact (noRankOne BinaryField.four.Carrier (e.trans fiveLinearEquiv)).elim
    · exact six ((QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
        ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
          QuotientGroup.quotientBot))
    · obtain ⟨_,_,_,_,_,_,_,_,ha⟩ := s.constrained_seven (h := h)
        hG hempty hM hJ hu hf e
      exact ha
    · obtain ⟨_,_,_,_,_,ha⟩ := s.constrained_binary_linear (h := h)
        hG hempty hM hJ hu hf (Or.inl rfl) (e.trans eightLinearEquiv)
      exact ha
  | linearFiveTwo e =>
    obtain ⟨_,_,_,_,_,ha⟩ := s.constrained_binary_linear (h := h)
      hG hempty hM hJ hu hf (Or.inr rfl) e
    exact ha
  | tripleSix z e => exact six e

/-- The literal component-or-constrained alternative with only its local
marked residual-normalizer bound. -/
theorem PreExclusionSource.component_or_constrained_of_local_residual
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    : IsComponent d.G1 (d.L.subgroupOf d.G1) ∨ d.ConstrainedAlternatives := by
  rcases d.L_component.2.component_or_generalizedFitting_eq_pCore s.odd_core with hc | hf
  · exact Or.inl hc
  · have hfL : generalizedFitting d.L = pCore 2 d.L := by
      let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
      exact (map_generalizedFitting_equiv e).symm.trans
        ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e))
    exact Or.inr (s.constrained_catalogue_of_local_residual (h := h) hp hG hempty hM hJ hu hfull hbound hfL)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
