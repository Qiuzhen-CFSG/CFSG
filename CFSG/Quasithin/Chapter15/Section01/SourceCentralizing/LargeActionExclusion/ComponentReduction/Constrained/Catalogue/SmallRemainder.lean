module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeInput
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryGraphFour
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenPartition.Membership
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Geometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneImage

/-!
# Assembly of the completed constrained rows with the small MS remainder

The reduced FF catalogue is now consumed case by case. Rank-one images
supply their actual Borel and Thompson clauses; A₇ supplies its literal
partition, placement and generation; the binary linear rows supply the
same marked parabolics and generation; G₂ supplies its actual block and
residual-centralizer identity.

Only binary SL₃ and the ordinary or cubic A₆ image remain in this reduction.
Each carries the genuine C.2.7 input and all MS-pair conditions on L,Q₁.
Their quotient markings agree elementwise with the original FF maps.
In particular the six-point row retains the central quotient, so this
reduction does not discard the cubic cover or assert a natural A₆ block.

The actual original-marker application works at both source primes and
keeps original 15.1.14 explicit. Completing the small-block clauses and the
full seven-row source contract, and proving general local-family Borel
placement, remain with the catalogue assembly. This reduction is not an
exhaustiveness theorem for ConstrainedAlternatives.

Source: Aschbacher--Smith 15.1.20(2) and15.1.22, printed pp.1094--1100.
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

/-- All reduced FF rows except binary-three and the two six-point rows
already satisfy the constrained alternatives. The remaining rows carry the
actual C.2.7 input, every MS condition and their original quotient markings.
This is a reduction, not the missing small-block geometry theorem. -/
theorem PreExclusionSource.constrained_catalogue_or_small_ms
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedAlternatives ∨
      (Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
        ((∃ e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL,
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
            ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∨
        (∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
          ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
            ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
              e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k))))) := by
  have six (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) :=
    s.constrained_six_msPair (h := h) hG hempty hM hJ hu hf e
  have sixInput (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L := by
    have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
    exact (s.constrained_alternating_central_input (h := h) hG hu hf (by decide)
      ((a.coreCenterQuotientEquiv s.quasisimple).trans e)).2
  cases s.constrained_reduced_ff_model (h := h) hG hempty hM hJ hu hf with
  | linearTwo F e =>
    exact Or.inl (.rankOne (s.constrained_rankOne_of_ff_image (h := h)
      hG hempty hM hJ hu hne hmany hres hf F.Carrier e))
  | linearThree e =>
    obtain ⟨hi,hm,t,ht,_⟩ := s.constrained_binaryThree_inputs (h := h)
      hG hempty hM hJ hu hf e
    exact Or.inr ⟨hi,hm,Or.inl ⟨e,t,ht⟩⟩
  | g2DerivedTwo e =>
    exact Or.inl (s.constrained_g2 (h := h) hG hempty hM hJ hfull hu hf e).2.2.2
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact Or.inl (.rankOne (s.constrained_rankOne_of_ff_image (h := h)
        hG hempty hM hJ hu hne hmany hres hf BinaryField.four.Carrier (e.trans fiveLinearEquiv)))
    · let c : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
          alternatingGroup (Fin 6) :=
        (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
          ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
            QuotientGroup.quotientBot)
      obtain ⟨hm,t,ht⟩ := six c
      exact Or.inr ⟨sixInput c,hm,Or.inr ⟨c,t,ht⟩⟩
    · obtain ⟨t,ht,π,hP,hSL,hplace,hproper,ha,hcat⟩ :=
        s.constrained_seven (h := h) hG hempty hM hJ hu hf e
      exact Or.inl hcat
    · obtain ⟨t,ht,hML,hM',hgen,hcat⟩ := s.constrained_binary_linear (h := h)
        hG hempty hM hJ hu hf (Or.inl rfl) (e.trans eightLinearEquiv)
      exact Or.inl hcat
  | linearFiveTwo e =>
    obtain ⟨t,ht,hML,hM',hgen,hcat⟩ := s.constrained_binary_linear (h := h)
      hG hempty hM hJ hu hf (Or.inr rfl) e
    exact Or.inl hcat
  | tripleSix z e =>
    obtain ⟨hm,t,ht⟩ := six e
    exact Or.inr ⟨sixInput e,hm,Or.inr ⟨e,t,ht⟩⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker reaches the assembled catalogue or one of
the two marked small MS rows. Both source primes and the earlier residual
hypothesis are retained; the remaining block clauses are not assumed. -/
theorem PreparedChosenModule.source_preExclusion_constrained_catalogue_or_small_ms
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.ConstrainedAlternatives ∨
          (Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
            SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
            ((∃ e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL,
              ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
                ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∨
            (∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
              ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
                ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
                  e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)))))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf => s.constrained_catalogue_or_small_ms (h := h)
    hG hempty hM hJ hu hne hmany hfull hres hf⟩

end CFSG.Quasithin.Chapter15.Section01
