module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineConstrained
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SmallRemainder
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.Exclusion

/-!
# The exact six-point remainder on the original Nine component

The reduced FF catalogue is applied to the actual normalizer image.
The original rank-one, binary-three, G2 and seven-point exclusions leave
only the binary-linear source or the six-point central quotient. The latter
retains the original C.2.7 input, MS pair and elementwise quotient marking,
and distinguishes the ordinary image from its cubic-center covering row.

A cubic center in the FF image is not an exceptional block reconstruction.
Both six-point outcomes remain explicit; no whole-core reconstruction,
global residual centralization or completed source22 catalogue is assumed.

Source: Aschbacher--Smith 15.1.20--26, printed pp.1094--1102.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
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

/-- The actual FF image leaves a linear source or the precise ordinary/cubic
six-point MS remainder, with the original comparison maps preserved. -/
theorem PreExclusionSource.six_ms_or_exchanged_linear_of_no_rankOne
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 3) (x : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (hnot : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5)) :
    d.HasExchangedLinearSource ∨
      (Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
        (Nonempty (d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (center (d.normalizerImage d.L) ≃* Multiplicative (ZMod 3))) ∧
        ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
            alternatingGroup (Fin 6),
          ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
            ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
              e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k))) := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have rankOne (F : BinaryField) (e : d.normalizerImage d.L ≃* SL(2,F.Carrier)) : False :=
    hnot (d.localFamily_rankOne_block hG hempty hM hJ hu h hk s.quasisimple d.L_not_le_MZ hf F.Carrier e)
  have linear {n : ℕ} (hn : n = 4 ∨ n = 5)
      (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) : d.HasExchangedLinearSource := by
    obtain ⟨t,_,_,_,_,_⟩ := s.constrained_binary_linear (h := h) hG hempty hM hJ hu hf hn e
    exact ⟨x,hf,n,hn,⟨t⟩⟩
  have six (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) :
      Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
        ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
          ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
            e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) := by
    obtain ⟨hi,_,_⟩ := s.constrained_alternating_star_comparison (h := h)
      hG hempty hM hJ hu hf (by decide) e
    obtain ⟨hm,t,ht⟩ := s.constrained_six_msPair (h := h) hG hempty hM hJ hu hf e
    exact ⟨hi,hm,t,ht⟩
  cases s.constrained_reduced_ff_model (h := h) hG hempty hM hJ hu hf with
  | linearTwo F e => exact (rankOne F e).elim
  | linearThree e =>
    exact (x.not_constrained_binaryThree_of_preExclusion (h := h) s
      hG hempty hM hJ hu hfull hf ⟨e⟩).elim
  | g2DerivedTwo e =>
    exact (x.not_constrained_g2_of_preExclusion (h := h) s
      hG hempty hM hJ hfull hu hf ⟨e⟩).elim
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact (rankOne BinaryField.four (e.trans fiveLinearEquiv)).elim
    · let c : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
          alternatingGroup (Fin 6) :=
        (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
          ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
            QuotientGroup.quotientBot)
      obtain ⟨hi,hm,t,ht⟩ := six c
      exact Or.inr ⟨hi,hm,Or.inl ⟨e⟩,c,t,ht⟩
    · obtain ⟨_,_,_,_,_,_,_,ha,_⟩ := s.constrained_seven (h := h) hG hempty hM hJ hu hf e
      exact (x.no_constrained_a7 hG hM.1.2 h ha).elim
    · exact Or.inl (linear (Or.inl rfl) (e.trans
        (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm)))
  | linearFiveTwo e => exact Or.inl (linear (Or.inr rfl) e)
  | tripleSix z e =>
    obtain ⟨hi,hm,t,ht⟩ := six e
    exact Or.inr ⟨hi,hm,Or.inr ⟨z⟩,e,t,ht⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
