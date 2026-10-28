module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableOrdinary
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSixSource

/-!
# The actual cubic decomposable source at the six-point MS duty

The independently constructed original constrained component has no rank-one
block by its actual marked residual control. The selected FF reduction then
leaves the original six-point small MS pair or the binary-linear source.
The latter is impossible by the original natural-module contradiction.

This retains the original component, its marked four-group, both sixteen-element
supports, the original C.2.7 input and the exact quotient maps. Both the ordinary
six-point image and its cubic central cover remain. No whole-core six-point
reconstruction or global residual conclusion is asserted.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic decomposable action reaches the actual marked small
six-point MS pair without assuming global residual centralization. -/
theorem PreparedChosenModule.decomposable_three_six_ms_source_without_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 3 →
      ∃ e : CaseIComponentData T M Mc V,
        e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space ∧
        e.row = .six ∧ Nat.card e.Z1 = 4 ∧
        e.PreExclusionSource h.normalized 3 ∧ e.ExchangedPlaneGeometry ∧
        e.ExchangedSource ∧
        generalizedFitting e.L = pCore 2 e.L ∧
        normalizer ((pResidual 2 e.MZ).map e.MZ.subtype : Set G) ≤ Mc ∧
        Input KnownSimple.IsKnownSimple e.G1 e.Q1 e.MZ e.L ∧
        SmallMSPair KnownSimple.IsKnownSimple e.L e.Q1 ∧
        (Nonempty (e.normalizerImage e.L ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (center (e.normalizerImage e.L) ≃* Multiplicative (ZMod 3))) ∧
        ∃ q : (e.normalizerImage e.L ⧸ center (e.normalizerImage e.L)) ≃*
            alternatingGroup (Fin 6),
          ∃ t : (e.L ⧸ centralPreimage (pCore 2 e.L)) ≃* alternatingGroup (Fin 6),
            ∀ k : e.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 e.L)) k) =
              q (QuotientGroup.mk' (center (e.normalizerImage e.L)) (e.toNormalizerImage e.L k)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hthree
  obtain ⟨e,heZ,herow,hecard,hepre,heplanes,hex,hf,hNY⟩ :=
    h.decomposable_three_constrained_without_residual
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hthree
  have hnot := hepre.no_rankOne_blocks_of_local_residual (h := h) (Or.inl rfl)
    hG hempty hM hJ hu hNY
  exact ⟨e,heZ,herow,hecard,hepre,heplanes,hex,hf,hNY,
    hepre.six_ms_of_local_source (h := h) hex hG hempty hM hmany hJ hu hne hfull hf hnot⟩

end CFSG.Quasithin.Chapter15.Section01
