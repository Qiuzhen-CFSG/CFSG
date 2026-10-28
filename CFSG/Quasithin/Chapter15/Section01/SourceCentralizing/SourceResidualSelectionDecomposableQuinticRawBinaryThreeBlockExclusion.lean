module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryThreeBlock
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawQuinticActor
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.BinaryLinearThreeQuintic

/-!
# The actual original quintic binary-three star exclusion

The literal C.2.7 star row reconstructs the whole original binary-three
block. The actual noncentral five-group on the opposite source support
normalizes that same L. Native quintic centralization of the full block
contradicts its noncentrality. No component replacement, Case-I record,
whole-M generation, or global residual-centralization premise is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original full quintic source excludes the actual binary-three C.2.7
star on the same component, preserving its radical and marked intersection. -/
theorem PreparedChosenModule.decomposable_five_raw_not_binaryThree_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      ∀ {L : Subgroup G},
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        Z1 ≤ thompsonFixed T V →
        Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ G1) G1 →
        Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ G1) ⊓ L) L →
        (G1 ⊓ Mc).pCoreIn 2 ≠ ⊥ →
        (T : Subgroup G) ≤ normalizer ((G1 ⊓ Mc : Subgroup G) : Set G) →
        ∀ (_hi : Input KnownSimple.IsKnownSimple G1 ((G1 ⊓ Mc).pCoreIn 2) (G1 ⊓ Mc) L),
          ¬ Nonempty (starImage L ((G1 ⊓ Mc).pCoreIn 2) L ≃* Matrix.PSL3Two.SL) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hnL hmove hZ hsyl hSL hQne hTn hi he
  obtain ⟨e⟩ := he
  have hb := h.raw_binaryThree_block_of_original_input hG T hM.1.2 hu hZ
    hsyl hSL hQne hTn hi e
  obtain ⟨Y,hY,hYn,hYc⟩ := h.decomposable_five_raw_noncentral_actor
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive hnL hmove
  exact hYc (hb.quintic_centralizes hY hYn)

end CFSG.Quasithin.Chapter15.Section01
