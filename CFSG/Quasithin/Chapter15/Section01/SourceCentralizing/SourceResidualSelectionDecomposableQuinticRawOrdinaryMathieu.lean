module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.Mathieu.M11.Properties.ThreeInvolutions

/-!
# M₁₁ is excluded by the original faithful moving support

The ordinary component's possible central two-cover is retained. Perfect
central-cover descent embeds its original elementary sixteen in Aut(M₁₁),
contradicting the intrinsic two-rank bound. No new local placement is needed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual full quintic source cannot have ordinary core quotient M₁₁. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_not_mathieuEleven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
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
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hLG hLc hcenter hnL hmove
  rintro ⟨e⟩
  obtain ⟨hBL,_,hcard⟩ := h.decomposable_five_raw_moving_support_action
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive hnL hmove
  let B := plane V (c.ambientFactor d s.second).space
  let A := internalActionImage B L hBL
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (plane_le _)
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_surjective (actionHom B L hBL).rangeRestrict
      (actionHom B L hBL).rangeRestrict_surjective
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hsur : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',←hcenter]
  let cover : PerfectCentralCovering.Cover L Sporadic.Mathieu.M11 :=
    ⟨q,hsur,inferInstance,hk.le⟩
  have hb := (primeRank_le_iff_elementary_card_le (MulAut Sporadic.Mathieu.M11)).mp
    Sporadic.Mathieu.m11_automorphism_twoRank_le_two
    (A.map (cover.autMap hk)) (IsElementaryAbelian.map _)
  rw [card_map_of_injective (cover.autMap_injective hk),hcard] at hb
  norm_num at hb

end CFSG.Quasithin.Chapter15.Section01
