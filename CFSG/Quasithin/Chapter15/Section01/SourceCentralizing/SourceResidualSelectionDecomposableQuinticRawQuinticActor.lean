module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction

/-!
# A noncentral quintic actor on the original raw component

The genuine five-group on the opposite support lies in the original marked
residual and normalizes the selected L. Its full displacement of that support
forces noncentrality on L. This uses neither ordinary componenthood nor a
quotient model, and retains the actual ambient actor.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The same original quintic actor acts nontrivially on the selected local group. -/
theorem PreparedChosenModule.decomposable_five_raw_noncentral_actor
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
      ∀ {L : Subgroup G},
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∃ Y : Subgroup G, IsPGroup 5 Y ∧ Y ≤ normalizer (L : Set G) ∧
          ¬ Y ≤ centralizer (L : Set G) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hnL hmove
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  obtain ⟨Y,hY,hperfect,hYA,_,_,_,_,hBY,_⟩ :=
    s.exists_permuting_quintic_actor hM.1.2 h.normalized h.le_selected c d π hp hs hJi hfive
  have hYC : Y ≤ C := hYA.trans (map_subtype_le _)
  have hYR : Y ≤ R := by
    have hh := embedded_pResidual_mono 2 hYC
    rw [(pResidual_eq_top_iff 2 Y).mpr hperfect,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hWB := (s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi).2.1
  have hWY : ⁅⁅localModule T M,R⁆,Y⁆ = ⁅localModule T M,R⁆ := by
    rw [hWB]
    exact hBY
  have hYN : Y ≤ normalizer (L : Set G) := hYR.trans (le_sup_left.trans hnL)
  refine ⟨Y,hY,hYN,?_⟩
  intro hYCen
  have hWN : ⁅localModule T M,R⁆ ≤ normalizer (L : Set G) := le_sup_right.trans hnL
  have hc : ⁅⁅localModule T M,R⁆,Y⁆ ≤ centralizer (L : Set G) := by
    rw [commutator_comm]
    exact (commutator_mono hYCen le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (hWN.trans (normalizer_le_normalizer_centralizer L)))
  rw [hWY] at hc
  exact hmove (by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc)

end CFSG.Quasithin.Chapter15.Section01
