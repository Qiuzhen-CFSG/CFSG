module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposablePartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSylowSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePreExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.PrimeSelection

/-!
# The original cubic decomposable component without global residual control

The actual factor action supplies the maximal Sylow image and hence the
original pair of maximal two-locals. Its central seed is the diagonal of
the two original Thompson four-groups. The marked partner centralizer is
therefore the centralizer of their full sixteen-element sum and is
T-invariant. These independent geometric facts supply the source component
selection while preserving the original marking, component and two
sixteen-element supports. No clause of global 15.1.14 is assumed.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original full prime-three decomposable source produces the marked
component, its pre-exclusion witness and its exchanged-plane source,
without the earlier global residual premise. -/
theorem PreparedChosenModule.decomposable_three_exchanged_without_residual
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
        normalizer ((pResidual 2 e.MZ).map e.MZ.subtype : Set G) ≤ Mc := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hthree
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun E hE => hE.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  have hpair := h.decomposable_three_maximal_overgroups hG T hempty hM hJ hu
    c d s π hp hs hdec hthree
  have hMc := (h.decomposable_three_partner_centralizer hG T hempty hM hJ hu hne
    rfl c d s π hp hs hdec hthree).1
  obtain ⟨m,hZ,hp3,hrow,hplanes⟩ := s.preExclusionMarker_of_prime_three
    hG T hM rfl h.normalized c d hd π hp hs he hthree
  have hTn : (T : Subgroup G) ≤ normalizer (centralizer (m.Z1 : Set G) ⊓ Mc : Set G) := by
    rw [hZ,inf_comm]
    exact (s.marked_partner_centralizer_of_prime_three hG T hM h rfl hMc
      c d hd π hp hs hthree).2.2
  obtain ⟨e,heZ,herow,hsource,hNY⟩ := h.component_of_preExclusionMarker_of_pair
    hG T hempty hM hmany hJ hu hne rfl m hpair hTn
  have hsource3 : e.PreExclusionSource h.normalized 3 := (hp3.trans hthree) ▸ hsource
  have hgeometry := hplanes e heZ herow
  refine ⟨e,heZ.trans hZ,herow.trans hrow,?_,hsource3,hgeometry,
    hsource3.exchangedSource hG h hgeometry,hNY⟩
  rw [heZ,hZ]
  exact s.thompson_card s.first

end CFSG.Quasithin.Chapter15.Section01
