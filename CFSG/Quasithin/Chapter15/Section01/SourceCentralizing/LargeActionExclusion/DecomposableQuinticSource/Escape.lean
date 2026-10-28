module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Core
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticActor

/-!
# The original marked centralizer escapes the partner

The actual partner normalizes the original Thompson fixed subgroup. If the
marked centralizer lay in the partner, its opposite quintic actor would
preserve the second Thompson four-group, as the intersection of its moving
support with the fixed subgroup. Irreducibility on the sixteen-element
support excludes that proper nontrivial invariant subgroup.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal marked centralizer escapes the actual partner for every
quintic partner-module size. -/
theorem PreparedChosenModule.decomposable_five_marked_centralizer_not_le
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
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ¬ M⊓centralizer (thompsonPlane T V (c.ambientFactor d s.first).space:Set G)≤Mc := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  let V := localModule T M
  let E := thompsonFixed T V
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let C := M⊓centralizer (Z₁:Set G)
  let Y := (primeToResidual 5 C).map C.subtype
  intro hCMc
  have hNE : normalizer (E : Set G) = Mc :=
    h.decomposable_five_fixed_normalizer_eq_partner
      hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  have hYC : Y ≤ C := map_subtype_le _
  have hYE : Y ≤ normalizer (E : Set G) :=
    (hYC.trans hCMc).trans_eq hNE.symm
  have hmove := (s.quintic_actor_geometry hM.1.2 h.normalized c d π hp hs hJi hfive).2.2.1
  have hYB : Y ≤ normalizer (plane V (c.ambientFactor d s.second).space : Set G) := by
    rw [←hmove]
    exact normalizer_commutator_ge_right V Y
  have hYZ₂ : Y ≤ normalizer (Z₂ : Set G) :=
    (le_inf hYB hYE).trans inf_normalizer_le_normalizer_inf
  rcases s.quintic_actor_irreducible hM.1.2 h.normalized c d π hp hs hJi hfive
      Z₂ inf_le_left hYZ₂ with hz | hz
  · have hc := s.thompson_card s.second
    change Nat.card Z₂=4 at hc
    rw [hz,card_bot] at hc
    omega
  · have hc := s.thompson_card s.second
    change Nat.card Z₂=4 at hc
    rw [hz,s.support_card] at hc
    omega

end CFSG.Quasithin.Chapter15.Section01
