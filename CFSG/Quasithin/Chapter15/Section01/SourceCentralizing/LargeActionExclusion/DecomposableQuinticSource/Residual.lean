module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.FullCentralizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticActor

/-!
# The order-five full-centralizer residual

The full centralizer residual contains the opposite marked five-kernel.  If
the literal module-centralizer quotient has order five, the transported
faithful residual has the same order, so the containment is equality.  This
keeps the conclusion on the original action and does not identify a setwise
normalizer with a pointwise centralizer.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- An order-five literal quotient makes the full residual image exactly the
opposite marked five-kernel. -/
theorem ThompsonPair.full_image_residual_eq_marked_of_quotient_card_five
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (_π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (_hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (_π g k)).actor)
    (_hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (_π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5)
    (hcard :
      let Z := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let := caseI_module_centralizer_normal (Z1 := Z) hn
      Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) :
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace
      (imageRepresentation M V hn)
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    (pResidual 2 K).map K.subtype =
      (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  let P := (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap
  let Z := thompsonPlane T V (c.ambientFactor d s.first).space
  let C := M ⊓ centralizer (Z : Set G)
  have hW : plane V W = Z := plane_thompson_intersection hTM hn _
  have hKcard : Nat.card (pResidual 2 K) = 5 := by
    let qcard (A : Subgroup G) : ℕ :=
      let C := M ⊓ centralizer (A : Set G)
      letI := caseI_module_centralizer_normal (Z1 := A) hn
      Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C))
    have htransport : qcard (plane V W) = Nat.card (pResidual 2 K) := by
      exact ExtraspecialMarker.residual_card M V hn W
    have hq : qcard Z = 5 := by
      let := caseI_module_centralizer_normal (Z1 := Z) hn
      change Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5
      exact hcard
    rw [← hW] at hq
    exact htransport.symm.trans hq
  have hfull := s.full_image_residual hTM hn c d hJ
  have hPR : P ≤ (pResidual 2 K).map K.subtype := hfull.1
  have hPcard : Nat.card P = 5 := (s.kernel_card s.second).trans hfive
  have hRcard : Nat.card ((pResidual 2 K).map K.subtype) = 5 := by
    rw [card_map_of_injective K.subtype_injective, hKcard]
  have hEq : P = (pResidual 2 K).map K.subtype :=
    eq_of_le_of_card_ge hPR (by rw [hRcard, hPcard])
  exact hEq.symm

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The unchanged prepared quintic source supplies the actor-side equality
needed by the literal order-five residual identity. -/
theorem PreparedChosenModule.decomposable_five_prime_residual_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (_hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      let Z := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
      Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 →
      (pResidual 2 (subspaceKernel (imageRepresentation M V h.normalized)
        ((c.ambientFactor d s.first).space ⊓ fixedSpace
          (imageRepresentation M V h.normalized)
          (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
            (actionHom M V h.normalized).rangeRestrict)) ⊤)).map
          (subspaceKernel (imageRepresentation M V h.normalized)
            ((c.ambientFactor d s.first).space ⊓ fixedSpace
              (imageRepresentation M V h.normalized)
              (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
                (actionHom M V h.normalized).rangeRestrict)) ⊤).subtype =
        (s.marking s.second).kernel.map
          (c.ambientFactor d s.second).embedding.groupMap := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  dsimp only
  intro hcard
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun E hE => hE.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  exact DecomposableMarker.ThompsonPair.full_image_residual_eq_marked_of_quotient_card_five
    hM.1.2 h.normalized c d s π hp hs hJi hfive hcard

end CFSG.Quasithin.Chapter15.Section01
