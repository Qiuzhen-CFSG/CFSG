module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionMarkedFusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFifteen

/-!
# Two original marker fields in the order-four partner branch

The literal marked residual has order five or fifteen. Order fifteen would
make the partner module equal to the original sixteen-element fixed subgroup,
contrary to the branch cardinality. Moreover, the marked centralizer cannot
lie in the partner: marked fusion would make its opposite quintic actor fix
the second Thompson four-group, contradicting irreducibility on its original
sixteen-element support. Generation is not asserted here.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.decomposable_five_partner_four_marked_residual_card_five
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
      Nat.card (localModule T Mc)=4 →
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M⊓centralizer (Z₁:Set G)
      letI := caseI_module_centralizer_normal (Z1:=Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸ (M⊓centralizer (V:Set G)).subgroupOf C))=5 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  rcases (s.full_quotient_residual_of_prime_five hM.1.2 h.normalized c d π hp hs hJi hfive).2
      with h5 | h15
  · exact h5
  · have he := (h.decomposable_fifteen_partner_and_normalization
      hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive h15).1
    have hc := congrArg (fun K : Subgroup G => Nat.card K) he
    rw [hcU,s.fixed_card] at hc
    omega

theorem PreparedChosenModule.decomposable_five_partner_four_marked_centralizer_not_le
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
      Nat.card (localModule T Mc)=4 →
      ¬ M⊓centralizer (thompsonPlane T V (c.ambientFactor d s.first).space:Set G)≤Mc := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
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
  have hmark : centralizer (Z₁:Set G)⊓Mc=centralizer (E:Set G) :=
    (h.decomposable_five_partner_four_marked_centralizer
      hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive hcU).1
  have hYC : Y≤C := map_subtype_le _
  have hYE : Y≤centralizer (E:Set G) :=
    (le_inf (hYC.trans inf_le_right) (hYC.trans hCMc)).trans_eq hmark
  have hYZ₂ : Y≤normalizer (Z₂:Set G) :=
    (hYE.trans (centralizer_le (show Z₂≤E from inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
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
