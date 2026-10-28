module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticPrimeGroup

/-!
# Faithful action of the original quintic moving support on the raw component

The original opposite quintic actor acts irreducibly on its sixteen-element
support. The centralizer of the selected component in that support is an
invariant subgroup. Original noncentral movement excludes the whole support,
so that centralizer is trivial. The resulting conjugation action is faithful.

The raw component and both original supports are retained. No marked
generation assertion or generation-dependent component record is used.

Source: Aschbacher--Smith 15.1.19(7), 15.1.21--23, printed pp.1093--1100.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem raw_moving_support_faithful
    {T : Sylow 2 G} {M V L : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJi : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5)
    (hnL : let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G))
    (hmove : let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅L,⁅V,R⁆⁆ ≠ ⊥) :
    let B := plane V (c.ambientFactor d s.second).space
    ∃ hBL : B ≤ normalizer (L : Set G),
      Function.Injective (actionHom B L hBL) ∧ Nat.card (internalActionImage B L hBL) = 16 := by
  intro B
  let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
  let C := M ⊓ centralizer (Z1 : Set G)
  let R := (pResidual 2 C).map C.subtype
  let A := (primeToResidual 5 C).map C.subtype
  have hWB : ⁅V,R⁆ = B := (s.full_residual_geometry hTM hn c d π hp hs hJi).2.1
  have hRB : R ⊔ B ≤ normalizer (L : Set G) := hWB ▸ hnL
  have hnon : ⁅L,B⁆ ≠ ⊥ := hWB ▸ hmove
  obtain ⟨_,_,hAmove,_,_,_,_,hAR⟩ := s.quintic_actor_geometry hTM hn c d π hp hs hJi hfive
  have hAB : A ≤ normalizer (B : Set G) := by
    change A ≤ normalizer (plane V (c.ambientFactor d s.second).space : Set G)
    rw [←hAmove]
    exact normalizer_commutator_ge_right V A
  have hAL : A ≤ normalizer (L : Set G) := hAR.trans (le_sup_left.trans hRB)
  have hbot : B ⊓ centralizer (L : Set G) = ⊥ := by
    rcases s.quintic_actor_irreducible hTM hn c d π hp hs hJi hfive
        (B ⊓ centralizer (L : Set G)) inf_le_left
        (le_normalizer_inf hAB (hAL.trans (normalizer_le_normalizer_centralizer _))) with hz | he
    · exact hz
    · exact False.elim (hnon (by
        rw [commutator_comm]
        exact commutator_eq_bot_iff_le_centralizer.mpr (he.symm.le.trans inf_le_right)))
  have hBL : B ≤ normalizer (L : Set G) := le_sup_right.trans hRB
  have hfaith : Function.Injective (actionHom B L hBL) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [actionHom_ker]
    apply bot_unique
    intro x hx
    have hh : (x : G) ∈ B ⊓ centralizer (L : Set G) := ⟨x.property,hx⟩
    rw [hbot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  exact ⟨hBL,hfaith,(Nat.card_range_of_injective hfaith).trans (s.support_card s.second)⟩

/-- The same prescribed raw component has faithful action of the original
sixteen-element moving support, directly from the full source hypotheses. -/
theorem PreparedChosenModule.decomposable_five_raw_moving_support_action
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
      let C := M ⊓ centralizer (Z1 : Set G)
      let R := (pResidual 2 C).map C.subtype
      let B := plane V (c.ambientFactor d s.second).space
      ∀ {L : Subgroup G}, R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∃ hBL : B ≤ normalizer (L : Set G),
          Function.Injective (actionHom B L hBL) ∧ Nat.card (internalActionImage B L hBL) = 16 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 C R B L hnL hmove
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  exact raw_moving_support_faithful hM.1.2 h.normalized c d s π hp hs hJi hfive hnL hmove

/-- The original order-four-partner branch constructs one outside component
and preserves the faithful moving-support action on that same component. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_faithful_component
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
      Nat.card (localModule T Mc) = 4 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let B := plane V (c.ambientFactor d s.second).space
      ∃ L : Subgroup G, L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ G1 ⊓ Mc ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) ∧ ⁅L,⁅V,R⁆⁆ ≠ ⊥ ∧
        ∃ hBL : B ≤ normalizer (L : Set G),
          Function.Injective (actionHom B L hBL) ∧ Nat.card (internalActionImage B L hBL) = 16 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨L,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLc,hout,hquasi,
      hloc,hSL,hLM,hn,hm,_⟩ := h.decomposable_five_partner_four_raw_component
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  exact ⟨L,hLc,hout,hquasi,hloc,hSL,hLM,hn,hm,
    h.decomposable_five_raw_moving_support_action hG T hempty hM hmany hJ hfull
      c d hd s π hp hs hdec hq hfive hn hm⟩

end CFSG.Quasithin.Chapter15.Section01
