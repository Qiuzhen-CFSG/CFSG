module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFixedAction
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Full

/-!+# The actual partner residual of a quintic third local

The symmetric-three action on a third local's own module supplies the
literal partner residual Y. Original ordering puts Y in M ∩ N and makes
C_M(V) normalize it. Its quotient by O₂(Y) is cyclic of order three, and
its full ambient normalizer is the original maximal two-local N.

These ambient conclusions do not identify the kernel of Y on V(M): that
requires a separate calculation of its original action image. They also
do not assert that the third local's module fills the sixteen-element E.

Source: Aschbacher--Smith 14.1.18 and 15.2.5, printed pp.981,1107--1108.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section02 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

/-- Original ordering and the actual S₃ action produce the partner residual,
including its literal placement and cyclic core quotient. -/
theorem PreparedChosenModule.ordered_local_residual_of_symmetricThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNMc : N ≠ Mc)
    (e : internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) :
    let Y := sourceResidual N Mc
    Y ≤ M ⊓ N ∧ (Y.subgroupOf N).Normal ∧ IsPPerfect 2 Y ∧
      Nat.card ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) = 3 ∧
      Y.pCoreIn 2 = Y ⊓ centralizer (localModule T N : Set G) ∧
      M ⊓ centralizer (V : Set G) ≤ normalizer (Y : Set G) ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (ZMod 3)) := by
  let W := localModule T N
  let C := (centralizer (W : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _))
  let a := actionHom N W (le_normalizer_conjugateSpanBy _ _)
  let eq : (N ⧸ C) ≃* Equiv.Perm (Fin 3) :=
    ((QuotientGroup.quotientMulEquivOfEq (actionHom_ker N W
      (le_normalizer_conjugateSpanBy _ _)).symm).trans
      (QuotientGroup.quotientKerEquivRange a)).trans e
  obtain ⟨hmeet,hne,hcomm⟩ := local_partner_core_inputs hG T hempty hN hu hmany hNMc
  have hs := sourceResidual_splitting N Mc W eq hmeet hne hcomm
  let Y := sourceResidual N Mc
  have hn : (Y.subgroupOf N).Normal := residualY_normal N Mc
  have hn' : N ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le N Mc)).mp hn
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hle : Y ≤ M ⊓ N := ordered_partner_residual_le T hM.1.2 hN.2 hu hord
  refine ⟨hle,hn,residualY_isPPerfect N Mc,hs.2.1,hs.2.2.2.2.1,?_,?_⟩
  · apply le_trans ?_ hn'
    rw [hfull]
    exact ((lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source hG T hN)).trans inf_le_left
  · let A := Y.subgroupOf N
    let : A.Normal := hn
    let j : A ≃* Y := subgroupOfEquivOfLe (hle.trans inf_le_right)
    let k := QuotientGroup.congr (pCore 2 A) (pCore 2 Y) j (pCore_map_iso 2 j)
    let f : A.map (QuotientGroup.mk' (pCore 2 N)) ≃* Multiplicative (ZMod 3) :=
      mulEquivOfPrimeCardEq hs.2.1 (by simp)
    exact ⟨k.symm.trans ((coreQuotientEquivImage 2 A).trans f)⟩

/-- The ambient normalizer of that literal partner residual is the original N. -/
theorem PreparedChosenModule.ordered_local_residual_normalizer_of_symmetricThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNMc : N ≠ Mc)
    (e : internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) :
    normalizer (sourceResidual N Mc : Set G) = N := by
  obtain ⟨_,hn,_,hc,hker,_,_⟩ := h.ordered_local_residual_of_symmetricThree
    hG T hempty hM hmany hJ hu hfull hN hNMc e
  let Y := sourceResidual N Mc
  let W := localModule T N
  have hYN : Y ≤ N := sourceResidual_le N Mc
  have hNY : N ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYN).mp hn
  have hne : Y ≠ ⊥ := by
    intro he
    have hb : Y.subgroupOf N = ⊥ := by rw [he,bot_subgroupOf]
    change Nat.card ((Y.subgroupOf N).map _) = 3 at hc
    rw [hb,Subgroup.map_bot,card_bot] at hc
    omega
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hWn : N ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
    let : IsElementaryAbelian 2 W := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
    have hcY : ⁅W,Y⁆ ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 W).to_le
        (le_normalizer_iff_commutator_le_left.mp (hYN.trans hWn)))
      (le_normalizer_iff_commutator_le_right.mp ((localModule_le T hN.2).trans hNY))
      (normalizer_commutator_ge_right W Y)
    have hcomm : ⁅W,Y⁆ = ⊥ := bot_unique (he ▸ hcY)
    have hcent : Y ≤ centralizer (W : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    have hh : Y = Y.pCoreIn 2 := by rw [hker,inf_eq_left.mpr hcent]
    exact hne (hh.trans he)
  exact normalizer_eq_of_nontrivial_core N Y (Y.pCoreIn 2) hYN hN.1 hn hcore le_rfl

/-- The actual prime-five source either fills E or has a four-element local
module with the original cyclic partner residual and full normalizer N. -/
theorem PreparedChosenModule.decomposable_five_third_residual_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
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
      N ∈ maximalTwoLocalOvergroups (T : Subgroup G) → N ≠ M → N ≠ Mc →
      localModule T N = conjugateSpanBy (centralInvolutions T) (M ⊓ N) ∧
        (localModule T N = thompsonFixed T V ∨
          (Nat.card (localModule T N) = 4 ∧
            Nonempty (internalActionImage N (localModule T N)
              (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃*
                Equiv.Perm (Fin 3)) ∧
            let Y := sourceResidual N Mc
            Y ≤ M ⊓ N ∧ (Y.subgroupOf N).Normal ∧ IsPPerfect 2 Y ∧
              Nat.card ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) = 3 ∧
              Y.pCoreIn 2 = Y ⊓ centralizer (localModule T N : Set G) ∧
              M ⊓ centralizer (V : Set G) ≤ normalizer (Y : Set G) ∧
              Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (ZMod 3)) ∧
              normalizer (Y : Set G) = N)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hN hNM hNMc
  obtain ⟨hspan,hcases⟩ := h.decomposable_five_third_fixed_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hN hNM hNMc
  refine ⟨hspan,?_⟩
  rcases hcases with ⟨hc,⟨e⟩⟩ | he
  · obtain ⟨hle,hn,hp,hstar,hker,hCY,hquot⟩ := h.ordered_local_residual_of_symmetricThree
      hG T hempty hM hmany hJ hu hfull hN hNMc e
    exact Or.inr ⟨hc,⟨e⟩,hle,hn,hp,hstar,hker,hCY,hquot,
      h.ordered_local_residual_normalizer_of_symmetricThree
        hG T hempty hM hmany hJ hu hfull hN hNMc e⟩
  · exact Or.inl he

end CFSG.Quasithin.Chapter15.Section01
