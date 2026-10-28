module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticActorCentralizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticLift

/-!
# Excluding the proper diagonal module in the original quintic source

An actual symmetric-three third local supplies its normal cubic residual Y.
The original action kernel normalizes Y. Two-perfectness forces the image
of Y to centralize each original order-five factor kernel. The rank-two
ambient lifting lemma therefore puts those kernels in the third-local
intersection image. That intersection meets J-hat in a two-group, a
contradiction. Thus the third local's actual module is the full original E.

The argument uses the literal original action and kernels, and allows the
extra cubic actors which occur in the full ratio-two module.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section02 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

/-- An actual third local in the original quintic decomposable row cannot
have symmetric-three action on its own local module. -/
theorem PreparedChosenModule.decomposable_five_third_not_symmetricThree
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
        (actionHom M V h.normalized).rangeRestrict c d π → s.prime = 5 →
      N ∈ maximalTwoLocalOvergroups (T : Subgroup G) → N ≠ M → N ≠ Mc →
      ¬ Nonempty (internalActionImage N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) := by
  let := h.elementary
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro U c d hd s π hp hs hdec hfive hN hNM hNMc ⟨eN⟩
  let f := (actionHom M V h.normalized).rangeRestrict
  let Y := sourceResidual N Mc
  let YM := Y.subgroupOf M
  let B := YM.map f
  let A := ((M ⊓ N).subgroupOf M).map f
  let S := ((T : Subgroup G).subgroupOf M).map f
  let J := Jhat (imageRepresentation M V h.normalized)
  obtain ⟨hYMN,_,hpY,_,_,hCY,⟨eY⟩⟩ := h.ordered_local_residual_of_symmetricThree
    hG T hempty hM hmany hJ hu hfull hN hNMc eN
  have hYM : Y ≤ M := hYMN.trans inf_le_left
  have hNY : normalizer (Y : Set G) = N :=
    h.ordered_local_residual_normalizer_of_symmetricThree
      hG T hempty hM hmany hJ hu hfull hN hNMc eN
  let j := subgroupOfEquivOfLe hYM
  have hpYM : IsPPerfect 2 YM := hpY.of_surjective j.symm.toMonoidHom j.symm.surjective
  have hpB : IsPPerfect 2 B := hpYM.of_surjective (f.subgroupMap YM) (f.subgroupMap_surjective YM)
  have hcYM : Nat.card (YM ⧸ pCore 2 YM) = 3 := by
    let eq := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
    exact (Nat.card_congr (eq.trans eY).toEquiv).trans (by simp)
  have hkernel : f.ker ≤ normalizer (YM : Set M) := by
    rw [←subgroupOf_normalizer_eq hYM]
    intro m hm
    apply hCY
    refine ⟨m.property,?_⟩
    have he : f.ker = (centralizer (V : Set G)).subgroupOf M := by
      rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
    change m ∈ (centralizer (V : Set G)).subgroupOf M
    exact he ▸ hm
  have hBc := s.twoPerfect_centralizes_quintic_kernels h.normalized c d π hp hdec hfive B hpB
  have hSA : S ≤ A := map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))
  have hnot : ¬ J ≤ A := h.decomposable_five_third_image_not_contains
    hG T hempty hM hJ hfull c d hd s π hp hs hdec hfive hN hNM
  have hinter : A ⊓ J = S ⊓ J :=
    (s.image_intersection_eq_or_contains_of_prime_five hM.1.2 h.normalized
      c d π hp hdec hfive A hSA).resolve_right hnot
  obtain ⟨_,_,_,_,_,i,k,_,_,hgen,_,_,_,_,_,_,_⟩ := hdec
  let P := (s.marking i).kernel.map (c.ambientFactor d i).embedding.groupMap
  have hcP : Nat.card P = 5 := (s.kernel_card i).trans hfive
  have hPfive : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hcP)
  have hPN : P ≤ (normalizer (YM : Set M)).map f :=
    DecomposableQuinticControl.five_image_le_normalizer_map_of_cubic_residual
      f (actionHom M V h.normalized).rangeRestrict_surjective YM hpYM hcYM
      ((hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 Nat.prime_three (by decide))
      P hPfive
      (le_centralizer_iff.mp (hBc i)) hkernel
  have hPA : P ≤ A := by
    apply hPN.trans
    apply map_mono
    rw [←subgroupOf_normalizer_eq hYM,hNY]
    exact fun m hm => ⟨m.property,hm⟩
  have hPJ : P ≤ J :=
    (map_le_range _ _).trans (le_sup_left.trans hgen.le)
  have hPS : P ≤ S := by
    have hh : P ≤ A ⊓ J := le_inf hPA hPJ
    rw [hinter] at hh
    exact hh.trans inf_le_left
  have hPtwo : IsPGroup 2 P :=
    (((T.isPGroup').comap_of_injective M.subtype M.subtype_injective).map f).to_le hPS
  obtain ⟨n,hn⟩ := hPtwo.exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card P) := by
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  rw [hcP] at hcop
  norm_num at hcop

/-- The surviving third-local module is exactly the original sixteen-element
Thompson fixed space; the proper diagonal alternative is excluded ambiently. -/
theorem PreparedChosenModule.decomposable_five_third_full_fixed
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
      localModule T N = thompsonFixed T V := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hN hNM hNMc
  obtain ⟨_,hcases⟩ := h.decomposable_five_third_residual_alternative
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hN hNM hNMc
  rcases hcases with he | ⟨_,he,_⟩
  · exact he
  · exact False.elim (h.decomposable_five_third_not_symmetricThree
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hfive hN hNM hNMc he)

end CFSG.Quasithin.Chapter15.Section01
