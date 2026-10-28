module

import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSeed
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualKernel
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The original quintic intersection residual determines the maximal local

Let R be the two-core of M ∩ Mc and let N be its relative conjugate closure
under O²(M₀)T, where M₀ is the original J-hat preimage. Its nontrivial
Sylow-normal image contains a central involution belonging to J-hat.
The image of YT contains N. If it missed J-hat, the quintic intersection
dichotomy would make N ∩ J-hat a nontrivial normal two-subgroup of J-hat,
contradicting the reduced original action. The original starred seed span
then gives unique maximal two-local overgroup M.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation {D : Type*} [Group D] [Finite D] (H : Subgroup D) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

private theorem quintic_central_involution_mem_Jhat
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V hn)=2) (hfive : s.prime=5)
    (z : internalActionImage M V hn)
    (hzS : z∈((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)
    (hz : orderOf z=2)
    (hzC : z∈centralizer ((((T : Subgroup G).subgroupOf M).map
      (actionHom M V hn).rangeRestrict : Subgroup (internalActionImage M V hn)) :
        Set (internalActionImage M V hn))) :
    z ∈ Jhat (imageRepresentation M V hn) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  obtain ⟨_,_,_,_,_,i,j,hij,hall,hgen,hdis,hcom,hcompl,t,ht,htij,_⟩ := hdec
  have emark (k : d.Index) : (c.ambientFactor d k).actor ≃* DihedralGroup 5 := by
    have hm := (s.dihedral k).dihedral
    rw [hfive] at hm
    exact (MonoidHom.ofInjective (c.ambientFactor d k).embedding.group_injective).symm.trans hm.some
  have hnormal : ((c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor).Normal := by
    rw [hgen]; exact Jhat_normal ρ
  have hcyc (A : Subgroup D) (hA : IsPGroup 2 A)
      (hAS : A≤subspaceStabilizer ρ (c.ambientFactor d i).space) :
      IsCyclic (restrictedSubgroup ρ (c.ambientFactor d i).space A) := by
    apply quintic_support_two_cyclic (c.ambientFactor d i)
      (c.support_stabilizer_normalizes_actor d π hp hs i) (s.marking i) _ A hA hAS
    change CyclicSource.DihedralMarking (s.marking i) 5 2
    simpa only [hfive] using s.dihedral i
  have hperm (g : D) (_hg : g∈(S:Subgroup D)) :
      ((c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom=(c.ambientFactor d i).actor ∧
        (c.ambientFactor d i).space.map (ρ g)=(c.ambientFactor d i).space) ∨
      ((c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom=(c.ambientFactor d j).actor ∧
        (c.ambientFactor d i).space.map (ρ g)=(c.ambientFactor d j).space) := by
    rcases hall (π g i) with hi | hj
    · exact Or.inl ⟨(hp g i).trans (congrArg (fun k => (c.ambientFactor d k).actor) hi),
        (hs g i).trans (congrArg (fun k => (c.ambientFactor d k).space) hi)⟩
    · exact Or.inr ⟨(hp g i).trans (congrArg (fun k => (c.ambientFactor d k).actor) hj),
        (hs g i).trans (congrArg (fun k => (c.ambientFactor d k).space) hj)⟩
  obtain ⟨hzin,_⟩ := central_involution_factor_product ρ (imageRepresentation_injective M V hn)
    S (c.ambientFactor d i) (c.ambientFactor d j)
    ((Nat.card_congr (emark i).toEquiv).trans (by rw [DihedralGroup.nat_card]))
    hdis hcom hnormal hcompl (c.ambient_cross d hij.symm) (c.ambient_cross d hij)
    hperm hcyc (f t) (mem_map_of_mem f ht)
    ((hp (f t) i).trans (congrArg (fun k => (c.ambientFactor d k).actor) htij))
    ((hs (f t) i).trans (congrArg (fun k => (c.ambientFactor d k).space) htij)) hq z hzS hz hzC
  rw [hgen] at hzin
  exact hzin

/-- The literal intersection residual and T have unique maximal two-local overgroup M. -/
theorem PreparedChosenModule.decomposable_five_caseIIResidual_unique
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
      maximalTwoLocalOvergroups
        (Section02.caseIIResidual T M (Section02.chosenStarredPreimage M V h.normalized) Mc ⊔
          (T : Subgroup G)) = {M} := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let V := localModule T M
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let S : Sylow 2 D := (T.subtype hM.1.2).mapSurjective
    (actionHom M V h.normalized).rangeRestrict_surjective
  let J := Jhat ρ
  let M₀ := Section02.chosenStarredPreimage M V h.normalized
  let R₀ := (M ⊓ Mc).pCoreIn 2
  let R := (R₀.subgroupOf M).map f
  let O := twoResidualAmbient J ⊔ (S : Subgroup D)
  let N := conjugateSpanBy R O
  let Y := Section02.caseIIResidual T M M₀ Mc
  let A := ((Y ⊔ (T : Subgroup G)).subgroupOf M).map f
  let : J.Normal := Jhat_normal ρ
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hRT : R₀ ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hM.1.2 hTMc))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf hM.1.2 hTMc)] using hh
  have hRS : R ≤ (S : Subgroup D) := map_mono (subgroupOf_mono M hRT)
  have hRn : (S : Subgroup D) ≤ normalizer (R : Set D) := by
    apply le_normalizer_iff.mpr
    rintro x ⟨t,ht,rfl⟩ y ⟨r,hr,rfl⟩
    refine ⟨t*r*t⁻¹,?_,by simp only [map_mul,map_inv]; rfl⟩
    exact le_normalizer_iff.mp
      ((le_inf hM.1.2 hTMc).trans ((M ⊓ Mc).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 (M ⊓ Mc : Subgroup G)))))
      t ht r hr
  have hRne : R ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    apply Section02.source_chosen_core_noncentral hG T hempty hM hJ hu hmany h
    intro x hx
    let a : M := ⟨x,((pCoreIn_le 2 _).trans inf_le_left) hx⟩
    have hh : actionHom M V h.normalized a = 1 :=
      congrArg Subtype.val (hk (show a ∈ R₀.subgroupOf M from hx))
    have hc : a ∈ (actionHom M V h.normalized).ker := hh
    rwa [actionHom_ker] at hc
  obtain ⟨z,hzR,hz,hzC⟩ := normal_two_contains_central_involution
    (S : Subgroup D) S.isPGroup' R hRS hRn hRne
  have hzJ : z ∈ J := quintic_central_involution_mem_Jhat hM.1.2 h.normalized c d s π hp hs
    hdec hq hfive z (hRS hzR) hz hzC
  have hM₀M : M₀ ≤ M := map_subtype_le _
  have hM₀image : (M₀.subgroupOf M).map f = J := by
    change ((((Jhat ρ).comap f).map M.subtype).subgroupOf M).map f = Jhat ρ
    rw [←comap_subtype,comap_map_eq_self_of_injective M.subtype_injective]
    exact map_comap_eq_self_of_surjective (show Function.Surjective f from
      (actionHom M V h.normalized).rangeRestrict_surjective) (Jhat ρ)
  have hY₀image : ((twoResidualAmbient M₀).subgroupOf M).map f = twoResidualAmbient J := by
    rw [←map_twoResidualAmbient_of_subgroup_image (M₀.subgroupOf M) M.subtype M₀
      (map_subgroupOf_eq_of_le hM₀M),←comap_subtype,
      comap_map_eq_self_of_injective M.subtype_injective,
      map_twoResidualAmbient_of_subgroup_image _ f _ hM₀image]
  have hY₀M : twoResidualAmbient M₀ ≤ M :=
    (show twoResidualAmbient M₀ ≤ M₀ from map_subtype_le _).trans hM₀M
  have hOrbit : ((twoResidualAmbient M₀ ⊔ (T : Subgroup G)).subgroupOf M).map f = O := by
    rw [subgroupOf_sup hY₀M hM.1.2,Subgroup.map_sup,hY₀image]
    rfl
  have hYimage : (Y.subgroupOf M).map f = twoResidualAmbient N := by
    rw [Section02.source_caseIIResidual_image T hM.1.2 hM₀M f,hOrbit]
  have hYM : Y ≤ M := Section02.source_caseIIResidual_le T hM.1.2 hM₀M
  have hA : A = twoResidualAmbient N ⊔ (S : Subgroup D) := by
    rw [show A = ((Y ⊔ (T : Subgroup G)).subgroupOf M).map f from rfl,
      subgroupOf_sup hYM hM.1.2,Subgroup.map_sup,hYimage]
    rfl
  have hSN : (S : Subgroup D) ≤ normalizer (N : Set D) :=
    le_sup_right.trans (le_normalizer_conjugateSpanBy R O)
  have hNA : N ≤ A := by
    rw [hA,residual_notation]
    exact le_embedded_pResidual_sup_sylow_of_normalizes S N hSN
  have hJO : J ≤ O := by
    change J ≤ twoResidualAmbient J ⊔ (S : Subgroup D)
    rw [residual_notation]
    exact le_embedded_pResidual_sup_sylow_of_normalizes S J le_normalizer_of_normal
  have hJA : J ≤ A := by
    rcases s.image_intersection_eq_or_contains_of_prime_five hM.1.2 h.normalized c d π hp hdec
      hfive A (by rw [hA]; exact le_sup_right) with he | hcontains
    · have hNJtwo : IsPGroup 2 (N ⊓ J : Subgroup D) := S.isPGroup'.to_le
        ((inf_le_inf hNA le_rfl).trans (he.le.trans inf_le_left))
      have hJNJ : J ≤ normalizer (N ⊓ J : Set D) :=
        le_normalizer_inf (hJO.trans (le_normalizer_conjugateSpanBy R O)) J.le_normalizer
      have hNJcore : N ⊓ J ≤ J.pCoreIn 2 :=
        le_pCoreIn_of_normalizes hNJtwo inf_le_right hJNJ
      have hDcore : pCore 2 D = ⊥ := source_localAction_twoCore hG T hM
      have hJcore : pCore 2 J = ⊥ := by
        rw [pCore_eq_comap_of_normal,hDcore]
        exact (MonoidHom.ker_eq_bot_iff J.subtype).mpr J.subtype_injective
      have hNJbot : N ⊓ J ≤ ⊥ := by
        simpa only [pCoreIn,hJcore,Subgroup.map_bot] using hNJcore
      have hz1 : z = 1 := hNJbot ⟨le_conjugateSpanBy R O hzR,hzJ⟩
      rw [hz1,orderOf_one] at hz
      contradiction
    · exact hcontains
  have himage : (M₀.subgroupOf M).map (actionHom M V h.normalized) ≤
      ((Y ⊔ (T : Subgroup G)).subgroupOf M).map (actionHom M V h.normalized) := by
    rintro _ ⟨x,hx,rfl⟩
    have hfx : f x ∈ J := hM₀image ▸ mem_map_of_mem f hx
    obtain ⟨y,hy,hyx⟩ := hJA hfx
    exact ⟨y,hy,congrArg Subtype.val hyx⟩
  exact Section02.source_residual_sylow_unique_of_action_image hG T hempty hM hJ h hYM hM₀M
    (h.decomposable_five_starred_seed_span hG T hM rfl c d hd s π hp hs hdec hfive) himage

end CFSG.Quasithin.Chapter15.Section01
