module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticCubic
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Normalization
public import Theory.GroupAction.FourPerfectOrbit
public import Theory.GroupTheory.PResidual.PrimeToAction

/-!
# Global Thompson normalization in the marked order-fifteen branch

The cubic part of the original marked centralizer lies in the actual partner
by the prior-free fixed-normalizer bound. Its moving support is the opposite
sixteen-group. Coprime action and the original central seed force the partner
module to contain the opposite Thompson four-group; the original Sylow exchange
then gives both four-groups. Thus the partner module equals the Thompson fixed
subgroup, and the whole seed centralizer normalizes it.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_action_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V)) :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let C := M ⊓ centralizer (plane V W : Set G)
    let A := (primeToResidual 3 C).map C.subtype
    (A.subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (primeToResidual 3 K).map K.subtype := by
  intro K C A
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  let a := f.comp (inclusion hAM)
  obtain ⟨q,hq,_,hcoord⟩ := ExtraspecialMarker.stabilizer_projection M V hn W
  have he := map_primeToResidual_of_surjective 3 q hq
  change (A.subgroupOf M).map f = _
  rw [←inclusion_range hAM,←MonoidHom.range_comp]
  change a.range = _
  rw [←he,map_map]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨z,hz,hzy⟩ := y.property
    refine ⟨z,hz,?_⟩
    change (q z : internalActionImage M V hn) = f (inclusion hAM y)
    exact (hcoord z).trans (congrArg f (Subtype.ext hzy))
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,mem_map_of_mem C.subtype hz⟩,(hcoord z).symm⟩

private theorem cubic_actor_of_fixed_normalizer
    (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V)
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized) (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) h.normalized c d)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ⊓
        Jhat (imageRepresentation M V h.normalized))
    (hfive : s.prime = 5)
    (hEN : normalizer (thompsonFixed T V : Set G) ≤ Mc) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let A := (primeToResidual 3 C).map C.subtype
    letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
    Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 15 →
      A ≤ M ⊓ Mc ∧ A ≤ (pResidual 2 C).map C.subtype ∧
      Nat.card ((A.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) = 3 ∧
      ¬ A ≤ centralizer (V : Set G) ∧
      ⁅V,A⁆ = plane V (c.ambientFactor d s.second).space := by
  intro Z C A h15
  let ρ := imageRepresentation M V h.normalized
  let f : M →* internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ J
  let K := subspaceKernel ρ W ⊤
  have hW : plane V W = Z := plane_thompson_intersection hM.1.2 h.normalized _
  have hi : (A.subgroupOf M).map f = (primeToResidual 3 K).map K.subtype := by
    have hh := cubic_action_image M V h.normalized W
    rwa [hW] at hh
  have hK15 : Nat.card (pResidual 2 K) = 15 := by
    let qcard (Z' : Subgroup G) : ℕ :=
      let C' := M ⊓ centralizer (Z' : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z') h.normalized
      Nat.card (pResidual 2 (C' ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C'))
    have hh : qcard (plane V W) = Nat.card (pResidual 2 K) :=
      ExtraspecialMarker.residual_card M V h.normalized W
    rw [hW] at hh
    exact hh.symm.trans h15
  obtain ⟨hcard,hcentral⟩ := s.full_image_cubic_residual_of_fifteen
    hM.1.2 h.normalized c d π hp hs hJ hfive hK15
  have hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  have hAJ : (A.subgroupOf M).map f ≤ centralizer (J : Set _) := by
    rw [hi]
    have hJJ : J ≤ Jhat ρ := by
      change ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict ≤ Jhat ρ
      rw [hJ]
      exact inf_le_right
    exact hcentral.trans (centralizer_le hJJ)
  have hnorm : (A.subgroupOf M).map f ≤ subspaceStabilizer ρ (fixedSpace ρ J) :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ _ J
      (commutator_eq_bot_iff_le_centralizer.mpr hAJ)
  have hAVE : A ≤ normalizer (thompsonFixed T V : Set G) := by
    rw [←plane_thompson_image hM.1.2 h.normalized]
    apply le_normalizer_iff.mpr
    rintro a ha y ⟨v,hv,rfl⟩
    let aM : M := ⟨a,hAM ha⟩
    refine ⟨(actionHom M V h.normalized aM) v,?_,rfl⟩
    exact (hnorm (mem_map_of_mem f (show aM ∈ A.subgroupOf M from ha))
      (Additive.ofMul v)).mpr hv
  have hAR : A ≤ (pResidual 2 C).map C.subtype := by
    apply map_mono
    apply primeToResidual_le
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := C) 2).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have himcard : Nat.card ((A.subgroupOf M).map f) = 3 := by
    rw [hi,card_map_of_injective K.subtype_injective,hcard]
  have hnoncentral : ¬ A ≤ centralizer (V : Set G) := by
    intro hAC
    have hb : (A.subgroupOf M).map f = ⊥ := by
      apply bot_unique
      rintro _ ⟨a,ha,rfl⟩
      apply mem_bot.mpr
      apply Subtype.ext
      change a ∈ (actionHom M V h.normalized).ker
      rw [actionHom_ker]
      exact hAC ha
    rw [hb,card_bot] at himcard
    omega
  refine ⟨le_inf hAM (hAVE.trans
    hEN),hAR,himcard,hnoncentral,?_⟩
  let Y := (primeToResidual 5 C).map C.subtype
  have hYC : Y ≤ C := map_subtype_le _
  have hCA : C ≤ normalizer (A : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 C))
  have hYN : Y ≤ normalizer ((⁅V,A⁆ : Subgroup G) : Set G) := by
    intro y hy
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (h.normalized (hYC hy).1),
      mem_normalizer_iff_map_conj_eq.mp (hCA (hYC hy))]
  have hgeo := s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJ
  have hmovele : ⁅V,A⁆ ≤ plane V (c.ambientFactor d s.second).space :=
    (commutator_mono le_rfl hAR).trans hgeo.2.1.le
  rcases s.quintic_actor_irreducible hM.1.2 h.normalized c d π hp hs hJ hfive
      ⁅V,A⁆ hmovele hYN with hzero | hfull
  · exact (hnoncentral (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hzero))).elim
  · exact hfull


private theorem coprime_cubic_fixed_support
    (M V A V₁ V₂ : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hAM : A ≤ M)
    (hi : Nat.card ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) = 3)
    (hV₁ : V₁ ≤ V) (hV₂ : V₂ ≤ V)
    (hjoin : V₁ ⊔ V₂ = V) (hdis : V₁ ⊓ V₂ = ⊥)
    (hcard₁ : Nat.card V₁ = 16) (hcard₂ : Nat.card V₂ = 16)
    (hfix : V₁ ≤ centralizer (A : Set G)) (hmove : ⁅V,A⁆ = V₂) :
    V ⊓ centralizer (A : Set G) = V₁ ∧ V₂ ⊓ centralizer (A : Set G) = ⊥ := by
  have hnorm (B C : Subgroup G) (hB : B ≤ V) (hC : C ≤ V) :
      C ≤ normalizer (B : Set G) :=
    (hC.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hB))).trans (Subgroup.centralizer_le_normalizer _)
  have hcV : Nat.card V = 256 := by
    rw [←hjoin,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hnorm V₁ V₂ hV₁ hV₂) (disjoint_iff.mpr hdis),hcard₁,hcard₂]
  have himage : Nat.card (actionHom A V (hAM.trans hn)).range = 3 := by
    have he : Nat.card ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) =
        (centralizer (V : Set G)).relIndex A := by
      rw [←relIndex_ker,MonoidHom.ker_rangeRestrict,actionHom_ker,relIndex_subgroupOf hAM]
    rw [MonoidHom.range_eq_map,←relIndex_ker,relIndex_top_right,actionHom_ker]
    exact he.symm.trans hi
  have hc : Nat.Coprime
      (Nat.card (V.normalizerMonoidHom.comp (inclusion (hAM.trans hn))).range)
      (Nat.card V) := by
    change Nat.Coprime (Nat.card (actionHom A V (hAM.trans hn)).range) (Nat.card V)
    rw [himage,hcV]
    decide
  obtain ⟨hgen,hd⟩ := commutator_centralizer_decomposition_of_coprime_image V A
    (hAM.trans hn) hc
  rw [hmove] at hgen hd
  have hcF : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) = 16 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint V₂
      (V ⊓ centralizer (A : Set G)) (hnorm _ _ hV₂ inf_le_left) (disjoint_iff.mpr hd)
    rw [hgen,hcV,hcard₂] at hh
    omega
  have he := (eq_of_le_of_card_ge (le_inf hV₁ hfix) (by rw [hcF,hcard₁])).symm
  refine ⟨he,?_⟩
  apply bot_unique
  intro x hx
  exact hd.le ⟨hx.1,hV₂ hx.1,hx.2⟩

private theorem four_group_le_of_nontrivial_commutator
    (A W Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hp : IsPPerfect 2 A) (hc : Nat.card Z = 4)
    (hAW : A ≤ normalizer (W : Set G)) (hAZ : A ≤ normalizer (Z : Set G))
    (hBZ : ⁅W,A⁆ ≤ Z) (hne : ⁅W,A⁆ ≠ ⊥)
    (hfixed : Z ⊓ centralizer (A : Set G) = ⊥) : Z ≤ W := by
  let B := ⁅W,A⁆
  have hBW : B ≤ W := le_normalizer_iff_commutator_le_left.mp hAW
  have hAB : A ≤ normalizer (B : Set G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hAW ha),
      mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer ha)]
  obtain ⟨b,hb,hb1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  let bZ : Z := ⟨b,hBZ hb⟩
  have hbZ : bZ ≠ 1 := fun he => hb1 (congrArg Subtype.val he)
  let f := actionHom A Z hAZ
  have hm : ∃ a, f a bZ ≠ bZ := by
    by_contra! hall
    have hba : b ∈ centralizer (A : Set G) := by
      intro a ha
      have he := congrArg Subtype.val (hall ⟨a,ha⟩)
      change a*b*a⁻¹=b at he
      exact mul_inv_eq_iff_eq_mul.mp he
    exact hb1 (mem_bot.mp (hfixed ▸ (show b ∈ Z ⊓ centralizer (A : Set G) from ⟨hBZ hb,hba⟩)))
  intro z hz
  by_cases hz1 : z=1
  · simpa only [hz1] using W.one_mem
  obtain ⟨a,ha⟩ := MulAction.four_orbit_of_twoPerfect hp hc f bZ hbZ hm
    ⟨z,hz⟩ (fun he => hz1 (congrArg Subtype.val he))
  have he := congrArg Subtype.val ha
  change (a:G)*b*(a:G)⁻¹=z at he
  exact hBW (he ▸ le_normalizer_iff.mp hAB a a.property b hb)

/-- The literal order-fifteen marked residual forces the partner's module to
be the whole original Thompson fixed subgroup. Consequently the global seed
centralizer normalizes that subgroup and all original residual and normalizer
conclusions follow, without a residual premise. -/
theorem PreparedChosenModule.decomposable_fifteen_partner_and_normalization
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
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z₁ : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 15 →
      localModule T Mc = thompsonFixed T V ∧
      centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T V : Set G) ∧
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T V : Set G) ∧
      M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  classical
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z₁ C h15
  let V := localModule T M
  let E := thompsonFixed T V
  let W := localModule T Mc
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let A := (primeToResidual 3 C).map C.subtype
  obtain ⟨hEN,hMN,hWE⟩ := h.decomposable_five_partner_control hG T hempty hM hmany hJ hu
    rfl c d hd s π hp hs hdec hq hfive
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun E hE => hE.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  obtain ⟨hAMc,hAR,himage,_,hmove⟩ := cubic_actor_of_fixed_normalizer T hM h c d s π hp hs
    hJi hfive hEN h15
  have hAM : A ≤ M := hAMc.trans inf_le_left
  have hAMc' : A ≤ Mc := hAMc.trans inf_le_right
  have hAE : A ≤ normalizer (E : Set G) := hAMc.trans hMN
  have hAV : A ≤ normalizer (V : Set G) := hAM.trans h.normalized
  have hV₁ : V₁ ≤ V := map_subtype_le _
  have hV₂ : V₂ ≤ V := map_subtype_le _
  have hgeo := s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi
  have hfix : V₁ ≤ centralizer (A : Set G) :=
    hgeo.1.symm.le.trans (inf_le_right.trans (centralizer_le hAR))
  obtain ⟨hfixed,hV₂fixed⟩ := coprime_cubic_fixed_support M V A V₁ V₂ h.normalized hAM
    himage hV₁ hV₂ s.complement s.disjoint (s.support_card s.first)
    (s.support_card s.second) hfix hmove
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMcW : Mc ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hAW : A ≤ normalizer (W : Set G) := hAMc'.trans hMcW
  obtain ⟨t,ht,hout⟩ : ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V₁ : Set G) := by
    by_contra! hall
    have he := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at he
    contradiction
  have hseedV₁ : centralInvolutions T ⊓ V₁ = ⊥ := by
    apply bot_unique
    intro z hz
    have hc : t*z*t⁻¹=z := by
      rw [centralInvolutions_le_centralizer_sylow T hz.1 t ht,mul_inv_cancel_right]
    have hz₂ : z ∈ V₂ := by
      have hh := mem_map_of_mem (MulAut.conj t).toMonoidHom hz.2
      rw [(s.exchanges t ht hout).1] at hh
      change t*z*t⁻¹ ∈ V₂ at hh
      rwa [hc] at hh
    exact s.disjoint.le ⟨hz.2,hz₂⟩
  have hne : ⁅W,A⁆ ≠ ⊥ := by
    intro he
    have hWC : W ≤ centralizer (A : Set G) := commutator_eq_bot_iff_le_centralizer.mp he
    have hZV₁ : centralInvolutions T ≤ V₁ := by
      rw [←hfixed]
      exact le_inf ((le_conjugateSpanBy _ _).trans (hWE.trans inf_le_left))
        ((le_conjugateSpanBy _ _).trans hWC)
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_inf le_rfl hZV₁).trans hseedV₁.le))
  have hAZ₂ : A ≤ normalizer (Z₂ : Set G) := by
    apply le_normalizer_inf ?_ hAE
    rw [←hmove]
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hAV ha),
      mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer ha)]
  have hBZ₂ : ⁅W,A⁆ ≤ Z₂ :=
    le_inf ((commutator_mono (hWE.trans inf_le_left) le_rfl).trans hmove.le)
      ((le_normalizer_iff_commutator_le_left.mp hAW).trans hWE)
  have hZ₂fixed : Z₂ ⊓ centralizer (A : Set G) = ⊥ :=
    bot_unique ((inf_le_inf inf_le_left le_rfl).trans hV₂fixed.le)
  let : IsElementaryAbelian 2 Z₂ := IsElementaryAbelian.of_injective
    (inclusion (show Z₂ ≤ V from inf_le_left.trans hV₂))
    (inclusion_injective _)
  have hAp : IsPPerfect 2 A := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hZ₂W := four_group_le_of_nontrivial_commutator A W Z₂ hAp (s.thompson_card s.second)
    hAW hAZ₂ hBZ₂ hne hZ₂fixed
  have hZ₁W : Z₁ ≤ W := by
    have hex : Z₂.map (MulAut.conj t).toMonoidHom = Z₁ := (s.thompson_exchanges t ht hout).2
    rw [←hex]
    exact (map_mono hZ₂W).trans
      (mem_normalizer_iff_map_conj_eq.mp (hMcW (hTMc ht))).le
  have he : W=E := le_antisymm hWE (by
    change thompsonFixed T (localModule T M) ≤ W
    rw [s.thompson_split]
    exact sup_le hZ₁W hZ₂W)
  have hn : centralizer (centralInvolutions T : Set G) ≤ normalizer (E : Set G) :=
    hMc.2.trans (he ▸ hMcW)
  exact ⟨he,hn,h.thompsonFixed_residual_of_normalizes hG T hM hJ hn,
    h.thompsonFixed_normalizers_of_normalizes hG T hM hJ hu hn⟩

end CFSG.Quasithin.Chapter15.Section01
