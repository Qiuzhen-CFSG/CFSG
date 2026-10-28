module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.GroupTheory.ElementarySylowQuinticAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

public import Theory.SpecificGroups.Triality.BinaryPrimeActors
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# The original quintic actor excludes five-free automorphism models

The actual support W and quintic actor Y map into Aut(L/O₂(L)); their
commutator image is the nontrivial image of W. Hence five divides the full
automorphism group of this quotient, retaining the whole central kernel.
No assumption on outer automorphisms or reversed support action is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem raw_quintic_aut_five_divides
    {V Z1 M L Y : Subgroup G} [Group.IsPerfect L]
    (hcenter : center L = pCore 2 L)
    (hY : IsPGroup 5 Y)
    (hYR : Y ≤ (pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype)
    (hnL : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G))
    (hWY : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅⁅V,R⁆,Y⁆ = ⁅V,R⁆)
    (hmove : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅L,⁅V,R⁆⁆ ≠ ⊥)
    {X : Type*} [Group X] (e : (L ⧸ pCore 2 L) ≃* X)
    : 5 ∣ Nat.card (MulAut X) := by
  let : Finite X := Finite.of_equiv (L ⧸ pCore 2 L) e.toEquiv
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      ←hcenter]
  let c : PerfectCentralCovering.Cover L X := ⟨q,hq,inferInstance,hker.le⟩
  let C := M ⊓ centralizer (Z1 : Set G)
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let N := normalizer (L : Set G)
  let f := (c.autMap hker).comp L.normalizerMonoidHom
  have hRN : R ≤ N := le_sup_left.trans hnL
  have hYN : Y ≤ N := hYR.trans hRN
  have hWN : W ≤ N := le_sup_right.trans hnL
  let A := (W.subgroupOf N).map f
  let B := (Y.subgroupOf N).map f
  have hB : IsPGroup 5 B :=
    (hY.of_equiv (subgroupOfEquivOfLe hYN).symm).map f
  have hAB : ⁅A,B⁆ = A := by
    dsimp only [A,B]
    rw [←map_commutator,←SubgroupTransport.subgroupOf_commutator W Y hWN hYN,hWY]
  have hAne : A ≠ ⊥ := by
    intro he
    have hcW : W ≤ centralizer (L : Set G) := by
      intro w hw l hl
      have hh : f ⟨w,hWN hw⟩ = 1 := mem_bot.mp (he ▸ mem_map_of_mem f hw)
      have hh' : L.normalizerMonoidHom ⟨w,hWN hw⟩ = 1 :=
        (c.autMap_injective hker) (hh.trans (map_one (c.autMap hker)).symm)
      have ha := congrArg Subtype.val (DFunLike.congr_fun hh' (⟨l,hl⟩ : L))
      change w*l*w⁻¹=l at ha
      exact (mul_inv_eq_iff_eq_mul.mp ha).symm
    exact hmove (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcW)
  have hBne : B ≠ ⊥ := by
    intro hb
    rw [hb,commutator_bot_right] at hAB
    exact hAne hAB.symm
  have hd : 5 ∣ Nat.card B := by
    rcases hB.card_eq_or_dvd with he | hd
    · exact (hBne (B.eq_bot_of_card_eq he)).elim
    · exact hd
  exact hd.trans B.card_subgroup_dvd_card

/-- The original movement forces a factor five in the full automorphism
group of the same ordinary central quotient. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_aut_five_divides
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
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ {X : Type*} [Group X], (L ⧸ pCore 2 L) ≃* X →
          5 ∣ Nat.card (MulAut X) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hLG hLc hcenter hnL hmove X _ e
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
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  exact raw_quintic_aut_five_divides hcenter hY hYR hnL hWY hmove e

/-- Binary triality and derived binary G₂ are excluded on the actual
ordinary core quotient, without any outer-action assumption. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_binary_exceptions
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
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ¬Nonempty ((L ⧸ pCore 2 L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
        ¬Nonempty ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hLG hLc hcenter hnL hmove
  have hdvd {X : Type} [Group X] (e : (L ⧸ pCore 2 L) ≃* X) :=
    h.decomposable_five_raw_ordinary_aut_five_divides hG T hempty hM hmany hJ hfull
      c d hd s π hp hs hdec hq hfive hLG hLc hcenter hnL hmove e
  constructor
  · rintro ⟨e⟩
    exact Triality.Standard.BinaryPrimeActors.five_not_dvd_card_aut (hdvd e)
  · rintro ⟨e⟩
    have hh := hdvd e
    have hc : Nat.card (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) = 12096 :=
      (Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv).symm.trans
        Atlas.G2.LieAutomorphismExtensions.card_binaryFull
    norm_num [hc] at hh

end CFSG.Quasithin.Chapter15.Section01
