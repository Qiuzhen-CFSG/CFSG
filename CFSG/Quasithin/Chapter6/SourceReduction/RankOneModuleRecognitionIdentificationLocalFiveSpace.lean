module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalLinearFourExclusion
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.SourceApplications
public import Theory.Representation.AlternatingFiveOffenderRecognition
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.PrimeRankZero
public import CFSG.Quasithin.ChapterE.Section03.OddCore
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# The original A5 component moved space in source 6.2.7

The complete B.5 comparison retains the actual minimal offender. Its order
four excludes the symmetric-five row, while component order sixty excludes
all linear-three rows. The remaining offender is a component Sylow, and the
central quotient of the moved space is the natural SL2(4) module.

Two conjugate Sylow four-groups generate A5. Applying the conjugate-generator
bound to the dual action bounds the whole moved space by four dimensions.
The natural quotient already has dimension four, so its fixed kernel is zero.
The B.5 fixed supplement then gives the direct sum with the component fixed
space. All conclusions are transported back from the normal offender subgroup
to the original action and offender.

The companion Chapter 12 module applies this to the literal field-plane
quotient. The remaining Sylow-normalizer contradiction and graph escape are
still required for LocalAnalysis.
Source: Aschbacher--Smith 6.2.7, printed pp.683--684; B.5.9--10, pp.107--109.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction

private theorem linear_three_not_five (F : BinaryField)
    {D : Type*} [Group D] (hc : Nat.card D = 60) (e : D ≃* SL(3,F.Carrier)) : False := by
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  have hh : 168 ≤ Nat.card SL(3,F.Carrier) := by
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    calc
      168 = 2^3*(2^3-1)*(2^2-1) := by norm_num
      _ ≤ _ := by gcongr
  rw [←Nat.card_congr e.toEquiv,hc] at hh
  omega

private theorem five_preliminary
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hyp : FFHypothesis KnownSimple.IsKnownSimple ρ)
    {K A : Subgroup D} (hK : IsComponent D K) (hA : IsMinimalBestOffender ρ A)
    (hKA : ⁅K,A⁆ = K) (hAc : Nat.card A = 4) (hKc : Nat.card K = 60)
    (p : Prepared ρ KnownSimple.IsKnownSimple hKA)
    (q : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hKA) (seedComponentImage ρ hKA))
    (s : MovedSection ρ K) :
    ∃ F : BinaryField, IsLinearNatural (s.action.comp K.subtype) F 2 ∧
      (∃ S : Sylow 2 K, A = (S : Subgroup K).map K.subtype) ∧
      s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤ := by
  have hr : primeRank 3 K = 1 := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hu : primeRank 3 K ≤ 1 := primeRank_le_one_of_square_not_dvd (by rw [hKc]; decide)
    have hn : primeRank 3 K ≠ 0 := by
      intro he
      have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp he
      rw [hKc] at hh
      exact hh (by decide)
    omega
  have hcomp := comparedCase_of_source ρ ChapterB.NaturalExtensions.earlierB48Two
    hyp hA hK hKA p hr q
  have hpre := preliminary_of_local_alternative ρ hyp hA hK hKA s p
    (hcomp.toLocalAlternative ρ)
  cases hpre with
  | classified H hc =>
    cases hc with
    | linearTwo F hn hsyl hs => exact ⟨F,hn,hsyl,hs⟩
    | symmetricFive e hcard hs => omega
    | doubleThree F ho hn hAL hs =>
      obtain ⟨e⟩ := hn
      exact (linear_three_not_five F hKc e.groupEquiv).elim
    | naturalThree F ho hn hinner =>
      obtain ⟨e⟩ := hn
      exact (linear_three_not_five F hKc e.groupEquiv).elim
    | fourCover cover hk hAL hs =>
      exact (linear_three_not_five BinaryField.two hKc cover.natural.groupEquiv).elim
  | naturalSeed seed =>
    exact (linear_three_not_five seed.field hKc seed.natural.groupEquiv).elim


private theorem field_four_of_five (F : BinaryField)
    {D : Type*} [Group D] (hc : Nat.card D = 60) (e : D ≃* SL(2,F.Carrier)) :
    F.degree = 2 := by
  have hh := (Nat.card_congr e.toEquiv).symm.trans hc
  rw [GorensteinWalter.sl2_card_formula] at hh
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  have hb : Nat.card F.Carrier ≤ 5 := by
    by_contra h
    have hlarge : 6 ≤ Nat.card F.Carrier := by omega
    have hsq : 36 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
    have hsub : 35 ≤ Nat.card F.Carrier ^ 2 - 1 := by omega
    nlinarith
  have hfour : Nat.card F.Carrier = 4 := by
    generalize Nat.card F.Carrier = q at hh hq hb ⊢
    interval_cases q <;> norm_num at *
  apply Nat.pow_right_injective (by decide : 1 < 2)
  change 2 ^ F.degree = 2 ^ 2
  rw [←F.card_eq,hfour]

private theorem five_section_natural
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {K A : Subgroup D}
    (s : MovedSection ρ K) (eK : K ≃* alternatingGroup (Fin 5))
    (hAc : Nat.card A = 4) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (F : BinaryField) (hn : IsLinearNatural (s.action.comp K.subtype) F 2)
    (hsyl : ∃ S : Sylow 2 K, A = (S : Subgroup K).map K.subtype)
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    F.degree = 2 ∧ IsLinearNatural (s.space.toRepresentation.comp K.subtype) F 2 ∧
      IsCompl s.space.toSubmodule (fixedSpace ρ K) := by
  obtain ⟨e⟩ := hn
  have hKc : Nat.card K = 60 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hF := field_four_of_five F hKc e.groupEquiv
  have hdF : Module.finrank (ZMod 2) F.Carrier = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq,hF] at hh
    exact (Nat.pow_right_injective (by decide : 1 < 2) hh).symm
  have hquot : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 := by
    rw [e.linearEquiv.finrank_eq,Module.finrank_pi_fintype,hdF]
    norm_num
  obtain ⟨S,hS⟩ := hsyl
  have hSc : Nat.card S = 4 := by
    rw [hS,card_map_of_injective K.subtype_injective] at hAc
    exact hAc
  obtain ⟨g,hgen⟩ := AlternatingFiveOffenderRecognition.conjugate_generation
    eK.toMonoidHom eK.surjective (by rw [(MonoidHom.ker_eq_bot_iff _).mpr eK.injective]; exact bot_le)
    (S : Subgroup K) S.isPGroup' (by rw [card_map_of_injective eK.injective]; exact hSc)
  have hdual : fixedCodim (Representation.dual (ρ.comp K.subtype)) (S : Subgroup K) ≤ 2 := by
    rw [fixedCodim_dual_eq_moved_finrank]
    change Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp K.subtype) ⊤ (S : Subgroup K)) ≤ 2
    rw [subspaceCommutator_comp_map,←hS]
    exact hd
  have hbound := AlternatingFiveOffenderRecognition.fixed_quotient_degree_le_four
    (Representation.dual (ρ.comp K.subtype)) (S : Subgroup K) g hgen hdual
  rw [fixedCodim_dual_eq_moved_finrank] at hbound
  change Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤) ≤ 4 at hbound
  rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hbound
  have hdW : Module.finrank (ZMod 2) s.space.toSubmodule ≤ 4 := s.space_eq.symm ▸ hbound
  have hc : s.central.toSubmodule = ⊥ := by
    have hh := Submodule.finrank_quotient_add_finrank s.central.toSubmodule
    rw [hquot] at hh
    exact Submodule.finrank_eq_zero.mp (by omega)
  let b := s.central.toSubmodule.quotEquivOfEqBot hc
  let a : ActionEquiv (s.space.toRepresentation.comp K.subtype) (linearNatural F 2) := {
    groupEquiv := e.groupEquiv
    linearEquiv := b.symm.trans e.linearEquiv
    intertwines k w := by
      change e.linearEquiv (Submodule.Quotient.mk _) = _
      exact e.intertwines k (Submodule.Quotient.mk w) }
  have hz : Representation.invariants (s.space.toRepresentation.comp K.subtype) = ⊥ :=
    ExtensionConsequences.invariants_of_equiv a
      (ExtensionConsequences.linearNatural_invariants F (by decide))
  exact ⟨hF,⟨a⟩,ExtensionConsequences.moved_disjoint_fixed s hz,
    codisjoint_iff.mpr (ProductGeometry.sylow_supplement s ⟨S,hS⟩ hs)⟩


/-- A component A5 moved by the actual minimal four-group acts naturally on
its whole moved space. The same offender is a Sylow subgroup of the component,
and the moved space complements the component fixed space. -/
theorem alternating_component_natural
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    {K A : Subgroup D} (hK : IsComponent D K) (hA : IsMinimalBestOffender ρ A)
    (hKA : ⁅K,A⁆ = K) (hAc : Nat.card A = 4)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (eK : K ≃* alternatingGroup (Fin 5)) :
    (∃ F : BinaryField, F.degree = 2 ∧
      IsLinearNatural ((invariantSubspace ρ K (moved ρ K)
        (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) F 2) ∧
      (∃ S : Sylow 2 K, A = (S : Subgroup K).map K.subtype) ∧
      IsCompl (moved ρ K) (fixedSpace ρ K) := by
  let N := offenderSubgroup ρ
  let σ := ρ.comp N.subtype
  obtain ⟨hKN,hAN,hcomm,p,⟨q⟩,hseed,hm⟩ :=
    component_marked_seed_of_minimal_plane ρ hf hcore cover hK hA hKA hd
  let K0 := K.subgroupOf N
  let A0 := A.subgroupOf N
  let eN : K0 ≃* K := subgroupOfEquivOfLe hKN
  let : K0.Normal := p.component_normal
  let s := MovedSection.ofNormal σ K0
  have hA0 : IsMinimalBestOffender σ A0 := by
    let : IsElementaryAbelian 2 A := hA.1.1.2
    apply Preparation.minimal_of_injective_image ρ N.subtype N.subtype_injective
      (IsElementaryAbelian.subgroupOf hAN)
    rwa [map_subgroupOf_eq_of_le hAN]
  have hAc0 : Nat.card A0 = 4 := (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans hAc
  have hKc : Nat.card K0 = 60 := by
    rw [Nat.card_congr (eN.trans eK).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd0 : Module.finrank (ZMod 2) (moved σ A0) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp N.subtype) ⊤ (A.subgroupOf N)) ≤ 2
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAN]
    exact hd
  obtain ⟨F,hn,hsyl,hs⟩ := five_preliminary σ (offenderSubgroup_hypothesis ρ hf hcore cover)
    (hK.subgroupOf hKN) hA0 hcomm hAc0 hKc p q s
  obtain ⟨hF,⟨a⟩,hc⟩ := five_section_natural σ s (eN.trans eK) hAc0 hd0 F hn hsyl hs
  have he : s.space.toSubmodule = moved ρ K := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp N.subtype) ⊤ (K.subgroupOf N) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKN]
  let b : ActionEquiv ((invariantSubspace ρ K (moved ρ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation)
      (s.space.toRepresentation.comp K0.subtype) :=
    ⟨eN.symm,(LinearEquiv.ofEq _ _ he).symm,fun k w => by apply Subtype.ext; rfl⟩
  refine ⟨⟨F,hF,⟨ThreeCovers.transAction b a⟩⟩,?_,?_⟩
  · obtain ⟨S,hS⟩ := hsyl
    refine ⟨S.mapSurjective (f := eN.toMonoidHom) eN.surjective,?_⟩
    have hh := congrArg (fun X : Subgroup N => X.map N.subtype) hS
    rw [map_subgroupOf_eq_of_le hAN,map_map] at hh
    change A = ((S : Subgroup K0).map eN.toMonoidHom).map K.subtype
    rw [map_map]
    exact hh
  · rw [he] at hc
    have hfix : fixedSpace σ K0 = fixedSpace ρ K := by
      rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hKN]
    rwa [hfix] at hc

/-- E.3.40 and Fitting self-centralization select a component actually moved
by the original offender. Its established Sylow containment makes it unique. -/
theorem exists_unique_moved_component
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) {A : Subgroup D} (hA : IsBestOffender ρ A)
    (hfam : A ∈ ChapterE.fixedSpaceFamily ρ 2)
    (hcontained : ∀ K, IsComponent D K → ⁅K,A⁆ = K → A ≤ K) :
    ∃ K, IsComponent D K ∧ ⁅K,A⁆ = K ∧
      ∀ J, IsComponent D J → ⁅J,A⁆ = J → J = K := by
  have hfit : A ≤ centralizer (fittingSubgroup D : Set D) :=
    (ChapterE.lemma_E_3_40 ρ hf hfam).trans
      (centralizer_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
  obtain ⟨K,hK,hm⟩ := exists_component_moved ρ hcore hA hfit
  have hn : A ≤ normalizer (K : Set D) :=
    (hA.le_offenderSubgroup ρ).trans (ChapterB.offenderSubgroup_le_normalizer_component ρ hf hK)
  have hKA := hK.commutator_eq_self_of_normalizes hn hm
  refine ⟨K,hK,hKA,?_⟩
  intro J hJ hJA
  by_contra hne
  have hh : ⁅J,A⁆ ≤ ⊥ := by
    calc
      ⁅J,A⁆ ≤ ⁅J,K⁆ := commutator_mono le_rfl (hcontained K hK hKA)
      _ = ⊥ := hJ.commutator_eq_bot_of_ne hK hne
  rw [hJA] at hh
  exact hJ.isCComponent.ne_bot (bot_unique hh)


/-- The original marked plane section with the full natural A5 moved spaces. -/
@[expose] def PlaneNaturalSection {G : Type*} [Group G] [Finite G]
    (B A U : Subgroup G) [IsElementaryAbelian 2 (LocalFieldQuotientAction.space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range
        (Additive (LocalFieldQuotientAction.space B U)))
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ IsQuadratic ρ I ∧ Nat.card I = 4 ∧
      moved ρ I = c.imageSpace ⁅A,B⁆ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2 ∧
      fixedCodim ρ I = 2 ∧ I ∈ ChapterE.fixedSpaceFamily ρ 2 ∧
      IsMinimalBestOffender ρ I ∧
      (∀ K, IsComponent (LocalFieldQuotientAction.action B U).range K → ⁅K,I⁆ = K →
        IsIrrPlus ρ K (moved ρ K) ∧
          Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
          (∃ F : BinaryField, F.degree = 2 ∧
            IsLinearNatural ((invariantSubspace ρ K (moved ρ K)
              (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) F 2) ∧
          (∃ S : Sylow 2 K, I = (S : Subgroup K).map K.subtype) ∧
          IsCompl (moved ρ K) (fixedSpace ρ K)) ∧
      (∃ K, IsComponent (action B U).range K ∧ ⁅K,I⁆ = K ∧
        ∀ J, IsComponent (action B U).range J → ⁅J,I⁆ = J → J = K) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)


/-- Upgrade the original section without changing its representation, offender,
coordinates or ambient quotient. The actual moved component is unique. -/
theorem plane_natural_of_alternating
    {G : Type*} [Group G] [Finite G] (B A U : Subgroup G)
    [IsElementaryAbelian 2 (space B U)]
    (hcore : pCore 2 (action B U).range = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple (action B U).range)
    (hs : PlaneAlternatingSection B A U) : PlaneNaturalSection B A U := by
  obtain ⟨ρ,c,hf,hI,hq,hIc,hm,hd,hcodim,hfam,hmin,hmodels,hmark⟩ := hs
  have hn := fun K hK hKI => alternating_component_natural ρ hf hcore cover
    hK hmin hKI hIc hd.le (hmodels K hK hKI).2.some
  have hex := exists_unique_moved_component ρ hf hcore hmin.1 hfam (by
    intro K hK hKI
    obtain ⟨S,hS⟩ := (hn K hK hKI).2.1
    rw [hS]
    exact map_subtype_le _)
  refine ⟨ρ,c,hf,hI,hq,hIc,hm,hd,hcodim,hfam,hmin,?_,hex,hmark⟩
  intro K hK hKI
  exact ⟨(hmodels K hK hKI).1,(hmodels K hK hKI).2,hn K hK hKI⟩

/-- Source 6.2.7's A5 natural-space conclusion on the literal centralizer
quotient. Both the trivial two-core and the SQTK cover follow from the original
field-plane hypotheses. -/
theorem field_plane_natural
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R A U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n) (hUc : Nat.card U = 4)
    [IsElementaryAbelian 2 (space (layer L R) U)]
    (hs : PlaneAlternatingSection (layer L R) A U) :
    PlaneNaturalSection (layer L R) A U := by
  let B := layer L R
  let H := Centralizer U
  let f := action B U
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  let cover : SQTKQuotient KnownSimple.IsKnownSimple f.range := {
    Cover := H
    kernel := f.ker
    sqtk := by
      let j : H →* normalizer (U : Set G) := inclusion (Subgroup.centralizer_le_normalizer _)
      have hsqtk := local_field_normalizer_sqtk h hfield hUne
      exact ⟨hsqtk.stronglyQuasithin.of_injective j (inclusion_injective _),
        hsqtk.isKGroup.of_injective j (inclusion_injective _)⟩
    equiv := QuotientGroup.quotientKerEquivRange f }
  exact plane_natural_of_alternating B A U
    (action_range_core h hnatural hE hfactor hfield hUc.ge) cover hs

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
