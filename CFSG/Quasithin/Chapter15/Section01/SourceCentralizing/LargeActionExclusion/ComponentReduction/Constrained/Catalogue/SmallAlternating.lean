module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Block
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
public import Theory.GroupTheory.NormalCentralQuotientAction.Maps

/-!
# Small alternating rows on the original component and radical

The A₆ and A₇ FF markings identify L/O₂,Z(L), preserving the original
map on every element. An alternating central quotient of degree at least
six has three-rank at least two. If the core quotient had three-rank at
most one, its cyclic Sylow image would contradict that bound. The original
local-family rank theorem therefore proves S-normalization, even when the
member is not an ambient C-component.

For the selected component this supplies Q₁-normalization and the actual
C.2.7 input. The FF and star central quotients are identified through their
two perfect central covers, with the original maps retained. In the
six-point row, M_Z supplies the odd-index radical and all three MS
conditions hold on the literal LQ₁. This treats both the ordinary FF image
and its cubic cover, without assuming that Q₁ is Sylow or removing a center.

The original marker retains either prime and the exchanged applications
retain either plane size. The final block implication is conditional only
on the independently owned AlternatingSixReconstructionInput, whose producer
is qt-e-ms-small-a6-reconstruction. Its natural and exceptional outcomes
remain distinct. This module does not assert catalogue exhaustiveness:
small-block exclusions and geometry, general-family Borel placement, and
all remaining catalogue clauses stay with this owner. Original 15.1.14
retains its existing producer and final assembly owner.

Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095;
C.1.31--32 and C.2.7, printed pp.135--136,145--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private def alternatingCover {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (e : d.normalizerImage K ≃* alternatingGroup (Fin n)) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) (alternatingGroup (Fin n)) where
  toMonoidHom := e.toMonoidHom.comp a.coreToImage
  surjective := e.surjective.comp a.coreToImage_surjective
  isPerfect := hq.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact a.coreToImage_ker_central hq

/-- The actual alternating FF marking descends to the literal O₂,Z quotient. -/
noncomputable def NormalizerAction.alternating_coreCenterEquiv
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hn : 5 ≤ n) (e : d.normalizerImage K ≃* alternatingGroup (Fin n)) :
    (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin n) :=
  (centralPreimageQuotientEquiv (pCore 2 K)).trans
    ((alternatingCover a hq e).quotientCenterEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))).trans QuotientGroup.quotientBot))

/-- The central-quotient marking agrees with the original action on every element. -/
theorem NormalizerAction.alternating_coreCenterEquiv_mk
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hn : 5 ≤ n) (e : d.normalizerImage K ≃* alternatingGroup (Fin n)) (k : K) :
    a.alternating_coreCenterEquiv hq hn e
      (QuotientGroup.mk' (centralPreimage (pCore 2 K)) k) = e (d.toNormalizerImage K k) := by
  rw [NormalizerAction.alternating_coreCenterEquiv, MulEquiv.trans_apply,
    centralPreimageQuotientEquiv_mk]
  rfl

/-- An alternating central quotient forces normalization on the full local family. -/
theorem localFamily_alternating_central_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hn : 6 ≤ n)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin n)) :
    d.S ≤ normalizer (K : Set G) := by
  apply d.localFamily_normalizes_of_oddRank hG h hK hq Nat.prime_three (by decide)
  let f := ((centralPreimageQuotientEquiv (pCore 2 K)).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (center (K ⧸ pCore 2 K)))
  have hf : Function.Surjective f :=
    ((centralPreimageQuotientEquiv (pCore 2 K)).symm.trans e).surjective.comp
      (QuotientGroup.mk'_surjective _)
  by_contra hr
  let P : Sylow 3 (K ⧸ pCore 2 K) := Classical.choice inferInstance
  have hh := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) f hf
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 3 Nat.prime_three (by decide)] at hh
  omega

/-- The original two perfect central covers identify the FF and star central quotients. -/
noncomputable def NormalizerAction.starCenterEquiv
    {d : CaseIComponentData T M Mc V} (a : d.NormalizerAction d.L)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L) :
    (starImage d.L d.Q1 d.L ⧸ center (starImage d.L d.Q1 d.L)) ≃*
      (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) := by
  let c : PerfectCentralCovering.Cover (d.L ⧸ pCore 2 d.L) (starImage d.L d.Q1 d.L) := {
    toMonoidHom := coreToStar hi.normalizes
    surjective := coreToStar_surjective hi.normalizes
    isPerfect := hi.quasisimple.toIsPerfect
    ker_le_center := coreToStar_ker_central_from_source hi }
  exact c.quotientCenterEquiv.symm.trans (a.coreCover hi.quasisimple).quotientCenterEquiv

/-- This comparison preserves the literal core-to-star and FF maps. -/
theorem NormalizerAction.starCenterEquiv_mk
    {d : CaseIComponentData T M Mc V} (a : d.NormalizerAction d.L)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L) (k : d.L) :
    a.starCenterEquiv hi
      (QuotientGroup.mk' (center (starImage d.L d.Q1 d.L))
        (coreToStar hi.normalizes (QuotientGroup.mk' (pCore 2 d.L) k))) =
      QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k) := by
  let c : PerfectCentralCovering.Cover (d.L ⧸ pCore 2 d.L) (starImage d.L d.Q1 d.L) := {
    toMonoidHom := coreToStar hi.normalizes
    surjective := coreToStar_surjective hi.normalizes
    isPerfect := hi.quasisimple.toIsPerfect
    ker_le_center := coreToStar_ker_central_from_source hi }
  change (a.coreCover hi.quasisimple).quotientCenterEquiv
    (c.quotientCenterEquiv.symm (c.quotientCenterEquiv
      (QuotientGroup.mk' (center (d.L ⧸ pCore 2 d.L))
        (QuotientGroup.mk' (pCore 2 d.L) k)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The literal alternating central quotient forces Q₁-normalization.
No triviality of the central kernel is assumed. -/
theorem PreExclusionSource.constrained_alternating_central_input
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) (hn : 6 ≤ n)
    (e : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin n)) :
    d.S ≤ normalizer (d.L : Set G) ∧
      Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L := by
  have hSL := d.localFamily_alternating_central_normalizes hG h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hn e
  exact ⟨hSL,s.constrained_input_of_normalizes (h := h) hG hf
    ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans hSL)⟩

/-- Both original small alternating FF rows have the literal central quotient
and full C.2.7 input. The original action marking is retained. -/
theorem PreExclusionSource.constrained_small_alternating_input
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) (hn : n = 6 ∨ n = 7)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin n)) :
    d.S ≤ normalizer (d.L : Set G) ∧
      Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
      ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin n),
        ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
          e (d.toNormalizerImage d.L k) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  let t := a.alternating_coreCenterEquiv s.quasisimple (by omega) e
  have hi := s.constrained_alternating_central_input (h := h) hG hu hf (by omega) t
  exact ⟨hi.1,hi.2,t,a.alternating_coreCenterEquiv_mk s.quasisimple (by omega) e⟩

/-- The two source quotients have the same marked alternating central quotient.
This comparison does not discard a possible cubic center in either quotient. -/
theorem PreExclusionSource.constrained_alternating_star_comparison
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) (hn : 6 ≤ n)
    (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin n)) :
    ∃ hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L,
      ∃ t : (starImage d.L d.Q1 d.L ⧸ center (starImage d.L d.Q1 d.L)) ≃*
        alternatingGroup (Fin n),
        ∀ k : d.L, t (QuotientGroup.mk' (center (starImage d.L d.Q1 d.L))
          (coreToStar hi.normalizes (QuotientGroup.mk' (pCore 2 d.L) k))) =
          e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  have hi := (s.constrained_alternating_central_input (h := h) hG hu hf hn
    ((a.coreCenterQuotientEquiv s.quasisimple).trans e)).2
  exact ⟨hi,(a.starCenterEquiv hi).trans e,fun k =>
    congrArg e (a.starCenterEquiv_mk hi k)⟩

/-- The actual A₆ central quotient supplies all three MS conditions on LQ₁,
for both the ordinary FF row and its cubic cover. -/
theorem PreExclusionSource.constrained_six_msPair
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) :
    SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
      ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
        ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
          e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  let t := (a.coreCenterQuotientEquiv s.quasisimple).trans e
  obtain ⟨hi,_,_⟩ := s.constrained_alternating_star_comparison (h := h)
    hG hempty hM hJ hu hf (by decide) e
  let es := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  exact ⟨Chapter14.Section06.smallMSPair_from_c27 hi
    (d.constrained_msOddIndexRadical hi s.centralizer_sylow hu)
    (Or.inr (Or.inl ⟨es⟩)),t,fun k =>
      congrArg e (a.coreCenterQuotientEquiv_mk s.quasisimple k)⟩

/-- The ordinary A₆ FF image also supplies the full MS-pair directly,
without assuming a marking of its central quotient. -/
theorem PreExclusionSource.constrained_six_msPair_of_image
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) :
    SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 := by
  obtain ⟨_,hi,t,_⟩ := s.constrained_small_alternating_input (h := h)
    hG hempty hM hJ hu hf (Or.inl rfl) e
  let es := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  exact Chapter14.Section06.smallMSPair_from_c27 hi
    (d.constrained_msOddIndexRadical hi s.centralizer_sylow hu) (Or.inr (Or.inl ⟨es⟩))

/-- Apply the independently owned A₆ whole-core theorem to the original FF row.
Its natural and exceptional alternatives are both retained. -/
theorem PreExclusionSource.constrained_six_blocks_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) :
    IsAlternatingBlock d.L 6 ∨ IsExceptionalAhat6Block d.L := by
  obtain ⟨hm,t,_⟩ := s.constrained_six_msPair (h := h) hG hempty hM hJ hu hf e
  let es := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  have r := ha G d.L d.Q1 hm es
  have hs := hm.short_of_core r.elementary r.central s.quasisimple r.irreducible
  rcases r.model with hn | ⟨hz,hu,hc⟩
  · exact Or.inl ⟨by decide,hs,hn⟩
  · exact Or.inr ⟨hs,s.quasisimple,hz,
      ⟨(centralPreimageQuotientEquiv (pCore 2 d.L)).symm.trans t⟩,hu,hc⟩

/-- Either exchanged plane size preserves the small alternating quotient marking
and supplies the same C.2.7 hypotheses. -/
theorem ExchangedSource.constrained_small_alternating_input
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin n)) :
    d.S ≤ normalizer (d.L : Set G) ∧
      Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
      ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin n),
        ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
          e (d.toNormalizerImage d.L k) := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    hK s.quasisimple d.L_not_le_MZ hf
  let t := a.alternating_coreCenterEquiv s.quasisimple (by omega) e
  have hSL := d.localFamily_alternating_central_normalizes hG h hK s.quasisimple (by omega) t
  exact ⟨hSL,s.constrained_input_of_normalizes hG h hf
    ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans hSL),t,
    a.alternating_coreCenterEquiv_mk s.quasisimple (by omega) e⟩

/-- The exchanged source also supplies the literal small MS-pair on its original L and Q₁. -/
theorem ExchangedSource.constrained_six_msPair
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
      alternatingGroup (Fin 6)) :
    SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    hK s.quasisimple d.L_not_le_MZ hf
  let t := (a.coreCenterQuotientEquiv s.quasisimple).trans e
  have hn := d.localFamily_alternating_central_normalizes hG h hK s.quasisimple (by decide) t
  have hi := s.constrained_input_of_normalizes hG h hf
    ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans hn)
  let es := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  exact Chapter14.Section06.smallMSPair_from_c27 hi
    (d.constrained_msOddIndexRadical hi s.centralizer_sylow hu) (Or.inr (Or.inl ⟨es⟩))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- At the actual original marker, both small alternating rows have C.2.7 input,
and the six-point central-quotient row has the full MS-pair. The same Z₁, row,
prime and independent original 15.1.14 premise are retained. -/
theorem PreparedChosenModule.source_preExclusion_small_alternating_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        (∀ n, n = 6 ∨ n = 7 →
          (d.normalizerImage d.L ≃* alternatingGroup (Fin n)) →
          d.S ≤ normalizer (d.L : Set G) ∧
            Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
            (n = 6 → SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)) ∧
        (((d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
          alternatingGroup (Fin 6)) → SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hf => ⟨?_,?_⟩⟩
  · intro n hn e
    obtain ⟨hN,hi,_⟩ := s.constrained_small_alternating_input (h := h)
      hG hempty hM hJ hu hf hn e
    refine ⟨hN,hi,?_⟩
    rintro rfl
    exact s.constrained_six_msPair_of_image (h := h) hG hempty hM hJ hu hf e
  · intro e
    exact (s.constrained_six_msPair (h := h) hG hempty hM hJ hu hf e).1

end CFSG.Quasithin.Chapter15.Section01
