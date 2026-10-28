module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOne
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.SectionKernel
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.OddSubgroups
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.HallFaithfulness
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeModule
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FundamentalHypothesis

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Models
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Configurations
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.BenderExclusion
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Injective

/-!
# The original rank-one orbit in the odd-local argument

Remark 4.4.2 puts every subgroup of N(L) intersect C(W) in the actual
section centralizer of L/O₂(L), including when that quotient has a center.
Consequently the fixed residual covers L and contains the original chosen
module in its two-core. The unitary and Suzuki markings give |W| > 8,
so source 4.4.8 makes W centralize the odd core of the actual odd normalizer.

The original non-FF hypothesis also makes every H-star comparison group
centralize the Sylow omega-center. Its odd section actors therefore fix W,
using Sylow fixed-point generation and perfect fixed-residual covering.
The actual central quotients now exclude every quotient alternative in 4.4.3,
including the central-cover rows. The same comparison applies to every covering
residual. An escaping abelian odd normalizer constructs either a literal C.2.8
pushing-up pair or a moved component of its normalizer with its full Theorem B
model. The two actual markings give binary rank at least twelve. With residual
uniqueness and the precise outer-section exclusion, the component is normal,
has odd centralizer, and contains the residual and W. Rank bounds and the perfect
residual's two-core then exclude every odd, finite and Bender quotient row.

Residual uniqueness, outer-section exclusion and the remaining rank-two
parabolic analysis are still required. The final Hall and E.6.27 applications
retain the abelian normalizer conclusion explicitly.
Source: Aschbacher--Smith, Remark 4.4.2, Lemmas 4.4.5--12 and Proposition
E.6.27, printed pp.619--623,257; applied on pp.699--700.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

include D in
/-- The genuine uniqueness of LT supplies the normalized pushing-up
hypothesis, without assuming uniqueness for the odd fixed residual. -/
theorem sourceOrbit_pushingUp_hypothesis
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    Hypothesis411 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) L := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  apply source_hypothesis411 h
  have hh := (D.fundamentalSetup h).lemma_3_2_3_uniqueness hu
  simpa only [UniqueMaximalOvergroup, Chapter3.Section02.FundamentalSetup.maximalLocal,
    Chapter3.Section02.localJoin, D.localOrbit_eq] using hh

/-- Remark 4.4.2 for the original invariant choice. This is the section
kernel on L/O₂(L), with no simplicity assumption on that quotient. -/
theorem sourceOrbit_relative_centralizer_le_sectionCentralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) :
    normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ≤
      sectionCentralizer L := by
  let := h.quasisimple
  rw [← hV]
  apply relative_module_centralizer_le_sectionCentralizer L V D.normalizes
    _ D.ne_bot D.eq_commutator
  exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes

/-- The literal covering input of 4.2.11 follows for every original odd
actor; the action-kernel hypothesis is proved, not added as a premise. -/
theorem sourceOrbit_oddActorResidual_pushingUp_input
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (B : Subgroup G)
    (hB : B ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hodd : Odd (Nat.card B)) :
    oddActorResidual L B ≤ normalizer (L : Set G) ∧
      (L : Set G) ⊆ (oddActorResidual L B : Set G) *
        ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ∧
      (oddActorResidual L B).pCoreIn 2 ≠ ⊥ ∧
      D.sourceOrbit = ⁅D.sourceOrbit,oddActorResidual L B⁆ ∧
      D.sourceOrbit ≤ (oddActorResidual L B).pCoreIn 2 := by
  have hc := (le_sectionCentralizer_iff B L).mp
    (hB.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hbV : B ≤ centralizer (V : Set G) := hV ▸ hB.trans inf_le_right
  simpa only [hV] using
    chosen_oddActorResidual_pushingUp_input h D B hc.1 hc.2 hodd hbV

private theorem sourceOrbit_card_of_finrank {d : ℕ}
    (hd : Module.finrank (ZMod 2) (Additive D.sourceOrbit) = d) :
    Nat.card D.sourceOrbit = 2 ^ d := by
  rw [Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod, hd] using
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)

/-- The actual unitary module is large enough for the 4.4.8 odd-core
argument; this uses its marked action and binary dimension. -/
theorem sourceOrbit_unitary_card_gt_eight
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) :
    8 < Nat.card D.sourceOrbit := by
  obtain ⟨F, hF, hfin, halg, J, hc, hconj, hmodel, hd⟩ :=
    D.sourceOrbit_unitary_model hs hs2 hq
  rw [D.sourceOrbit_card_of_finrank hd]
  have he : 3 < 6 * s := by omega
  exact (show 8 = 2 ^ 3 by norm_num).trans_lt ((Nat.pow_lt_pow_right (by decide) he))

/-- The Suzuki marking gives the same strict threshold on the literal W. -/
theorem sourceOrbit_suzuki_card_gt_eight
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    8 < Nat.card D.sourceOrbit := by
  obtain ⟨M, he, hd⟩ := D.sourceOrbit_suzuki_model hs hm e
  rw [D.sourceOrbit_card_of_finrank hd]
  have he : 3 < 4 * (2 * m + 1) := by omega
  exact (show 8 = 2 ^ 3 by norm_num).trans_lt ((Nat.pow_lt_pow_right (by decide) he))

private theorem sourceOrbit_oddNormalizer_centralizes_oddCore_of_large
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hcard : 8 < Nat.card D.sourceOrbit)
    (B : Subgroup G)
    (hB : B ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hodd : Odd (Nat.card B)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (B : Set G))).map
      (normalizer (B : Set G)).subtype⁆ = ⊥ := by
  have hc := (le_sectionCentralizer_iff B L).mp
    (hB.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hbV : B ≤ centralizer (V : Set G) := hV ▸ hB.trans inf_le_right
  have hcardV : 8 < Nat.card V := hV ▸ hcard
  simpa only [hV] using chosen_oddNormalizer_centralizes_oddCore_of_large_module
    h D hcardV B hc.1 hc.2 hodd hbV

/-- Source 4.4.8 on the unchanged unitary orbit and actual N_G(B). -/
theorem sourceOrbit_unitary_oddNormalizer_centralizes_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (B : Subgroup G)
    (hB : B ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hodd : Odd (Nat.card B)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (B : Set G))).map
      (normalizer (B : Set G)).subtype⁆ = ⊥ :=
  D.sourceOrbit_oddNormalizer_centralizes_oddCore_of_large h.toHypothesis1221 hV
    (D.sourceOrbit_unitary_card_gt_eight hs hs2 hq) B hB hodd

/-- Source 4.4.8 for the given Suzuki quotient equivalence. -/
theorem sourceOrbit_suzuki_oddNormalizer_centralizes_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (B : Subgroup G)
    (hB : B ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hodd : Odd (Nat.card B)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (B : Set G))).map
      (normalizer (B : Set G)).subtype⁆ = ⊥ :=
  D.sourceOrbit_oddNormalizer_centralizes_oddCore_of_large h.toHypothesis1221 hV
    (D.sourceOrbit_suzuki_card_gt_eight hs hm e) B hB hodd

/-- E.6.27 on the original orbit. Only the abelian instance of the
normalizer theorem is required; arbitrary odd actors have been discharged. -/
theorem sourceOrbit_centralizer_le_of_abelian_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (habel : ∀ B : Subgroup G, B ≠ ⊥ →
      B ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card B) → IsMulCommutative B → normalizer (B : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (j : ℕ∞) < ChapterE.globalR D.sourceOrbit)
    (hn : nPrime (ChapterE.inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ j)
    (hJ : thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) j ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  centralizer_le_of_abelian_odd_control
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon)
    hU hUW hj1 hj hn hJ habel

/-- The original non-FF action forces every H-star comparison group to
centralize the original Sylow omega-center, by source 3.1.8(3). -/
theorem sourceOrbit_hstar_omega_le_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hHF : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,D.localOrbit_eq] using hH
  have hu := F.lemma_3_2_3_uniqueness h127
  have hJ := Chapter7.NormalizedSource.thompson_centralizes
    D.sourceOrbit_weakClosure_setup (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
  have hJF : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (F.moduleSubgroup : Set G) := by
    rwa [D.fundamentalSetup_module h.toHypothesis1221, ← D.sourceOrbit_eq]
  by_contra hz
  exact (F.qrcHypotheses h127 hHF).thompson_moves_of_noncentral_omega
    h.simpleQTKE hu.1 hu.2.2 F.module_ne_bot hz hJF

/-- The invariant original Irr-plus seed is generated by its Sylow fixed
subgroup. Minimality and the p-group fixed-point theorem prove this directly. -/
theorem sourceOrbit_generated_by_sylow_fixed
    (hV : V = D.sourceOrbit) (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    D.sourceOrbit = conjugateSpanBy
      (D.sourceOrbit ⊓ centralizer (T : Set G)) L := by
  let := D.elementary
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    rw [hV]
    exact D.sourceOrbit_weakClosure_setup.normalizes
  let Z := V ⊓ centralizer (T : Set G)
  let U := conjugateSpanBy Z L
  have hUV : U ≤ V := conjugateSpanBy_le inf_le_left D.normalizes
  have hmin := ReducedNormal.subspaceImage_eq_or_le_centralizer
    (L ⊔ (T : Subgroup G)) L le_sup_left D.irrPlus.isIrrPlus U
    (by change U ≤ subspaceImage (L ⊔ (T : Subgroup G)) D.space; rwa [D.image_eq])
    (le_normalizer_conjugateSpanBy Z L)
  change U = subspaceImage (L ⊔ (T : Subgroup G)) D.space ∨ U ≤ centralizer (L : Set G) at hmin
  rw [D.image_eq] at hmin
  rcases hmin with he | hu
  · simpa only [U,Z,hV] using he.symm
  · exfalso
    have hZ := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) V
      T.isPGroup' (IsElementaryAbelian.isPGroup 2 V) hTV D.ne_bot
    apply hZ
    exact bot_unique ((le_conjugateSpanBy Z L).trans ((le_inf hUV hu).trans_eq hc))

/-- The module-centralization step of 4.4.14, with perfect fixed-residual
covering on L/O₂(L), applies to every odd section actor inside the actual H. -/
theorem sourceOrbit_odd_section_actor_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (B : Subgroup G) (hBH : B ≤ H) (hBC : B ≤ sectionCentralizer L)
    (hodd : Odd (Nat.card B)) : B ≤ centralizer (D.sourceOrbit : Set G) := by
  let := D.elementary
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hz := D.sourceOrbit_hstar_omega_le_center h hnon hH
  have hseed : D.sourceOrbit ⊓ centralizer (T : Set G) ≤ centralizer (B : Set G) := by
    intro v hv b hb
    have hvV : v ∈ V := hV.symm ▸ hv.1
    have hvZ : v ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨D.le_sylow hvV, elemPow_eq_one_of_isElementaryAbelian (p := 2) v hvV,hv.2⟩
    obtain ⟨z,hz,rfl⟩ := hz hvZ
    exact congrArg H.subtype (mem_center_iff.mp hz ⟨b,hBH hb⟩)
  have hcore : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    rw [← hV]
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  exact le_centralizer_iff.mp (centralization_in_4_4_14 L B D.sourceOrbit T hBC hodd
    hcore hseed (D.sourceOrbit_generated_by_sylow_fixed hV
      (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1)).1

/-- The literal 4.4.14 Hall-faithfulness conclusion is reduced to the
abelian instance of 4.4.3. All module-generation, section-kernel, Hall
selection and normalizer-escape premises are discharged internally. -/
theorem sourceOrbit_hall_faithful_of_abelian_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (habel : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
      normalizer (A : Set G) ≤ normalizer (L : Set G))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  exact hall_faithful_of_abelian_odd_control h.simpleQTKE T L D.sourceOrbit
    D.sylow_normalizes_component habel hH hlarge
    (fun A hAH hAC ho =>
      D.sourceOrbit_odd_section_actor_centralizes h hmany hV hnon hH A hAH hAC ho)
    B hBM hHall

private def centralQuotientCongr {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem covering_central_quotient {I L : Subgroup G} (hi : I ≤ L)
    (hc : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G)) :
    Nonempty (((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ≃*
      ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L))) := by
  obtain ⟨e,_⟩ := exists_pCoreQuotientEquiv_of_cover (p := 2) (A := I) (L := L) hi hc
  exact ⟨centralQuotientCongr e⟩

/-- Every literal covering subgroup has the same central quotient as the orbit
component. The comparison is induced by the original inclusion and orbit action. -/
theorem sourceOrbit_covering_central_quotient
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {I : Subgroup G} (hi : I ≤ L)
    (hc : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G)) :
    Nonempty (((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ≃*
      (D.orbitComponent ⧸ center D.orbitComponent)) := by
  exact ⟨(Classical.choice (covering_central_quotient hi hc)).trans
    (D.orbitCentralQuotientEquiv h)⟩

/-- The actual unitary quotient excludes every 4.4.3 quotient alternative
for any covering residual, including central covers. -/
theorem sourceOrbit_unitary_cover_not_exceptional
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {I : Subgroup G} (hi : I ≤ L)
    (hc : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G)) :
    ¬ ExceptionalQuotient (I ⧸ pCore 2 I) := by
  obtain ⟨c⟩ := D.sourceOrbit_covering_central_quotient h hi hc
  have hu := hq.of_mulEquiv c
  exact not_exceptional_of_central_quotient (unitary_card_gt_20160 hs2 hu)
    (unitary_not_binary_linear_two hs2 hu)

/-- The Suzuki central-quotient marking gives the same full residual exclusion. -/
theorem sourceOrbit_suzuki_cover_not_exceptional
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {I : Subgroup G} (hi : I ≤ L)
    (hc : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G)) :
    ¬ ExceptionalQuotient (I ⧸ pCore 2 I) := by
  obtain ⟨c⟩ := D.sourceOrbit_covering_central_quotient h hi hc
  exact not_exceptional_of_central_quotient (suzuki_card_gt_20160 hm (c.trans e))
    (suzuki_not_binary_linear_two hm (c.trans e))

/-- The invariant choice supplies the actual C.2.8 counterexample if uniqueness
fails. Its module comparison and all section-centralizer premises are proved. -/
theorem sourceOrbit_pushingUp_case_of_not_unique
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    PushingUpCase L D.sourceOrbit A := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hv : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  simpa only [hV] using pushingUp_case_of_not_unique h D hu A hc.1 hc.2 ho hv hnot

private theorem sourceOrbit_oddActorResidual_cover_at
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    (L : Set G) = (oddActorResidual L A : Set G) * (L.pCoreIn 2 : Set G) := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  exact (chosen_oddActorResidual_cover h D A hc.1 hc.2 ho
    (hV ▸ hA.trans inf_le_right)).1

/-- The original unitary odd fixed residual avoids the complete exceptional
quotient list, through its actual inclusion-induced quotient map. -/
theorem sourceOrbit_unitary_oddActorResidual_not_exceptional
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ¬ ExceptionalQuotient (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) :=
  D.sourceOrbit_unitary_cover_not_exceptional h.toHypothesis1221 hs2 hq
    ((oddActorResidual_le L A).trans inf_le_left)
    (D.sourceOrbit_oddActorResidual_cover_at h.toHypothesis1221 hV A hA ho).subset

/-- The same literal residual calculation for the given Suzuki equivalence. -/
theorem sourceOrbit_suzuki_oddActorResidual_not_exceptional
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ¬ ExceptionalQuotient (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) :=
  D.sourceOrbit_suzuki_cover_not_exceptional h.toHypothesis1221 hm e
    ((oddActorResidual_le L A).trans inf_le_left)
    (D.sourceOrbit_oddActorResidual_cover_at h.toHypothesis1221 hV A hA ho).subset

private theorem sourceOrbit_outside_case_of_large
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hcard : 8 < Nat.card D.sourceOrbit)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    PushingUpCase L D.sourceOrbit A ∨ ComponentCase L D.sourceOrbit A := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hv : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hvcard : 8 < Nat.card V := hV ▸ hcard
  simpa only [hV] using outside_case h D hvcard hu A hne hc.1 hc.2 ho hv hout

/-- An escaping abelian odd normalizer in the unitary row constructs either
an actual C.2.8 pair or an actual moved component of N(A). -/
theorem sourceOrbit_unitary_outside_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    PushingUpCase L D.sourceOrbit A ∨ ComponentCase L D.sourceOrbit A :=
  D.sourceOrbit_outside_case_of_large h.toHypothesis1221 hV
    (D.sourceOrbit_unitary_card_gt_eight hs hs2 hq) A hne hA ho hout

/-- The same constructed alternatives for the independent Suzuki family input. -/
theorem sourceOrbit_suzuki_outside_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    PushingUpCase L D.sourceOrbit A ∨ ComponentCase L D.sourceOrbit A :=
  D.sourceOrbit_outside_case_of_large h.toHypothesis1221 hV
    (D.sourceOrbit_suzuki_card_gt_eight hs hm e) A hne hA ho hout


private theorem sourceOrbit_rank_ge_of_finrank {d : ℕ}
    (hd : Module.finrank (ZMod 2) (Additive D.sourceOrbit) = d) :
    d ≤ primeRank 2 D.sourceOrbit := by
  have hc : Nat.card D.sourceOrbit = 2 ^ d := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod,hd] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
  let : IsElementaryAbelian 2 (⊤ : Subgroup D.sourceOrbit) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup D.sourceOrbit).subtype Subtype.val_injective
  exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup D.sourceOrbit)
    (by simpa only [card_top] using hc)

/-- The actual unitary orbit has binary rank at least twelve. -/
theorem sourceOrbit_unitary_twoRank_ge_twelve
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) :
    12 ≤ primeRank 2 D.sourceOrbit := by
  obtain ⟨F,hF,hfin,halg,J,hc,hconj,hmodel,hd⟩ := D.sourceOrbit_unitary_model hs hs2 hq
  exact (by omega : 12 ≤ 6 * s).trans (D.sourceOrbit_rank_ge_of_finrank hd)

/-- The actual Suzuki orbit has the same uniform lower bound. -/
theorem sourceOrbit_suzuki_twoRank_ge_twelve
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    12 ≤ primeRank 2 D.sourceOrbit := by
  obtain ⟨M,he,hd⟩ := D.sourceOrbit_suzuki_model hs hm e
  exact (by omega : 12 ≤ 4 * (2 * m + 1)).trans (D.sourceOrbit_rank_ge_of_finrank hd)

private theorem sourceOrbit_normal_component_of_unique_and_no_outer_sections
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hcard : 8 < Nat.card D.sourceOrbit)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K →
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) →
      ∀ U : Subgroup (MulAut.Outer K),
      ∀ f : U →* (D.orbitComponent ⧸ center D.orbitComponent), ¬ Function.Surjective f) :
    NormalComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent) := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  have hsect := D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV
  have hc := (le_sectionCentralizer_iff A L).mp (hA.trans hsect)
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hcover := (chosen_oddActorResidual_cover h D A hc.1 hc.2 ho hAV).1
  let e := Classical.choice (D.sourceOrbit_covering_central_quotient h
    ((oddActorResidual_le L A).trans inf_le_left) hcover.subset)
  have hsectV : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L :=
    hV ▸ hsect
  exact normal_component_of_unique_and_no_outer_sections h D
    (show 8 < Nat.card V from hV ▸ hcard) hsectV A hne hc.1 hc.2 ho hAV hu hout e hno


private theorem sourceOrbit_rankTwo_component_of_unique_and_no_outer_sections
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hcard : 8 < Nat.card D.sourceOrbit) (hr : 12 ≤ primeRank 2 D.sourceOrbit)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K →
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) →
      ∀ U : Subgroup (MulAut.Outer K),
      ∀ f : U →* (D.orbitComponent ⧸ center D.orbitComponent), ¬ Function.Surjective f) :
    RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) := by
  have hc := D.sourceOrbit_normal_component_of_unique_and_no_outer_sections
    h hV hcard A hne hA ho hu hout hno
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hrV : 12 ≤ primeRank 2 V := hV ▸ hr
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  simpa only [hV] using rankTwo_component_of_normal_case h D A hsect.1 hsect.2 ho hAV hrV hc

/-- The unitary orbit eliminates all odd, finite and Bender component rows.
The ambient residual uniqueness and exact outer-section premise remain explicit. -/
theorem sourceOrbit_unitary_rankTwo_component_of_unique_no_outer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K →
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) →
      ∀ U : Subgroup (MulAut.Outer K),
      ∀ f : U →* (D.orbitComponent ⧸ center D.orbitComponent), ¬ Function.Surjective f) :
    RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) :=
  D.sourceOrbit_rankTwo_component_of_unique_and_no_outer_sections h.toHypothesis1221 hV
    (D.sourceOrbit_unitary_card_gt_eight hs hs2 hq) (D.sourceOrbit_unitary_twoRank_ge_twelve hs hs2 hq)
    A hne hA ho hu hout hno

/-- The independent Suzuki marking gives the same actual component reduction. -/
theorem sourceOrbit_suzuki_rankTwo_component_of_unique_no_outer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K →
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) →
      ∀ U : Subgroup (MulAut.Outer K),
      ∀ f : U →* (D.orbitComponent ⧸ center D.orbitComponent), ¬ Function.Surjective f) :
    RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) :=
  D.sourceOrbit_rankTwo_component_of_unique_and_no_outer_sections h.toHypothesis1221 hV
    (D.sourceOrbit_suzuki_card_gt_eight hs hm e) (D.sourceOrbit_suzuki_twoRank_ge_twelve hs hm e)
    A hne hA ho hu hout hno


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
