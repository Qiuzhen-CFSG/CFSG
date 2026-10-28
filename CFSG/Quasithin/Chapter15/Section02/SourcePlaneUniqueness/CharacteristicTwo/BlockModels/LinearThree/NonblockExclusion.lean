module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.NaturalCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications

/-!
# The preliminary binary non-block exclusion in original 15.2.23

Apply C.1.34 to the genuine constituent MS pair XQI, whose construction
has already identified O₂(C_XQI(ZS)) with QI. The doubled row is excluded
by its actual offender action. In the two nonabelian rows, the natural
central layer gives equality with the local Sylow omega-center centralizer,
contradicting those rows' literal radical inequalities. The central-omega
row contradicts escape. Exactly the natural L₃(2)-block row remains.

The original radical R=O₂(M∩I) supplies the initial MS input and escape;
its description is not transferred wholesale to XQI. Individual constituents
are used throughout, so the proof also covers an S-exchanged component.
The final theorem applies this construction to the literal C.2.7(g) branch.

The argument `classify` is exactly the universal `linearThree` field of
`MarkedMS.EarlierMSClassifications`, owned by qt-rank-two-ms93. It remains
explicit for discharge by qt-e-152-plane-characteristic-two and qt-theorem-e.
The earlier Kc orbit alternative retains its plane-geometry and
small-parabolic producers. No local action, core-comparison, or block
exclusion callback remains. This completes this conditional preliminary
family, not the full characteristic-two contradiction of 15.2.23.

Source: Aschbacher--Smith C.1.34, pp.136--137, C.2.7(3)(g), p.145,
and preliminary 15.2.23, pp.1115--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable (classify : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
  SmallMSPair KnownSimple.IsKnownSimple L R → ∀ (n : ℕ), 1 ≤ n →
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
  Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
  ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      MSModuleAlternatives L R S n F e)
include d classify

/-- On the actual constituent extension XQI, the full C.1.34 input leaves
only the natural block. Both nonabelian rows use the proved omega-center
core comparison, and the doubled row uses its actual offender action. -/
theorem linearThree_component_isBlock_of_classification
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (eX : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ X.map I.subtype ≤ Mc) :
    ChapterC.IsBlock X ∧ ChapterC.IsSL3EvenBlock (X.map I.subtype) 1 := by
  let L := X.map I.subtype
  let R := planeParabolicCore T H ZS
  let S := planeSylow T ZS ⊓ (L ⊔ R)
  have hms := d.linearThree_component_msPair_of_escape hI hfit hX eX hout
  have hodd := (d.linearThree_component_ms_odd_index hI hX eX hout).1
  have hQI : R ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hn : R ≤ normalizer (L : Set G) := by
    rw [←map_subgroupOf_eq_of_le hQI]
    exact (map_mono (d.linearThree_parabolic_core_normalizes_component hI hX eX)).trans
      (le_normalizer_map I.subtype)
  have hsmall := linearThree_smallMSPair_of_odd_index hms hodd hn
  have hS := d.linearThree_component_extension_sylow hI hX eX
  have hRS : R ≤ S := le_inf (d.planeParabolicCore_le_plane hI) le_sup_right
  obtain ⟨e,hcases⟩ := classify G L R hsmall 1 (by decide) (ZMod 2)
    (by norm_num [Nat.card_eq_fintype_card]) hms.model S hS hRS
  rcases hcases with h | h | h | h | h
  · let a : X ≃* L := X.equivMapOfInjective I.subtype I.subtype_injective
    exact ⟨⟨inferInstance,h.2.1.2.1.of_mulEquiv a.symm,hX.subnormal⟩,h.2.1⟩
  · obtain ⟨hc,hcard⟩ := binary_doubled_section_data (by norm_num [Nat.card_eq_fintype_card]) e h.1
    exact (d.linearThree_component_no_doubled_core hI hfit hX eX hout hc hcard).elim
  · have he := d.linearThree_component_omega_core_of_natural_layer hI hfit hX eX hout e h.1
      (le_normalizer_iff_commutator_le_left.mp h.1.2.1)
    exact (h.2.2 he.symm).elim
  · obtain ⟨_,_,_,_,_,hm,_,_,_,hneq⟩ := h
    have he := d.linearThree_component_omega_core_of_natural_layer hI hfit hX eX hout e hm le_rfl
    exact (hneq he.symm).elim
  · exact (d.plane_extension_omega_not_central hI hfit hout h.2.2.2.1).elim

/-- The preliminary source application retains the original radical R.
Its genuine MS hypotheses give escape; the actual XQI construction and
classification then prove the block conclusion without transporting R. -/
theorem linearThree_component_isBlock_of_source
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (eX : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    {R : Subgroup G} (hR : IsPGroup 2 R) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype) R n F) :
    ChapterC.IsBlock X ∧ ChapterC.IsSL3EvenBlock (X.map I.subtype) 1 :=
  d.linearThree_component_isBlock_of_classification classify hI hfit hX eX
    (d.linearThree_ms_component_not_le_partner horbit hI hX eX hR hms)

/-- The literal binary C.2.7(g) branch is an L₃(2)-block. All ordinary
constituent, action and omega-center premises are discharged here. -/
theorem LinearThree.Branch.binary_isBlock
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : LinearThree.Branch M I X 1 F) :
    ChapterC.IsBlock (X.subgroupOf I) ∧ ChapterC.IsSL3EvenBlock X 1 := by
  let A := X.subgroupOf I
  let a : A ≃* X := subgroupOfEquivOfLe b.input.component.1
  obtain ⟨e⟩ := b.ms.1.model
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [←Nat.card_eq_fintype_card,pow_one] using b.field_card)).symm
  let eA : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL :=
    (((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e).trans
      (Atlas.fieldEquivSL 3 f)).trans Matrix.PSL3Two.equiv
  have hA : A.map I.subtype = X := map_subgroupOf_eq_of_le b.input.component.1
  have hout : ¬ A.map I.subtype ≤ Mc := hA.symm ▸ b.binary_not_le_partner d horbit hI
  have hh := d.linearThree_component_isBlock_of_classification classify hI hfit
    b.input.component.2 eA hout
  exact ⟨hh.1,hA ▸ hh.2⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
