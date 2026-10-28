module
public import Theory.GroupTheory.PGroup.SecondCenterCommutator
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NaturalOmegaCore
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterSquares
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralDerivedSections

/-!
# A canonical central image for the upper-section reconstruction

For the literal core Q, let B=[Z₂(Q),Q]. This nonzero central subgroup is
characteristic in Q, lies in Q′ and Φ(Q), and is normalized by every
normalizer of Q. A whole natural center forces B=Z(Q), by natural
irreducibility. In a whole doubled center, either B=Z(Q), or B and Z(Q)/B
are natural at the same full SL₃ marking. In the latter case the central
flag is canonical, with no choice of an invariant summand.

The actual C_Q(Z₂(Q)) contains Φ(Q) and is proper in Q. Its quotient is
elementary and has the faithful commutator coordinates constructed in
SecondCenterCommutator. This centralizer is kept distinct from the source
fourth-row group C_Q(Φ(Q)). Neither class two nor upper-module recognition
is inferred.

Under the genuine MS-pair hypotheses, MS3 proves that this nontrivial
KR-normal B is not characteristic in R. Characteristicity in Q therefore
cannot supply characteristicity in R for a quotient-induction argument.
NonblockSecondCenterImage applies all these results to the original
field-four configuration and discharges its whole-center model premise.
Source: Aschbacher–Smith C.1.31 and C.1.34, printed pp.135–137;
MS93's upper-section reconstruction in Section 4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterImage
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open SecondCenterSections
variable {G : Type*} [Group G] [Finite G] {K Q : Subgroup G}
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "O" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn Q
local notation "B" => (⁅secondCenterIn Q,Q⁆ : Subgroup G)
local notation "T₂" => Subgroup.upperCentralSeries Q 2

omit [Finite G] in
/-- The ambient commutator is exactly the intrinsic characteristic image. -/
theorem image_eq_map : B = (SecondCenterFrattini.upperImage (P := Q)).map Q.subtype := by
  rw [SecondCenterFrattini.upperImage,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  rfl

/-- This central layer is canonical and nontrivial; it requires no choice
of a natural summand. Its normalization comes from characteristicity in Q. -/
theorem image_structure (hQ : IsPGroup 2 Q) (hna : ¬IsMulCommutative Q) :
    B ≠ ⊥ ∧ B ≤ Z ∧ B ≤ ⁅Q,Q⁆ ∧ B ≤ frattiniIn Q ∧
      normalizer (Q : Set G) ≤ normalizer (B : Set G) := by
  rw [image_eq_map]
  have hd := SecondCenterFrattini.upperImage_le_derived_frattini hQ
  refine ⟨?_,map_mono SecondCenterFrattini.upperImage_le_center,?_,map_mono hd.2,?_⟩
  · intro he
    exact SecondCenterFrattini.upperImage_ne_bot hQ hna
      ((map_eq_bot_iff_of_injective _ Q.subtype_injective).mp he)
  · rw [←map_subtype_commutator]
    exact map_mono hd.1
  · exact normalizer_le_normalizer_characteristic_image Q _

omit [Finite G] in
/-- The effective second variable has the literal ambient centralizer. -/
theorem centralizer_image :
    (centralizer (T₂ : Set Q)).map Q.subtype = Q ⊓ centralizer (secondCenterIn Q : Set G) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨y.property,?_⟩
    rintro z ⟨z,hz,rfl⟩
    exact congrArg Q.subtype (hy z hz)
  · intro hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    intro y hy
    exact Subtype.ext (hx.2 y (mem_map_of_mem Q.subtype hy))

/-- The proper effective upper quotient lies beyond the Frattini subgroup
and is normalized by every normalizer of the original core. -/
theorem effective_section_structure (hQ : IsPGroup 2 Q) (hna : ¬IsMulCommutative Q)
    [IsElementaryAbelian 2 (center Q)] :
    frattiniIn Q ≤ Q ⊓ centralizer (secondCenterIn Q : Set G) ∧
      Q ⊓ centralizer (secondCenterIn Q : Set G) < Q ∧
      normalizer (Q : Set G) ≤ normalizer ((Q ⊓ centralizer (secondCenterIn Q : Set G) : Subgroup G) : Set G) ∧
      IsElementaryAbelian 2 (Q ⧸ centralizer (T₂ : Set Q)) := by
  rw [←centralizer_image]
  refine ⟨map_mono (le_centralizer_iff.mp SecondCenterFrattini.second_le_frattini_centralizer),
    lt_of_le_of_ne (map_subtype_le _) ?_,?_,
    SecondCenterFrattini.right_quotient_elementary⟩
  · intro he
    have hc : centralizer (T₂ : Set Q)=⊤ := by
      apply map_injective Q.subtype_injective
      simpa only [←MonoidHom.range_eq_map,range_subtype] using he
    apply SecondCenterFrattini.upperImage_ne_bot hQ hna
    rw [SecondCenterFrattini.upperImage,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (by rw [hc])
  · exact normalizer_le_normalizer_characteristic_image Q (centralizer (T₂ : Set Q))

variable {F : Type} [Field F] [CharP F 2]

/-- A whole natural center is the canonical second-center commutator image. -/
theorem natural_image_eq (hQ : IsPGroup 2 Q) (hna : ¬IsMulCommutative Q)
    (hKQ : K ≤ normalizer (Q : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3)) : B=Z := by
  let := (SecondCenterSquares.exists_marked_squares (linearThreeActor e) _ hm).1
  have hw : omega₁ (center Q) (p := 2)=⊤ := by
    apply top_unique
    intro z _
    apply Subgroup.subset_closure
    change z^(2^1)=1
    simpa only [pow_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center Q)) z
  have hOZ : O=Z := by
    simp only [Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn,
      hw,←MonoidHom.range_eq_map,range_subtype]
    rfl
  obtain ⟨hb,hbz,_,_,hbn⟩ := image_structure hQ hna
  apply le_antisymm hbz
  rw [←hOZ]
  exact NaturalOmegaCore.omega_le_normal hQ e (hOZ.symm ▸ hm) B
    (hbz.trans (map_subtype_le _)) (Q.le_normalizer.trans hbn) (hKQ.trans hbn) hb

omit [CharP F 2] in
/-- In the doubled-center branch the canonical image is the whole center,
or it supplies a natural flag at the same marking. -/
theorem doubled_image_sections (hQ : IsPGroup 2 Q) (hna : ¬IsMulCommutative Q)
    (hKQ : K ≤ normalizer (Q : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    B=Z ∨ (HasSectionModel K B ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K Z B (linearThreeActor e) (specialLinearNatural 3)) := by
  by_cases he : B=Z
  · exact Or.inl he
  obtain ⟨hb,hbz,_,_,hbn⟩ := image_structure hQ hna
  exact Or.inr (CentralDerivedSections.proper_invariant_sections e hm hbz (hKQ.trans hbn) hb he)

variable {R : Subgroup G} {n : ℕ} [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1<n)
include h hn

omit [CharP F 2] in
/-- MS3 forbids this nonzero KR-normal layer from being characteristic in R.
Thus characteristicity in Q cannot justify quotient induction on MS-pairs. -/
theorem ms_image_not_characteristic_radical (hna : ¬IsMulCommutative (msQ K R)) :
    ¬ ((⁅secondCenterIn (msQ K R),msQ K R⁆ : Subgroup G).subgroupOf R).Characteristic := by
  let Q := msQ K R
  let X : Subgroup G := ⁅secondCenterIn Q,Q⁆
  have hQ : IsPGroup 2 Q := (isPGroup_pCoreIn 2 (K ⊔ R)).to_le msQ_le_joinCore
  obtain ⟨hb,hbz,_,_,hbn⟩ := image_structure hQ hna
  have hXQ : X≤Q := hbz.trans (map_subtype_le _)
  have hNR : (K ⊔ R).pCoreIn 2 ≤ R := by
    rintro _ ⟨x,hx,rfl⟩
    exact (join_oddIndex h hn).twoCore_le hx
  have hXR : X≤R := hXQ.trans (msQ_le_joinCore.trans hNR)
  have hXN : K ⊔ R ≤ normalizer (X : Set G) :=
    (CentralSections.join_normalizes_core h hn).trans hbn
  intro hc
  have he := h.characteristic (X.subgroupOf R) hc (by
    rw [map_subgroupOf_eq_of_le hXR]
    exact (normal_subgroupOf_iff_le_normalizer (hXR.trans le_sup_right)).mpr hXN)
  apply hb
  have hh := congrArg (map R.subtype) he
  simpa only [map_subgroupOf_eq_of_le hXR,Subgroup.map_bot] using hh

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterImage
