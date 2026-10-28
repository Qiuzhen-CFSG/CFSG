module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.CubicLift.Obstruction
public import Theory.GroupTheory.CComponent.CentralizerMovement
public import Theory.SpecificGroups.BinaryComponentResidual.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.BinaryModels

public import Theory.SpecificGroups.Triality.CComponentResidual
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.HigmanSims
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.QuotientModels

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Source

/-!
# Central residual exclusion for the original extraspecial marker

The full preimage X₀ of the extraspecial residual center has a prime-to-three
residual A=O^{3′}(X₀) mapping onto that central cubic. Its action normalizes
and has no nonzero fixed point on the marked four-group Z₁. Thus A moves Z₁
and is its own embedded prime-to-three residual.

The ambient bound m₃(N_G(Z₁))≤2 makes this movement incompatible with a
C-component centralizing Z₁ whose quotient has cubic rank two and a two-group
outer automorphism group. Triality uses its separate cubic-residual theorem.
The actual ordinary quotient models are all excluded, including HS and Ru;
Rudvalis simplicity is inherited from the ordinary component. Among the
constrained alternatives, the source rank-one theorem leaves only the
natural L₃(2) block, which remains an obligation of the final assembly.

This is a replacement exclusion argument using O^{3′}(X₀). It neither changes
nor constructs a cubic in O²(⟨R^{X₀}⟩), which the earlier obstruction proves
trivial under 15.1.14. The original marking and selected component remain
fixed throughout.

Source: Aschbacher--Smith 15.1.16(c), 15.1.21--24 and A.3.18,
printed pp.1092,1097--1101,51--53.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The full residual-center preimage has the literal central cubic as image. -/
theorem centralPreimage_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) :
    ((centralPreimage M V hn).subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (center (pResidual 2 (internalActionImage M V hn))).map
        (pResidual 2 (internalActionImage M V hn)).subtype := by
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let P := pResidual 2 (internalActionImage M V hn)
  let Z := (center P).map P.subtype
  change (((Z.comap f).map M.subtype).comap M.subtype).map f = Z
  rw [comap_map_eq_self_of_injective M.subtype_injective]
  exact map_comap_eq_self_of_surjective (actionHom M V hn).rangeRestrict_surjective _

/-- The prime-to-three residual still maps onto the original center. -/
theorem centralPreimage_primeToResidual_image
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    let A := (primeToResidual 3 (centralPreimage M V hn)).map
      (centralPreimage M V hn).subtype
    (A.subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (center (pResidual 2 (internalActionImage M V hn))).map
        (pResidual 2 (internalActionImage M V hn)).subtype := by
  intro A
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let P := pResidual 2 (internalActionImage M V hn)
  let Z := (center P).map P.subtype
  let X := Z.comap f
  obtain ⟨_,_,_,hP,_,_,_,_⟩ := hex
  let := hP
  have hcard : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  have hz : primeToResidual 3 Z = ⊤ := by
    apply top_unique
    intro z _
    exact mem_primeToResidual_of_pow (n := 1) (by
      simpa only [pow_one,hcard] using (pow_card_eq_one' (x := z)))
  have he : (X.map f) = Z :=
    map_comap_eq_self_of_surjective (actionHom M V hn).rangeRestrict_surjective _
  have hA : A = ((primeToResidual 3 X).map X.subtype).map M.subtype := by
    exact (map_embedded_primeToResidual_of_hom 3 X M.subtype).symm
  change (A.comap M.subtype).map f = Z
  rw [hA,comap_map_eq_self_of_injective M.subtype_injective,map_embedded_primeToResidual_of_hom,he,hz,
    ←MonoidHom.range_eq_map,range_subtype]

/-- Any subgroup with the central cubic image normalizes the marked plane
and has no nontrivial fixed element on it. No order of the lift is assumed. -/
theorem ImageMarking.central_image_geometry
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (c : ImageMarking T M V hn) (X : Subgroup M)
    (himage : X.map (actionHom M V hn).rangeRestrict =
      (center (pResidual 2 (internalActionImage M V hn))).map
        (pResidual 2 (internalActionImage M V hn)).subtype) :
    X.map M.subtype ≤ normalizer (fixedSubgroup M V hn c.X : Set G) ∧
      fixedSubgroup M V hn c.X ⊓ centralizer (X.map M.subtype : Set G) = ⊥ := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  let B := c.X.map P.subtype
  let W := fixedSpace ρ B
  let Z := fixedSubgroup M V hn c.X
  let Y := X.map M.subtype
  change X.map f = ZP at himage
  obtain ⟨_,_,_,hP,hcard,_,hdim,_⟩ := hex
  let := hP
  let σ := ρ.comp P.subtype
  have hfaith : Function.Injective σ :=
    (imageRepresentation_injective M V hn).comp P.subtype_injective
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    hfaith hcard hdim
  have hzero : fixedSpace ρ ZP = ⊥ := by
    rw [←fixedSpace_comp_map]
    change invariants (σ.comp (center P).subtype) = ⊥
    by_contra hh
    have hh' := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hh
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr hfaith] using hh')
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  have hcom : ⁅ZP,B⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro z ⟨z,hz,rfl⟩ b ⟨b,hb,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz b)
  have hnormW : ZP ≤ subspaceStabilizer ρ W :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ ZP B hcom
  constructor
  · apply le_normalizer_iff.mpr
    rintro y ⟨x,hx,rfl⟩ z ⟨v,hv,rfl⟩
    refine ⟨(actionHom M V hn x) v,?_,rfl⟩
    have hfx : f x ∈ ZP := himage ▸ mem_map_of_mem f hx
    exact (hnormW hfx (Additive.ofMul v)).mpr hv
  · apply bot_unique
    intro z hz
    obtain ⟨v,hv,rfl⟩ := hz.1
    have hvfix : Additive.ofMul v ∈ fixedSpace ρ ZP := by
      rw [←himage]
      rintro ⟨a,⟨x,hx,rfl⟩⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x : G) * (v : G) * (x : G)⁻¹ = v
      have hc : (x : G) * (v : G) = (v : G) * x :=
        hz.2 x (mem_map_of_mem M.subtype hx)
      rw [hc,mul_inv_cancel_right]
    rw [hzero,Submodule.mem_bot] at hvfix
    exact congrArg (fun w : Additive V => (w.toMul : G)) hvfix

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker

namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The prime-to-three residual of the full central preimage normalizes and
moves the original marked four-group, and is itself generated by three-elements. -/
theorem ImageMarking.central_primeToResidual_movement
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (c : ImageMarking T M V hn) :
    let A := (primeToResidual 3 (centralPreimage M V hn)).map
      (centralPreimage M V hn).subtype
    A ≤ M ∧ A ≤ normalizer (fixedSubgroup M V hn c.X : Set G) ∧
      (primeToResidual 3 A).map A.subtype = A ∧
      fixedSubgroup M V hn c.X ⊓ centralizer (A : Set G) = ⊥ ∧
      ⁅fixedSubgroup M V hn c.X,A⁆ ≠ ⊥ := by
  intro A
  have hAM : A ≤ M := (map_subtype_le _).trans (map_subtype_le _)
  have hg := c.central_image_geometry T hn hex (A.subgroupOf M)
    (centralPreimage_primeToResidual_image T hn hex)
  rw [map_subgroupOf_eq_of_le hAM] at hg
  have hid : (primeToResidual 3 A).map A.subtype = A := by
    rw [show A = (primeToResidual 3 (centralPreimage M V hn)).map
      (centralPreimage M V hn).subtype from rfl,
      ←map_embedded_primeToResidual_of_hom 3
        (primeToResidual 3 (centralPreimage M V hn)) (centralPreimage M V hn).subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 (centralPreimage M V hn)) le_rfl]
  refine ⟨hAM,hg.1,hid,hg.2,?_⟩
  intro hc
  have hZbot : fixedSubgroup M V hn c.X = ⊥ := by
    rw [←hg.2,inf_eq_left.mpr (commutator_eq_bot_iff_le_centralizer.mp hc)]
  have hplanes := source_image_planes T hn hex c.X c.card_X c.noncentral
  have hcard : Nat.card (fixedSubgroup M V hn c.X) = 4 := by
    rw [fixedSubgroup,card_map_of_injective V.subtype_injective,binarySubgroup_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hplanes.1]
    norm_num
  rw [hZbot,card_bot] at hcard
  omega
end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original extraspecial marker excludes every centerless cubic-rank-two
component quotient with two-group outer automorphisms. The moving actor is
O^{3'}(X₀), not the obstructed residual O²(⟨R^{X₀}⟩). -/
theorem PreExclusionSource.no_extraspecial_component_facts
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X) :
    ¬ Facts (d.L ⧸ pCore 2 d.L) := by
  let := h.elementary
  let := s.quasisimple
  intro hf
  obtain ⟨_,hn,hid,_,hm⟩ := c.central_primeToResidual_movement T h.normalized hex
  rw [←hZ] at hn hm
  have htwo : IsPGroup 2 d.Z1 :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)
  have hrN : primeRank 3 (normalizer (d.Z1 : Set G)) ≤ 2 :=
    (hG.twoLocal_sqtk ⟨d.Z1,d.Z1_ne_bot,htwo,rfl⟩).stronglyQuasithin
      3 Nat.prime_three (by decide)
  exact d.L_isCComponent_in_G1.not_centralizes_of_cubic_movement
    le_rfl hf.1 hf.2.1 hf.2.2 hrN hn hid hm d.L_component.1

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor ChapterC
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Apply the residual obstruction to the actual known quotient models and
constrained alternatives. The earlier catalogue must still supply exhaustiveness. -/
theorem PreExclusionSource.extraspecial_model_exclusions
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X) :
    ¬ SmallOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
      ¬ SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
      (d.ConstrainedAlternatives → d.ConstrainedRankOneAlternative ∨ d.ConstrainedL3Alternative) := by
  have hn := s.no_extraspecial_component_facts hG h hex c hZ
  refine ⟨fun hm => hn (facts_of_small_model hm),
    fun hm => hn (facts_of_small_binary_model hm),?_⟩
  intro ha
  cases ha with
  | rankOne a => exact Or.inl a
  | linearThree a => exact Or.inr a
  | alternatingSeven a =>
    obtain ⟨e⟩ := a.block.2.2.quotient_iso
    exact False.elim (hn (Facts.of_equiv e alternatingSeven))
  | alternatingSix hb _ =>
    obtain ⟨e⟩ := hb.2.2.quotient_iso
    exact False.elim (hn (Facts.of_equiv e alternatingSix))
  | g2 hb _ =>
    obtain ⟨e⟩ := hb.quotient_iso
    exact False.elim (hn (Facts.of_equiv e g2))
  | linear n hdegree e _ _ _ =>
    exact False.elim (hn (Facts.of_equiv e (linear hdegree)))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Triality has an outer cubic, but the ambient rank bound still forces its
component to contain every cubic residual normalizing the marked plane. -/
theorem PreExclusionSource.no_extraspecial_triality
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X)
    (n : ℕ) (hn : 0 < n) :
    ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier n hn) := by
  let := h.elementary
  let := s.quasisimple
  rintro ⟨e⟩
  obtain ⟨_,hAn,hid,_,hm⟩ := c.central_primeToResidual_movement T h.normalized hex
  rw [←hZ] at hAn hm
  have htwo : IsPGroup 2 d.Z1 :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)
  have hrN : primeRank 3 (normalizer (d.Z1 : Set G)) ≤ 2 :=
    (hG.twoLocal_sqtk ⟨d.Z1,d.Z1_ne_bot,htwo,rfl⟩).stronglyQuasithin
      3 Nat.prime_three (by decide)
  exact Triality.Standard.cComponent_not_centralizes_of_cubic_movement
    d.L_isCComponent_in_G1 le_rfl n hn e hrN hAn hid hm d.L_component.1

/-- The earlier ordinary quotient list is already incompatible with the
extraspecial marker, including HS and Ru before their catalogue refinements.
Rudvalis simplicity is inherited from the original ordinary component. -/
theorem PreExclusionSource.no_extraspecial_ordinary_postRankOne
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  have hn := s.no_extraspecial_component_facts hG h hex c hZ
  intro hm
  unfold OrdinaryPostRankOneModel at hm
  rcases hm with hm | hm | hm | hm | hm | hm
  · exact hn (facts_of_small_model hm)
  · exact hn (facts_of_small_binary_model hm)
  · obtain ⟨e⟩ := hm
    exact hn (Facts.of_equiv e
      ⟨Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot,
        Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank,
        Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
          Sporadic.LeechRelated.HS.pointStabilizer_map
          Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow⟩)
  · obtain ⟨e⟩ := hm
    let : Finite Held.He := Finite.of_equiv _ e.toEquiv
    exact hn (Facts.of_equiv e
      ⟨Held.LocalPairs.center_eq_bot,Held.three_rank_ge_two,Held.outer_isPGroup_two⟩)
  · obtain ⟨e⟩ := hm
    let := hL.2
    let a : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
    let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv a
    let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
    let b : (d.L ⧸ center d.L) ≃* Rudvalis.Model :=
      (QuotientGroup.quotientMulEquivOfEq (d.ordinary_center hL s.odd_core).1).trans e
    let : IsSimpleGroup Rudvalis.Model := b.symm.isSimpleGroup
    exact hn (Facts.of_equiv e
      ⟨Rudvalis.LowCentralizers.model_center_eq_bot,Rudvalis.three_rank_ge_two,
        Rudvalis.outer_isPGroup_two⟩)
  · exact s.no_extraspecial_triality hG h hex c hZ 1 Nat.zero_lt_one hm

/-- All four ordinary conclusions of 15.1.22 are excluded on the same
extraspecial component, with the literal center and two-core denominators. -/
theorem PreExclusionSource.no_extraspecial_ordinary22
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : ¬ d.Ordinary22Alternatives := by
  intro ha
  exact s.no_extraspecial_ordinary_postRankOne hG h hex c hZ hL
    (ha.postRankOneModel (d.ordinary_center hL s.odd_core).1)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData



namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The source rank-one theorem and the central residual exclude every
constrained alternative except the natural binary three-dimensional block.
That remaining block is retained as a genuine obligation of 15.1.24. -/
theorem PreExclusionSource.extraspecial_constrained_l3
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X)
    (ha : d.ConstrainedAlternatives) : d.ConstrainedL3Alternative := by
  exact ((s.extraspecial_model_exclusions hG h hex c hZ).2.2 ha).resolve_left
    (s.no_constrained_rankOne (h := h) (Or.inl rfl) hG hM hJ)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
