module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.LocalCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.SectionCentralizer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The nonquasisimple component and the SL₃(4) exclusion

The elementary abelian group U lies in G_u. The central involution u lies
in O₂(G_u), giving the Sylow-centralizer hypothesis of 1.2.11. Once the
original point z is in [U,K], two-perfectness of K supplies the exact
normalizer residual in that lemma. Its characteristic-two conclusion passes
to the component L_u by relative subnormality. This supplies every hypothesis
of the full C.2.7 implication, retaining its actual star quotient and all eight
alternatives.

The commutator membership of z is an explicit intermediate premise, not a
proved consequence here. The universal 1.2.11 and C.2.7 inputs belong to
qt-1-02-component-dichotomy/qt-1-02-adequate-assembly and qt-c-02.
The actual two-core quotient also lifts section-centralizer elements: its
kernel normalizes K, so residual transport lifts normalization and exact
prime-core transport lifts the commutator bound. Cauchy's theorem then lifts
cubic divisibility to an ambient element. This proves the entire SL₃(4)
exclusion, using its center of order three. The A.3.14 comparison,
chief-factor exclusion, and Sp₄(4) section-centralizer calculation remain.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
1.2.11, printed p.508, and 14.7.68(2), printed pp.1071–1072.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Nonquasisimple

/-- The universal earlier 1.2.11 implication on the actual ambient group.
Order two makes explicit the nonidentity hypothesis required by its proof.
The residual is taken inside N_H(A), not inside N_G(A). -/
def Earlier1211 (G : Type u) [Group G] [Finite G] : Prop :=
  IsSimpleQTKE KnownSimple.IsKnownSimple G →
    ∀ (S : Sylow 2 G) (H B : Subgroup G) (z : G),
      H ∈ Chapter1.H G → Chapter1.IsSylowIn 2 ((S : Subgroup G) ⊓ H) H →
      B ∈ Chapter1.cComponentsIn H → orderOf z = 2 →
      z ∈ B → z ∈ (S : Subgroup G) ⊓ H →
      (∀ t ∈ (S : Subgroup G), t * z = z * t) →
      (∃ A : Subgroup G, A ≤ H ∧ IsElementaryAbelian 2 A ∧
        z ∈ ⁅A, (pResidual 2 (H ⊓ normalizer (A : Set G) : Subgroup G)).map
          (H ⊓ normalizer (A : Set G)).subtype⁆) →
      (S : Subgroup G) ⊓ centralizer (H.pCoreIn 2 : Set G) ≤
        (S : Subgroup G) ⊓ H →
      IsQuasisimple B ∨ H ∈ Chapter1.He G

/-- The literal hypotheses of the remaining case of 14.7.68. In particular,
normality and C-component membership are relative to G_u. -/
structure Case (d : Data T L V F W) (u : F.U) (Lu : Subgroup G) : Prop where
  member : (u : G) ∈ d.U₀
  nonidentity : (u : G) ≠ 1
  fixed : d.FixedModuloPoint u
  normalizer : normalizer (K F : Set G) = F.H
  maximal : IsMaximalTwoLocal F.H
  sylow : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u)
  le_centralizer : Lu ≤ d.fixedCentralizer u
  component : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent
  larger : K F < Lu
  normal : (Lu.subgroupOf (d.fixedCentralizer u)).Normal
  outside : ¬ Lu ≤ F.H
  nonquasisimple : ¬ IsQuasisimple Lu
  quotient : IsQuasisimple (Lu ⧸ pCore 2 Lu)

/-- The exact full special-linear model in the last source alternative.
No projective quotient or unconnected family tag is substituted. -/
def IsSLThreeFour (Q : Type*) [Group Q] : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
    Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) k)

/-- The desired output of the C.2.7/A.3.14 comparison, not an assumed
source implication. Blocks remain subnormal in the actual G_u. -/
inductive ReducedModels (H Lu : Subgroup G) : Prop
  | alternatingSeven (block : ChapterC.IsBlock (Lu.subgroupOf H))
      (model : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
  | symplecticFour (block : ChapterC.IsBlock (Lu.subgroupOf H))
      (model : ChapterC.IsSp4FourBlock Lu)
  | linearThree (model : IsSLThreeFour (Lu ⧸ pCore 2 Lu))

end Nonquasisimple

namespace Data
variable (d : Data T L V F W)

/-- Every element of the original elementary abelian U centralizes u. -/
theorem U_le_fixedCentralizer (u : F.U) : F.U ≤ d.fixedCentralizer u := by
  let := d.abelian
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : F.U) u)

/-- The source involution is in the actual two-core of its centralizer. -/
theorem fixedElement_mem_core (u : F.U) : (u : G) ∈ (d.fixedCentralizer u).pCoreIn 2 := by
  let A := zpowers (u : G)
  have hA : IsPGroup 2 A := by
    let := d.U_elementary
    exact (IsElementaryAbelian.zpowers_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (u : G) u.property)).isPGroup 2 _
  have hAG : A ≤ d.fixedCentralizer u :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hn : d.fixedCentralizer u ≤ normalizer (A : Set G) := by
    apply (show d.fixedCentralizer u ≤ centralizer (A : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    rw [show A = zpowers (u : G) from rfl, zpowers_eq_closure, centralizer_closure]
    exact le_rfl
  exact le_pCoreIn_of_normalizes hA hAG hn (mem_zpowers (u : G))

/-- This verifies hypothesis (b) of 1.2.11 without a characteristic-two
assumption: u already belongs to the core being centralized. -/
theorem fixedCentralizer_core_centralizer_le (u : F.U) :
    (T : Subgroup G) ⊓ centralizer ((d.fixedCentralizer u).pCoreIn 2 : Set G) ≤
      d.fixedSylow u := by
  intro t ht
  refine ⟨ht.1, mem_centralizer_singleton_iff.mpr ?_⟩
  exact (mem_centralizer_iff.mp ht.2 _ (d.fixedElement_mem_core u)).symm

/-- K embeds in precisely the normalizer residual used in 1.2.11(a). -/
theorem K_le_fixedNormalizer_residual (u : F.U) (hu : (u : G) ∈ d.U₀) :
    K F ≤ (pResidual 2 (d.fixedCentralizer u ⊓ normalizer (F.U : Set G) :
      Subgroup G)).map (d.fixedCentralizer u ⊓ normalizer (F.U : Set G)).subtype := by
  have hKN : K F ≤ d.fixedCentralizer u ⊓ normalizer (F.U : Set G) :=
    le_inf (d.K_le_fixedCentralizer u hu)
      ((K_le_H F).trans d.conjugationSection.normalized)
  have hm := embedded_pResidual_mono 2 hKN
  rw [(pResidual_eq_top_iff 2 _).mpr (K_twoPerfect F),
    ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- The genuine 1.2.11 specialization. Only the earlier universal source
implication and the displayed point-commutator membership remain explicit. -/
theorem fixedCentralizer_characteristicTwo
    (earlier : Nonquasisimple.Earlier1211 G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hzcomm : d.z ∈ ⁅F.U, K F⁆) : d.fixedCentralizer u ∈ Chapter1.He G := by
  have hzpoint : d.z ∈ F.Vi 1 := by rw [d.point]; exact mem_zpowers d.z
  have hzK : d.z ∈ K F :=
    le_normalizer_iff_commutator_le_right.mp
      (d.conjugationSection.section_le.trans (H_normalizes_K F)) hzcomm
  have hd := earlier d.counterexample.qtke T (d.fixedCentralizer u) Lu d.z
    (d.fixedCentralizer_core_ne_bot u h.nonidentity) h.sylow
    ⟨h.le_centralizer, h.component⟩
    (d.fixedElement_order ⟨d.z, d.U₀_le_U d.z_mem_U₀⟩ d.z_ne_one)
    (h.larger.le hzK) (d.point_le_fixedSylow u hzpoint)
    (fun t ht => mem_centralizer_singleton_iff.mp
      (d.centralizer_eq ▸ F.invariant 1 ht))
    ⟨F.U, d.U_le_fixedCentralizer u, d.U_elementary,
      commutator_mono le_rfl (d.K_le_fixedNormalizer_residual u h.member) hzcomm⟩
    (d.fixedCentralizer_core_centralizer_le u)
  exact hd.resolve_left h.nonquasisimple

/-- Characteristic two passes from G_u to its relative C-component; no
ambient normality of L_u is asserted. -/
theorem fixedComponent_fitting
    (earlier : Nonquasisimple.Earlier1211 G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hzcomm : d.z ∈ ⁅F.U, K F⁆) : generalizedFitting Lu = pCore 2 Lu := by
  have hc := d.fixedCentralizer_characteristicTwo earlier u h hzcomm
  have hne : Lu ≠ ⊥ := by
    intro he
    exact h.larger.not_ge (he ▸ bot_le)
  exact Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_3_1 hc hne h.le_centralizer
      h.component.subnormal))

/-- Construct every input of full C.2.7 using the literal R_u and H_u.
The component normality implies normalization by R_u, and escape from H
implies escape from H_u. -/
theorem fixedComponent_C27_input
    (earlier : Nonquasisimple.Earlier1211 G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hzcomm : d.z ∈ ⁅F.U, K F⁆) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G) Lu := by
  refine ⟨d.fixedCentralizer_pushingUpSetup u h.member h.nonidentity h.fixed h.maximal,
    ⟨h.le_centralizer, h.component⟩, h.quotient,
    d.fixedComponent_fitting earlier u h hzcomm,
    fun hle => h.outside (hle.trans inf_le_left), ?_⟩
  exact ((pCoreIn_le 2 _).trans inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer h.le_centralizer).mp h.normal)

/-- Apply the entire C.2.7 implication, retaining its local clauses and
all eight alternatives on the original groups and quotient maps. -/
theorem fixedComponent_C27
    (earlier : Nonquasisimple.Earlier1211 G)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Source
      KnownSimple.IsKnownSimple G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hzcomm : d.z ∈ ⁅F.U, K F⁆) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G) :=
  c27 _ _ _ _ inferInstance (d.fixedComponent_C27_input earlier u h hzcomm)

/-- Relative normality and the actual Sylow placement put O₂(L_u) inside H.
This is the normalizing-kernel hypothesis needed to lift a quotient normalizer. -/
theorem fixedComponent_core_le_H
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Lu.pCoreIn 2 ≤ F.H := by
  have hcore : Lu.pCoreIn 2 ≤ (d.fixedCentralizer u).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes h.le_centralizer
      ((normal_subgroupOf_iff_le_normalizer h.le_centralizer).mp h.normal)
  obtain ⟨S, hS⟩ := h.sylow
  exact hcore.trans ((pCoreIn_le_sylow _ S).trans
    (hS ▸ (inf_le_left.trans (F.invariant 1))))

/-- Section centralizers lift through the actual two-core quotient. The
normalizer lifts by two-perfectness, and the commutator lifts by the exact
prime-core preimage theorem on the restricted map K → K*. -/
theorem fixedComponent_sectionCentralizer_lift
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (y : Lu) (hy : QuotientGroup.mk' (pCore 2 Lu) y ∈
      ChapterA.Section04.twoSectionCentralizer
        (((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) ⊤) :
    (y : G) ∈ ChapterA.Section04.twoSectionCentralizer (K F) ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 Lu)
  let A := (K F).subgroupOf Lu
  have hp : IsPPerfect 2 A := (K_twoPerfect F).of_surjective
    (subgroupOfEquivOfLe h.larger.le).symm.toMonoidHom
    (subgroupOfEquivOfLe h.larger.le).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hn : q.ker ≤ normalizer (A : Set Lu) := by
    rw [QuotientGroup.ker_mk', ← subgroupOf_normalizer_eq h.larger.le]
    intro a ha
    exact H_normalizes_K F (d.fixedComponent_core_le_H u h (mem_map_of_mem _ ha))
  have hyA : y ∈ normalizer (A : Set Lu) := by
    rw [← comap_normalizer_map_of_pPerfect q A hp hk hn]
    exact hy.2.1
  have hyK : (y : G) ∈ normalizer (K F : Set G) := by
    rwa [← subgroupOf_normalizer_eq h.larger.le] at hyA
  refine ⟨mem_top _, hyK, ?_⟩
  intro k hkK
  let kL : Lu := ⟨k, h.larger.le hkK⟩
  have hcommA : ⁅y, kL⁆ ∈ A :=
    le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr hyA)
      (commutator_mem_commutator (mem_zpowers y) (show kL ∈ A from hkK))
  have hkA : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  have hpre := (q.subgroupMap A).comap_pCore_of_ker_isPGroup
    (q.subgroupMap_surjective A) hkA
  have himage : q ⁅y, kL⁆ ∈ (A.map q).pCoreIn 2 := by
    rw [map_commutatorElement]
    exact hy.2.2 _ (mem_map_of_mem q (show kL ∈ A from hkK))
  have hc : (⟨⁅y, kL⁆, hcommA⟩ : A) ∈ pCore 2 A := by
    rw [← hpre]
    change (q.subgroupMap A) ⟨⁅y, kL⁆, hcommA⟩ ∈ pCore 2 (A.map q)
    apply (mem_map_iff_mem (f := (A.map q).subtype)
      (x := (q.subgroupMap A) ⟨⁅y, kL⁆, hcommA⟩)
      (A.map q).subtype_injective).mp
    exact himage
  have he : (A.pCoreIn 2).map Lu.subtype = (K F).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 A Lu.subtype Lu.subtype_injective,
      map_subgroupOf_eq_of_le h.larger.le]
  exact he ▸ mem_map_of_mem Lu.subtype (mem_map_of_mem A.subtype hc)

/-- The quotient center is contained in the section centralizer. Its lifts
therefore satisfy both normalization and the original commutator bound. -/
theorem fixedComponent_center_lift_sectionCentralizer
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (y : Lu) (hy : QuotientGroup.mk' (pCore 2 Lu) y ∈
      center (Lu ⧸ pCore 2 Lu)) :
    (y : G) ∈ ChapterA.Section04.twoSectionCentralizer (K F) ⊤ := by
  apply d.fixedComponent_sectionCentralizer_lift u h y
  refine ⟨mem_top _, (Subgroup.centralizer_le_normalizer _)
    (mem_centralizer_iff.mpr (fun a _ => mem_center_iff.mp hy a)), ?_⟩
  intro k _
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hy k).symm]
  exact one_mem _

/-- Cauchy's theorem on the full preimage turns a cubic divisor in the
literal quotient section centralizer into the required ambient element. -/
theorem fixedComponent_exists_orderThree_of_sectionCentralizer_image
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hthree : 3 ∣ Nat.card (ChapterA.Section04.twoSectionCentralizer
      (((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) ⊤)) :
    ∃ y : G, y ∈ Lu ∧ orderOf y = 3 ∧
      y ∈ ChapterA.Section04.twoSectionCentralizer (K F) ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 Lu)
  let C := ChapterA.Section04.twoSectionCentralizer (((K F).subgroupOf Lu).map q) ⊤
  let P := C.comap q
  have hd : Nat.card C ∣ Nat.card P := by
    have hm := P.card_map_dvd q
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 (hthree.trans hd)
  refine ⟨((y : Lu) : G), (y : Lu).property, ?_,
    d.fixedComponent_sectionCentralizer_lift u h (y : Lu) y.property⟩
  exact (Subgroup.orderOf_coe (y : Lu)).trans ((Subgroup.orderOf_coe y).trans hy)

/-- The actual consumer of quotient section-centralizer lifting. The
Sp₄(4) model calculation must supply the contradictory cubic divisibility
on this same K-image, not an abstract unrelated A₅ subgroup. -/
theorem fixedComponent_sectionCentralizer_image_not_three
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    ¬ 3 ∣ Nat.card (ChapterA.Section04.twoSectionCentralizer
      (((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) ⊤) := by
  intro hd
  obtain ⟨y, _, hy, hc⟩ := d.fixedComponent_exists_orderThree_of_sectionCentralizer_image u h hd
  exact d.no_orderThree_sectionCentralizer h.normalizer y hy hc

/-- Cubic divisibility in the actual quotient center supplies a genuine
ambient order-three section-centralizer element by Cauchy's theorem on its
full preimage. No splitting of L_u over its two-core is assumed. -/
theorem fixedComponent_exists_orderThree_of_quotient_center
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hthree : 3 ∣ Nat.card (center (Lu ⧸ pCore 2 Lu))) :
    ∃ y : G, y ∈ Lu ∧ orderOf y = 3 ∧
      y ∈ ChapterA.Section04.twoSectionCentralizer (K F) ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 Lu)
  let Z := (center (Lu ⧸ pCore 2 Lu)).comap q
  have hd : Nat.card (center (Lu ⧸ pCore 2 Lu)) ∣ Nat.card Z := by
    have hm := Z.card_map_dvd q
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (hthree.trans hd)
  refine ⟨((y : Lu) : G), (y : Lu).property, ?_,
    d.fixedComponent_center_lift_sectionCentralizer u h (y : Lu) y.property⟩
  exact (Subgroup.orderOf_coe (y : Lu)).trans ((Subgroup.orderOf_coe y).trans hy)

/-- The SL₃(4) alternative gives the actual forbidden cubic element. Its
center has order gcd(3,4−1)=3, transported through the supplied model
isomorphism of L_u/O₂(L_u). -/
theorem fixedComponent_linearThree_false
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hm : Nonquasisimple.IsSLThreeFour (Lu ⧸ pCore 2 Lu)) : False := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hm
  have hcenter : Nat.card (center (Lu ⧸ pCore 2 Lu)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, hk]
    decide
  obtain ⟨y, _, hy, hc⟩ := d.fixedComponent_exists_orderThree_of_quotient_center u h
    (by rw [hcenter])
  exact d.no_orderThree_sectionCentralizer h.normalizer y hy hc

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
