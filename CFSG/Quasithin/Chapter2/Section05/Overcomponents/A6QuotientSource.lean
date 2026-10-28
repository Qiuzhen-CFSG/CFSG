module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.QuotientFixedSource
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.OddBender
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Source
public import Theory.SpecificGroups.Alternating.SmallFixedComponents
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The full quotient census for an original fixed A₆ component

An involution with a fixed A₆ component screens the complete Theorem C
catalogue. The odd, Bender, exceptional rank-two and non-HS sporadic rows
are excluded by intrinsic fixed-group calculations. The surviving quotient
models are A₈, PSL₅(2), Sp₄(4) with its actual field involution, and HS with
its marked inner product-class involution. These genuine surviving cases
are retained; the ambient source argument must handle them.

The final application descends the original component and actor through the
literal containing central quotient. For an actual component of C_G(i),
SQTK inheritance and the proved earlier Theorems A and C supply its complete
quotient catalogue. No Chapter E ambient exclusion is used.

Source: Aschbacher–Smith 2.5.19, pp.560–563, and the intrinsic involution
inspection of Theorem C in E.6.23, p.254, combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ChapterA.Section02 ComponentRefinement ComponentSelection
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open Theory.SpecificGroups.SymplecticFour
open ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen

/-- Surviving actual quotient models, retaining the field and HS actor marks. -/
def A6FixedQuotientModels (D : Type*) [Group D] (a : MulAut D) : Prop :=
  Nonempty (D ≃* alternatingGroup (Fin 8)) ∨
  ClassicalGroup.IsPSL D 5 2 ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    Nat.card F = 4 ∧ ∃ e : D ≃* Sp F,
      MulAut.congr e a = DiagramAutomorphisms.FieldFixedResidual.representative 1) ∨
  (∃ e : D ≃* _root_.Sporadic.LeechRelated.HS.Carrier,
    MulAut.congr e a = MulAut.conj HSInner.ClassCoverage.t)

private theorem alternating_quotient_eight {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : n ≤ 8) (e : D ≃* alternatingGroup (Fin n))
    (a : MulAut D) (ha : orderOf a = 2) (S : Subgroup D)
    (hS : IsComponentIn S a.fixedSubgroup) (eS : S ≃* alternatingGroup (Fin 6)) :
    Nonempty (D ≃* alternatingGroup (Fin 8)) := by
  have hcard : Nat.card S = 360 :=
    (Nat.card_congr eS.toEquiv).trans alternatingGroup.SixSubgroupObstructions.card_six
  have hsmall : ¬ n ≤ 5 := by
    intro hs
    have hd := S.card_subgroup_dvd_card
    rw [hcard, Nat.card_congr e.toEquiv] at hd
    interval_cases n
    · rw [Nat.card_unique] at hd; norm_num at hd
    · rw [Nat.card_unique] at hd; norm_num at hd
    all_goals rw [nat_card_alternatingGroup] at hd; norm_num at hd
  have h6 : n ≠ 6 := by
    rintro rfl
    exact alternatingGroup.SmallFixedComponents.six_model_no_component e a ha S hS
  have h7 : n ≠ 7 := by
    rintro rfl
    obtain ⟨f⟩ := alternatingGroup.SmallFixedComponents.seven_component_equiv e a ha S hS
    have hc := Nat.card_congr f.toEquiv
    rw [hcard, nat_card_alternatingGroup] at hc
    norm_num at hc
  have he : n = 8 := by omega
  exact ⟨he ▸ e⟩

private theorem hs_product_class_mark {D : Type*} [Group D] [Finite D]
    [IsSimpleGroup D] [Group.IsPerfect D]
    (e : D ≃* _root_.Sporadic.LeechRelated.HS.Carrier)
    (a : MulAut D) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : B ≃* alternatingGroup (Fin 6)) :
    ∃ f : D ≃* _root_.Sporadic.LeechRelated.HS.Carrier,
      MulAut.congr f a = MulAut.conj HSInner.ClassCoverage.t := by
  let : IsSimpleGroup _root_.Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect _root_.Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  let j := MulAut.fixedSubgroupCongr e a
  let C := B.map j.toMonoidHom
  have hC : IsComponent b.fixedSubgroup C := hB.map_equiv j
  let fC : C ≃* alternatingGroup (Fin 6) := (j.subgroupMap B).symm.trans eB
  have hi : ∃ x, b = MulAut.conj x := by
    by_contra ho
    obtain ⟨f⟩ := HSOuter.outer_component_equiv b hb ho C hC
    have hc := Nat.card_congr (fC.symm.trans f).toEquiv
    change Nat.card (alternatingGroup (Fin 6)) = Nat.card (alternatingGroup (Fin 8)) at hc
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num at hc
  obtain ⟨x, hx⟩ := hi
  have ho : orderOf x = 2 :=
    (orderOf_injective MulAut.conj HSInner.conj_injective x).symm.trans (hx ▸ hb)
  rcases HSInner.ClassCoverage.involution_classes x ho with hc | ht
  · obtain ⟨f⟩ := HSInner.fixed_equiv_centralizer_of_isConj hc
    have he : b.fixedSubgroup ≃*
        centralizer ({_root_.Sporadic.LeechRelated.HS.EvenLocalCandidates.e0} : Set _) := by
      rw [hx]
      exact f
    exact ((HSInner.selfCentralizing_transport he.symm
      HSInner.centralizer_selfCentralizing).not_isComponent C hC).elim
  · obtain ⟨k, hk⟩ := isConj_iff.mp ht
    have hm : MulAut.congr (MulAut.conj k⁻¹) b = MulAut.conj HSInner.ClassCoverage.t := by
      rw [hx, MulAut.congr_conj]
      congr 1
      change k⁻¹ * x * k = HSInner.ClassCoverage.t
      rw [← hk]
      group
    refine ⟨e.trans (MulAut.conj k⁻¹), ?_⟩
    convert hm using 1
    ext y
    rfl

/-- The complete intrinsic fixed-A₆ census on the full earlier Theorem C list.
Every excluded row uses the actual involution and its specified component. -/
theorem a6_fixed_quotient_models {D : Type*} [Group D] [Finite D]
    [IsSimpleGroup D] [Group.IsPerfect D]
    (hm : IsTheoremCModel D) (a : MulAut D) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : B ≃* alternatingGroup (Fin 6)) : A6FixedQuotientModels D a := by
  let S := B.map a.fixedSubgroup.subtype
  have hS : IsComponentIn S a.fixedSubgroup := by
    refine ⟨map_subtype_le _, ?_⟩
    have he : S.subgroupOf a.fixedSubgroup = B :=
      comap_map_eq_self_of_injective a.fixedSubgroup.subtype_injective _
    rw [he]
    exact hB
  let eS : S ≃* alternatingGroup (Fin 6) :=
    (B.equivMapOfInjective a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective).symm.trans eB
  have heS : Nonempty (S ≃* alternatingGroup (Fin 6)) := ⟨eS⟩
  have hsix : 360 ∣ Nat.card D := by
    have hd := S.card_subgroup_dvd_card
    rwa [Nat.card_congr eS.toEquiv, alternatingGroup.SixSubgroupObstructions.card_six] at hd
  cases hm with
  | alternating n hn iso =>
    exact Or.inl (alternating_quotient_eight hn iso.some a ha S hS eS)
  | odd hm => exact (oddFixedComponentExclusion D hm a ha S hS heS).elim
  | bender hm => exact (benderFixedComponentExclusion D hm a ha S hS heS).elim
  | linear_binary n hn hm =>
    rcases hn with rfl | rfl
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      have hc : Fintype.card F = Fintype.card (ZMod 2) := by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF
      exact Or.inl ⟨e.trans ((Atlas.fieldEquivPSL 4
        (FiniteField.ringEquivOfCardEq hc)).trans
          Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)⟩
    · exact Or.inr (Or.inl hm)
  | rank_two f hm =>
    cases hm with
    | linear hf hm =>
      exact (RankTwo.Classical.linearInspection D f hf hm a ha S hS heS).elim
    | symplectic hf hm =>
      exact Or.inr (Or.inr (Or.inl
        (RankTwo.Classical.symplecticInspection D f hf hm a ha S hS heS)))
    | g2 hf hm =>
      exact (RankTwo.exceptionalInspection_source D (Or.inl ⟨f, hf, hm⟩) a ha S hS heS).elim
    | triality hf hm =>
      exact (RankTwo.exceptionalInspection_source D (Or.inr (Or.inl ⟨f, hf, hm⟩)) a ha S hS heS).elim
    | ree_f4 m hm hf iso =>
      exact (RankTwo.exceptionalInspection_source D
        (Or.inr (Or.inr (Or.inl ⟨m, hm, iso⟩))) a ha S hS heS).elim
    | tits hf iso =>
      exact (RankTwo.exceptionalInspection_source D
        (Or.inr (Or.inr (Or.inr iso))) a ha S hS heS).elim
    | symplectic_derived hf iso =>
      exact (alternatingGroup.SmallFixedComponents.six_model_no_component
        (iso.some.trans Binary.projectiveDerivedEquivAlternatingSix) a ha S hS).elim
    | g2_derived hf iso =>
      have hd : Nat.card D ∣ Nat.card (Atlas.G2.Model (ZMod 2)) := by
        rw [Nat.card_congr iso.some.toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      have hh := hsix.trans hd
      rw [Atlas.G2.card_Model] at hh
      norm_num at hh
  | sporadic hm =>
    rcases hm with ⟨name, hname, ⟨e⟩⟩ | ⟨e⟩
    · let : IsSimpleGroup name.Carrier := e.symm.isSimpleGroup
      let : Group.IsPerfect name.Carrier := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      have exclude (h : Sporadic.FixedSixExclusion name.Carrier) : False :=
        h.of_equiv e a ha B hB ⟨eB⟩
      cases name with
      | m11 => exact (exclude Sporadic.m11).elim
      | m12 => exact (exclude Sporadic.m12).elim
      | m22 => exact (exclude Sporadic.m22).elim
      | m23 => exact (exclude Sporadic.m23).elim
      | m24 => exact (exclude Sporadic.m24).elim
      | j2 => exact (exclude Sporadic.janko_two).elim
      | j3 => exact (hname rfl).elim
      | j4 => exact (exclude (@Sporadic.janko_four e.symm.isSimpleGroup
          (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective))).elim
      | he => exact (exclude Sporadic.held).elim
      | ru => exact (exclude (@Sporadic.rudvalis e.symm.isSimpleGroup
          (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective))).elim
      | hs => exact Or.inr (Or.inr (Or.inr (hs_product_class_mark e a ha B hB eB)))
    · exact ((Sporadic.janko_one.of_equiv e.some) a ha B hB ⟨eB⟩).elim

/-- Source application to the literal containing central quotient. The earlier
catalogue premise belongs to the containing-component assembly; the original
component, actor, and quotient map are preserved by the proved descent. -/
theorem source_a6_fixed_component_quotient {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) (eK : K ≃* alternatingGroup (Fin 6))
    (hm : IsTheoremCModel (E ⧸ center E)) :
    A6FixedQuotientModels (E ⧸ center E) (quotientAut (center E) a) := by
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : Group.IsPerfect (E ⧸ center E) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center E))
  obtain ⟨hc, haq, hD, ⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  exact a6_fixed_quotient_models hm _ haq _ hD (eD.symm.trans eK)

/-- The original invariant overcomponent supplies its own complete quotient
catalogue. Theorems A and C apply to the actual SQTK subgroup of C_G(i),
so no model-classification premise remains in this source row family. -/
theorem source_a6_overcomponent_quotient {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (i : G) (hi : orderOf i = 2)
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) (eK : K ≃* alternatingGroup (Fin 6)) :
    A6FixedQuotientModels (X ⧸ center X) (quotientAut (center X) a) := by
  let : IsQuasisimple X := hX.2
  have hm : IsTheoremCModel (X ⧸ center X) :=
    Chapter1.QuasisimpleInvolutions.quotient_model
      ((hG.involution_centralizer_sqtk hi).subgroup X)
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  exact source_a6_fixed_component_quotient c hG hempty hgen hb a ha B hB eKB eK hm

end CFSG.Quasithin.Chapter2.Section05.Overcomponents
