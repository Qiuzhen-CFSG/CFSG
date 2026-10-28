module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityAction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Applying G.6.4 to the canonical equality action

The image of the layer has a nonidentity element central in the actual
quotient Sylow two-subgroup. Its displacement lies in the line Z_S/⟨z⟩;
faithfulness makes it equal to that line. The normal-closure definition of
U then proves that its conjugate displacements generate the whole space.
The original SQTK cover is the actual involution centralizer.

These facts supply every hypothesis of the proved known-simple G.6.4.
The resulting action retains the actor and vector-space isomorphisms for
GL_n(2), 2 ≤ n ≤ 5, the natural S₆ and S₇ modules, and the S₆ core.
Excluding the larger alternatives is a subsequent source obligation.

Source: Aschbacher–Smith, 6.2.13, printed p.687 (PDF p.704), first paragraph;
G.6.4, printed pp.345–346. The action and displacement arguments use the
same literal quotient constructions as the later 15.3.50 action development.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G] {T L M R : Subgroup G} {z : G}

section LinearRecognition
open Representation.BinaryOffender
variable [IsElementaryAbelian 2 (EqualityVectorQuotient T L R z)]

noncomputable def equalityVectorSubspace :
    Submodule (ZMod 2) (Additive (EqualityVectorQuotient T L R z)) :=
  AddSubgroup.toZModSubmodule 2 (equalityDistinguishedLine T L R z).toAddSubgroup

theorem equalityVectorSubspace_finrank
    (hZSH : ZS T L R ≤ centralizer ({z} : Set G))
    (hz : z ∈ ZS T L R) (horder : orderOf z = 2)
    (hcard : Nat.card (ZS T L R) = 4) :
    Module.finrank (ZMod 2) (equalityVectorSubspace (T := T) (L := L) (R := R) (z := z)) = 1 := by
  let e : equalityVectorSubspace (T := T) (L := L) (R := R) (z := z) ≃
      equalityDistinguishedLine T L R z := {
    toFun w := ⟨w.val.toMul, w.property⟩
    invFun w := ⟨Additive.ofMul w.val, w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Nat.card (equalityVectorSubspace (T := T) (L := L) (R := R) (z := z)) = 2 :=
    (Nat.card_congr e).trans (equalityDistinguishedLine_card hZSH hz horder hcard)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := equalityVectorSubspace (T := T) (L := L) (R := R) (z := z))
  rw [hc, Nat.card_zmod] at hh
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)

omit [Finite G] in
theorem equalityDisplacement_le_line
    (A : LocalAnalysis T L M R z)
    (hcomm : ⁅layer L R, sourceClosure T L R z⁆ ≤ ZS T L R)
    (a : EqualityActor z) (ha : a ∈ equalityActorImage z (layer L R)) :
    LinearMap.range (equalityRepresentation A a - LinearMap.id) ≤
      equalityVectorSubspace := by
  obtain ⟨v, hv, rfl⟩ := ha
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    ((equalityLine z).subgroupOf (equalityClosure T L R z)) w.toMul
  have hw : w = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
  rw [hw]
  change Additive.ofMul (equalityQuotientAction T L R z v (QuotientGroup.mk' _ u)) -
    Additive.ofMul (QuotientGroup.mk' _ u) ∈ equalityVectorSubspace
  have hc : ⁅(v : G), u.val.val⁆ ∈ ZS T L R :=
    hcomm (commutator_mem_commutator hv ⟨u.val, u.property, rfl⟩)
  have hcS : ⁅v, u.val⁆ ∈ equalityPlane T L R z := hc
  let c : equalityClosure T L R z := ⟨⁅v, u.val⁆, sourceEight_contains _ hcS⟩
  have he : equalityQuotientAction T L R z v (QuotientGroup.mk' _ u) *
      (QuotientGroup.mk' _ u)⁻¹ = QuotientGroup.mk' _ c := by
    rw [equalityQuotientAction_mk, ← map_inv, ← map_mul]
    congr 1
  change equalityQuotientAction T L R z v (QuotientGroup.mk' _ u) /
    (QuotientGroup.mk' _ u) ∈ equalityDistinguishedLine T L R z
  rw [div_eq_mul_inv, he]
  exact mem_map_of_mem _ hcS

theorem equalityDisplacement_eq_line
    (A : LocalAnalysis T L M R z)
    (hcomm : ⁅layer L R, sourceClosure T L R z⁆ ≤ ZS T L R)
    (hZSH : ZS T L R ≤ centralizer ({z} : Set G))
    (hz : z ∈ ZS T L R) (horder : orderOf z = 2)
    (hcard : Nat.card (ZS T L R) = 4)
    (a : EqualityActor z) (ha : a ∈ equalityActorImage z (layer L R)) (hne : a ≠ 1) :
    LinearMap.range (equalityRepresentation A a - LinearMap.id) =
      equalityVectorSubspace := by
  have hl := equalityDisplacement_le_line A hcomm a ha
  have hd := equalityVectorSubspace_finrank hZSH hz horder hcard
  apply Submodule.eq_of_le_of_finrank_eq hl
  have hm := Submodule.finrank_mono hl
  have hn : LinearMap.range (equalityRepresentation A a - LinearMap.id) ≠ ⊥ := by
    intro hh
    have he : equalityRepresentation A a = 1 :=
      sub_eq_zero.mp (LinearMap.range_eq_bot.mp hh)
    exact hne (equalityRepresentation_injective A (he.trans (map_one _).symm))
  have hp : Module.finrank (ZMod 2)
      (LinearMap.range (equalityRepresentation A a - LinearMap.id)) ≠ 0 :=
    fun hz => hn (Submodule.finrank_eq_zero.mp hz)
  omega

omit [Finite G] in
theorem equalityDisplacement_generates
    (A : LocalAnalysis T L M R z) (a : EqualityActor z)
    (he : LinearMap.range (equalityRepresentation A a - LinearMap.id) = equalityVectorSubspace) :
    conjugateDisplacementSpan (equalityRepresentation A) a ⊤ = ⊤ := by
  let ρ := equalityRepresentation A
  let W := conjugateDisplacementSpan ρ a ⊤
  let D : Subgroup (EqualityVectorQuotient T L R z) := W.toAddSubgroup.toSubgroup'
  have hg : closure {w : EqualityVectorQuotient T L R z |
      ∃ h : centralizer ({z} : Set G), ∃ s ∈ equalityDistinguishedLine T L R z,
        equalityQuotientAction T L R z h s = w} ≤ D := by
    apply (closure_le _).mpr
    rintro _ ⟨h, s, hs, rfl⟩
    have hs' : Additive.ofMul s ∈ LinearMap.range (ρ a - LinearMap.id) := by
      rw [he]
      exact hs
    obtain ⟨w, hw⟩ := hs'
    change ρ (QuotientGroup.mk' _ h) (Additive.ofMul s) ∈ W
    rw [← hw]
    exact Submodule.subset_span ⟨QuotientGroup.mk' _ h, mem_top _, w, rfl⟩
  rw [equalityDistinguishedLine_generates] at hg
  apply top_unique
  intro w _
  exact hg (mem_top w.toMul)

end LinearRecognition

section CentralMark
variable {κ : GroupClass} {TS : Sylow 2 G} {n : ℕ}

theorem LocalAnalysis.equalityActorImage_ne_bot
    (A : LocalAnalysis (TS : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ TS L M R n)
    (hnatural : Conclusion6127 (TS : Subgroup G) L M R n)
    (hz : z ∈ ZS (TS : Subgroup G) L R) :
    equalityActorImage z (layer L R) ≠ ⊥ := by
  intro hbot
  have hVQ : layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
    intro v hv
    let vH : centralizer ({z} : Set G) := ⟨v, layer_le_involution_centralizer h611 hz hv⟩
    have hm : QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) vH ∈
        equalityActorImage z (layer L R) := mem_map_of_mem _ hv
    rw [hbot, mem_bot] at hm
    exact mem_map.mpr ⟨vH, (QuotientGroup.eq_one_iff _).mp hm, rfl⟩
  have he := A.layer_core_card
  rw [inf_eq_left.mpr hVQ, hnatural.2.1.card] at he
  norm_num at he

/-- A nontrivial marked image can be chosen in the center of the actual quotient Sylow. -/
theorem LocalAnalysis.exists_equalityCentralMark
    (A : LocalAnalysis (TS : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ TS L M R n)
    (hnatural : Conclusion6127 (TS : Subgroup G) L M R n)
    (hz : z ∈ ZS (TS : Subgroup G) L R)
    (hTH : (TS : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ a : EqualityActor z, a ∈ equalityActorImage z (layer L R) ∧ a ≠ 1 ∧
      a ∈ (center ((TS.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _))).map
        (((TS.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _) :
          Sylow 2 (EqualityActor z)) : Subgroup (EqualityActor z)).subtype := by
  let Q : Sylow 2 (EqualityActor z) :=
    (TS.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _)
  let W := equalityActorImage z (layer L R)
  have hWQ : W ≤ (Q : Subgroup (EqualityActor z)) :=
    map_mono (fun _ hv => h611.layer_le_T hv)
  have hQN : (Q : Subgroup (EqualityActor z)) ≤ normalizer (W : Set (EqualityActor z)) := by
    rintro _ ⟨t, ht, rfl⟩
    apply ((layer L R).subgroupOf (centralizer ({z} : Set G))).le_normalizer_map
      (QuotientGroup.mk' _)
    apply mem_map_of_mem
    rw [← subgroupOf_normalizer_eq (layer_le_involution_centralizer h611 hz)]
    exact h611.sylow_normalizes_layer ht
  let N := W.subgroupOf (Q : Subgroup (EqualityActor z))
  let : N.Normal := normal_subgroupOf_of_le_normalizer hQN
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr
    (A.equalityActorImage_ne_bot h611 hnatural hz)
  let : Nontrivial N := (subgroupOfEquivOfLe hWQ).toEquiv.nontrivial
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  obtain ⟨x, hx, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  refine ⟨x.val.val, x.property, ?_, ⟨x.val, hc, rfl⟩⟩
  intro he
  apply hx
  apply Subtype.ext
  exact Subtype.ext he

end CentralMark

section Classification
open Representation.BinaryOffender
variable {TS : Sylow 2 G} {n : ℕ}

/-- G.6.4 applies to the actual source action. The marked transvection has
center the actual image of Z_S, and its normal closure is the whole actor. -/
theorem LocalAnalysis.equality_action_classification
    (A : LocalAnalysis (TS : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple TS L M R n)
    (hnatural : Conclusion6127 (TS : Subgroup G) L M R n)
    (hz : z ∈ ZS (TS : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (TS : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (TS : Subgroup G) L R z ⊓ layer L R =
      ZS (TS : Subgroup G) L R) :
    let := A.sourceEqualityVectorQuotient_elementary h611 hz
    let ρ := sourceEqualityRepresentation A h611 hz
    ∃ a : EqualityActor z, a ∈ equalityActorImage z (layer L R) ∧ a ≠ 1 ∧
      LinearMap.range (ρ a - LinearMap.id) = equalityVectorSubspace ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 ∧
      normalClosure ({a} : Set (EqualityActor z)) = ⊤ ∧
      ChapterG.Section06.CentralModel ρ := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  let ρ := equalityRepresentation A
  obtain ⟨a, ha, hne, hcentral⟩ := A.exists_equalityCentralMark h611 hnatural hz hTH
  have hZSH : ZS (TS : Subgroup G) L R ≤ centralizer ({z} : Set G) :=
    inf_le_left.trans (layer_le_involution_centralizer h611 hz)
  have hcard := (h611.natural_ZS_geometry hnatural).2.1
  have he := equalityDisplacement_eq_line A
    (A.layer_closure_commutator_eq_plane h611 hnatural hz hTH hbranch).le
    hZSH hz horder hcard a ha hne
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 := by
    rw [he]
    exact equalityVectorSubspace_finrank hZSH hz horder hcard
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨v, hv, rfl⟩ := ha
    let := h611.layer_elementary
    have hv2 : v ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := layer L R) (v : G) hv)
    rw [← map_pow, hv2, map_one]
  have hhyp : ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple ρ a
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := h611.simpleQTKE.involution_centralizer_sqtk horder
    quotient_surjective := QuotientGroup.mk'_surjective _
    twoCore := pCore_quotient_pCore_eq_bot 2
    faithful := equalityRepresentation_injective A
    involution := ha2
    nonidentity := hne
    displacement_rank := hr.le.trans (by decide)
    generated := equalityDisplacement_generates A a he }
  have hc := ChapterG.Section06.lemma_G_6_4 hhyp hr
  have hm := hc.2 ((TS.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _)) hcentral
  exact ⟨a, ha, hne, he, hr, hm.1, hm.2⟩

/-- The exact surviving natural binary action required by the pair lift.
This is an output specification; its producer must eliminate every larger
model in `equality_action_classification`. -/
def EqualityNaturalAction
    (A : LocalAnalysis (TS : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple TS L M R n)
    (hz : z ∈ ZS (TS : Subgroup G) L R) : Prop :=
  letI := A.sourceEqualityVectorQuotient_elementary h611 hz
  ChapterG.Section06.HasModelOn (sourceEqualityRepresentation A h611 hz) ⊤ ⊤
    (ChapterG.Section06.binaryLinearAction 2)

end Classification

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
