module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralDerivedSections
public import Theory.Representation.SL3.NaturalInvariantLines

/-!
# Normal central flags for doubled natural MS centers

A doubled natural section has exactly |F|+1 nonzero proper K-invariant
subgroups. Conjugation by a two-group normalizing K and the section permutes
this odd family, and therefore fixes one member. Both that subgroup and its
literal quotient are natural at the original full SL₃ marking.

For a nonabelian two-group Q, the intersection Z(Q) ∩ Q' is nontrivial. If
it is proper in the doubled center, it already supplies a characteristic
intersection invariant under the whole normalizer of Q. If it is the whole
center, the odd-family argument supplies an invariant natural summand inside
Q' and hence Φ(Q). Applying this to the genuine MS-pair makes the chosen flag
normal in the entire original KR, in every nonbinary degree. No characteristicity
inside R is inferred. NonblockCentralInvariantFlags applies the result to the
original nonblock configuration, with normalization by its full KS.

This removes radical invariance as an extra premise for the central flag.
It does not exclude the nonabelian doubled-center branch or recognize the
upper and Frattini sections needed for full C.1.34.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original 4.3.8–10,
pp.616–617. The projective-line argument is the natural analogue of the
odd family used in C.1.35, pp.137–139.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.SL3ParabolicNatural
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CentralInvariantFlags
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {K Z : Subgroup G}
variable {F : Type} [Field F]
local notation "W" => (Fin 3 → F)
local notation "V" => (W × W)

/-- The intrinsic family of nonzero proper K-invariant subgroups of Z. -/
def invariantSubgroups (K Z : Subgroup G) :=
  {A : Subgroup G // ⊥ < A ∧ A < Z ∧ K ≤ normalizer (A : Set G)}

private def indexedLine (b : Z ≃* Multiplicative V) (a : Option F) : Subgroup G :=
  ((naturalLine a).comap b.toMonoidHom).map Z.subtype

private theorem indexedLine_properties
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hKZ : K ≤ normalizer (Z : Set G)) (b : Z ≃* Multiplicative V)
    (hb : ∀ (k : K) (x y : Z), (y:G)=k*(x:G)*(k:G)⁻¹ →
      (b y).toAdd=(specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.1,
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.2))
    (a : Option F) :
    ⊥ < indexedLine b a ∧ indexedLine b a < Z ∧
      K ≤ normalizer (indexedLine b a : Set G) := by
  have hle : indexedLine b a ≤ Z := map_subtype_le _
  have hmem (x : Z) : (x:G) ∈ indexedLine b a ↔ b x ∈ naturalLine a :=
    mem_map_iff_mem Z.subtype_injective
  refine ⟨bot_lt_iff_ne_bot.mpr ?_,lt_of_le_of_ne hle ?_,?_⟩
  · intro he
    apply naturalLine_ne_bot a
    apply bot_unique
    intro v hv
    have hh := (hmem (b.symm v)).mpr (by rwa [b.apply_symm_apply])
    rw [he,mem_bot] at hh
    have hx : b.symm v=1 := Subtype.ext hh
    change v=1
    simpa only [b.apply_symm_apply,map_one] using congrArg b hx
  · intro he
    apply naturalLine_ne_top a
    apply top_unique
    intro v _
    have hh := (hmem (b.symm v)).mp (he.symm ▸ (b.symm v).property)
    rwa [b.apply_symm_apply] at hh
  · apply le_normalizer_iff.mpr
    intro k hk x hx
    let xx : Z := ⟨x,hle hx⟩
    let y : Z := Z.normalizerMonoidHom ⟨k,hKZ hk⟩ xx
    apply (hmem y).mpr
    have hh := naturalLine_invariant a (linearThreeActor e ⟨k,hk⟩) (b xx)
      ((hmem xx).mp hx)
    rwa [←hb ⟨k,hk⟩ xx y rfl] at hh

private theorem line_classification
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hKZ : K ≤ normalizer (Z : Set G)) (b : Z ≃* Multiplicative V)
    (hb : ∀ (k : K) (x y : Z), (y:G)=k*(x:G)*(k:G)⁻¹ →
      (b y).toAdd=(specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.1,
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.2))
    (A : invariantSubgroups K Z) : ∃ a : Option F, A.val=indexedLine b a := by
  let B := (A.val.subgroupOf Z).map b.toMonoidHom
  have hrecover : (B.comap b.toMonoidHom).map Z.subtype=A.val := by
    rw [comap_map_eq_self_of_injective b.injective,map_subgroupOf_eq_of_le A.property.2.1.le]
  have hb0 : B ≠ ⊥ := by
    intro hh
    have hh' := hrecover
    rw [hh,MonoidHom.comap_bot,b.toMonoidHom.ker_eq_bot b.injective,Subgroup.map_bot] at hh'
    exact A.property.1.ne hh'
  have hbt : B ≠ ⊤ := by
    intro hh
    have hh' := hrecover
    rw [hh,comap_top,←MonoidHom.range_eq_map,range_subtype] at hh'
    exact A.property.2.1.ne hh'.symm
  have hinv : ∀ g : SL(3,F), ∀ v ∈ B,
      Multiplicative.ofAdd (specialLinearNatural 3 g v.toAdd.1,
        specialLinearNatural 3 g v.toAdd.2) ∈ B := by
    intro g v hv
    obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
    obtain ⟨x,hx,rfl⟩ := hv
    let y : Z := Z.normalizerMonoidHom ⟨k,hKZ k.property⟩ x
    refine ⟨y,?_,?_⟩
    · exact (mem_normalizer_iff.mp (A.property.2.2 k.property) x).mp hx
    · apply Multiplicative.toAdd.injective
      have hh := hb k x y rfl
      rwa [show linearThreeActor e k=g from hk] at hh
  obtain ⟨a,ha⟩ := invariant_natural_subgroup_eq_line B hb0 hbt hinv
  exact ⟨a,hrecover.symm.trans (by rw [ha]; rfl)⟩

/-- The actual nonzero proper K-invariant subgroups of a doubled natural
section form a projective line of cardinality |F|+1. -/
theorem invariantSubgroups_card [Finite F]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    Nat.card (invariantSubgroups K Z)=Nat.card F+1 := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKZ,_,hi,b0,hb0⟩ := hm
  let := hi
  let b : Z ≃* Multiplicative V := QuotientGroup.quotientBot.symm.trans b0
  have hb (k : K) (x y : Z) (hxy : (y:G)=k*(x:G)*(k:G)⁻¹) :
      (b y).toAdd=(specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.1,
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.2) := hb0 k x y hxy
  let f : Option F → invariantSubgroups K Z := fun a =>
    ⟨indexedLine b a,indexedLine_properties e hKZ b hb a⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a c hac
      apply naturalLine_injective
      apply comap_injective (f := b.toMonoidHom) b.surjective
      exact map_injective Z.subtype_injective (congrArg Subtype.val hac)
    · intro A
      obtain ⟨a,ha⟩ := line_classification e hKZ b hb A
      exact ⟨a,Subtype.ext ha.symm⟩
  let := Fintype.ofFinite F
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_eq_fintype_card,Fintype.card_option,
    ←Nat.card_eq_fintype_card]

private def conjugateSubgroup (S : Subgroup G)
    (hSK : S ≤ normalizer (K : Set G)) (hSZ : S ≤ normalizer (Z : Set G))
    (s : S) (A : invariantSubgroups K Z) : invariantSubgroups K Z := by
  let e := MulAut.conj (s:G)
  have hZ : Z.map e.toMonoidHom=Z := mem_normalizer_iff_map_conj_eq.mp (hSZ s.property)
  have hK : K.map e.toMonoidHom=K := mem_normalizer_iff_map_conj_eq.mp (hSK s.property)
  refine ⟨A.val.map e.toMonoidHom,?_,?_,?_⟩
  · have hh := (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr A.property.1
    rwa [Subgroup.map_bot] at hh
  · have hh := (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr A.property.2.1
    rwa [hZ] at hh
  · have hh := map_mono (f := e.toMonoidHom) A.property.2.2
    rwa [hK,map_equiv_normalizer_eq] at hh

/-- A two-group normalizing K and a doubled natural section fixes an actual
natural subgroup, with natural quotient at the same full SL₃ marking. -/
theorem exists_invariant_flag [Finite F] (heven : Even (Nat.card F))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hSK : S ≤ normalizer (K : Set G)) (hSZ : S ≤ normalizer (Z : Set G)) :
    ∃ B : Subgroup G, ⊥ < B ∧ B < Z ∧ K ⊔ S ≤ normalizer (B : Set G) ∧
      HasSectionModel K B ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K Z B (linearThreeActor e) (specialLinearNatural 3) := by
  let : MulAction S (invariantSubgroups K Z) := {
    smul := conjugateSubgroup S hSK hSZ
    one_smul := fun A => Subtype.ext (by
      change A.val.map (MulAut.conj (1:G)).toMonoidHom=A.val
      have hi : (MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G := by ext x; simp
      rw [hi,map_id])
    mul_smul := fun s t A => Subtype.ext (by
      change A.val.map (MulAut.conj ((s:G)*(t:G))).toMonoidHom=
        (A.val.map (MulAut.conj (t:G)).toMonoidHom).map (MulAut.conj (s:G)).toMonoidHom
      rw [map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply,mul_assoc]) }
  have hodd : ¬2 ∣ Nat.card (invariantSubgroups K Z) := by
    rw [invariantSubgroups_card e hm]
    have hh := Nat.even_iff.mp heven
    simp [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,hh]
  obtain ⟨B,hB⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (invariantSubgroups K Z) hodd
  have hfix (s : S) : B.val.map (MulAut.conj (s:G)).toMonoidHom=B.val :=
    congrArg Subtype.val (hB s)
  exact ⟨B.val,B.property.1,B.property.2.1,
    sup_le B.property.2.2 (fun s hs => mem_normalizer_iff_map_conj_eq.mpr (hfix ⟨s,hs⟩)),
    CentralDerivedSections.proper_invariant_sections e hm B.property.2.1.le B.property.2.2
      B.property.1.ne.symm B.property.2.1.ne⟩

variable [Finite G] [Finite F] {Q : Subgroup G}
local notation "ZQ" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q

/-- A nonabelian two-group with doubled natural center admits a natural
central subgroup in both characteristic layers, normal under K and any
normalizing two-group S. Both sections retain the original marking. -/
theorem exists_derived_invariant_flag
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (heven : Even (Nat.card F)) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ZQ ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative Q)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hSK : S ≤ normalizer (K : Set G)) (hSQ : S ≤ normalizer (Q : Set G)) :
    ∃ B : Subgroup G, ⊥ < B ∧ B < ZQ ∧ B ≤ ⁅Q,Q⁆ ∧ B ≤ frattiniIn Q ∧
      K ⊔ S ≤ normalizer (B : Set G) ∧
      HasSectionModel K B ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K ZQ B (linearThreeActor e) (specialLinearNatural 3) := by
  have hh := CentralDerivedSections.derived_frattini_sections hQ hKQ e hm hna
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hDP : (⁅Q,Q⁆ : Subgroup G) ≤ frattiniIn Q := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  by_cases hZD : ZQ ≤ ⁅Q,Q⁆
  · obtain ⟨B,hB0,hBZ,hBn,hB,hquot⟩ := exists_invariant_flag heven e hm S hS hSK
      (hSQ.trans (normalizer_le_normalizer_characteristic_image Q (center Q)))
    exact ⟨B,hB0,hBZ,hBZ.le.trans hZD,hBZ.le.trans (hZD.trans hDP),hBn,hB,hquot⟩
  · have hBJ : K ⊔ S ≤ normalizer ((ZQ ⊓ ⁅Q,Q⁆ : Subgroup G) : Set G) := by
      have hJQ : K ⊔ S ≤ normalizer (Q : Set G) := sup_le hKQ hSQ
      have hJD : K ⊔ S ≤ normalizer ((⁅Q,Q⁆ : Subgroup G) : Set G) := by
        rw [←map_subtype_commutator]
        exact hJQ.trans (normalizer_le_normalizer_characteristic_image Q (_root_.commutator Q))
      exact (le_inf (hJQ.trans (normalizer_le_normalizer_characteristic_image Q (center Q)))
        hJD).trans inf_normalizer_le_normalizer_inf
    have hproper : ZQ ⊓ ⁅Q,Q⁆ < ZQ := lt_of_le_of_ne inf_le_left (by
      intro he
      exact hZD (he.symm ▸ (inf_le_right : ZQ ⊓ ⁅Q,Q⁆ ≤ ⁅Q,Q⁆)))
    exact ⟨ZQ ⊓ ⁅Q,Q⁆,bot_lt_iff_ne_bot.mpr hh.1,hproper,inf_le_right,
      inf_le_right.trans hDP,hBJ,hh.2.2.1.resolve_left hZD⟩

variable {R : Subgroup G} {n : ℕ} [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
include h hn

/-- In the genuine nonabelian doubled-omega MS branch the central natural
flag can be chosen normal in the entire original KR. There is no additional
radical-invariance hypothesis, including at field four. -/
theorem ms_exists_derived_normal_flag
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R))
      ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative (msQ K R)) :
    let Q := msQ K R
    let Z := Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
    ∃ B : Subgroup G, ⊥ < B ∧ B < Z ∧ B ≤ ⁅Q,Q⁆ ∧ B ≤ frattiniIn Q ∧
      K ⊔ R ≤ normalizer (B : Set G) ∧
      HasSectionModel K B ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K Z B (linearThreeActor e) (specialLinearNatural 3) := by
  have hR : IsPGroup 2 R := by
    obtain ⟨A,_,_,he⟩ := oddIndex h hn
    rw [←he]
    exact isPGroup_pCoreIn 2 A
  have heven : Even (Nat.card F) := by
    rw [h.field_card]
    exact even_two.pow_of_ne_zero (by omega : n ≠ 0)
  exact exists_derived_invariant_flag
    ((isPGroup_pCoreIn 2 (K ⊔ R)).to_le msQ_le_joinCore)
    ((le_sup_left : K ≤ K ⊔ R).trans (CentralSections.join_normalizes_core h hn))
    heven e (DoubledCenter.center_doubled h hn e hm) hna R hR
    (radical_normalizes h hn)
    ((le_sup_right : R ≤ K ⊔ R).trans (CentralSections.join_normalizes_core h hn))

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CentralInvariantFlags
