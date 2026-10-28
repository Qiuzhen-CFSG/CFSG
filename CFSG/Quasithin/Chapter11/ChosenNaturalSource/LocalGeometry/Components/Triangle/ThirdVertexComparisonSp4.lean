module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LocalGLSp4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LocalQuotientEquality
public import Theory.SpecificGroups.Triality.OddSupplement
public import GorensteinWalter.A7SylowCentralizer
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSection

/-!
# Comparing both original local sections at the third vertex

At one fixed Sylow of the genuine triality group over four, every proper
local component with A₅ two-core quotient is the central parabolic residual.
The other residual has quotient PSL₂(64), so its order excludes that marking.
Consequently two such proper components cannot generate the triality group.

In A₇ the same full-Sylow condition makes each local A₅ the five-letter
subgroup. After aligning the Sylow, its element of cycle type (4,2) fixes
only one two-letter subset, forcing both local subgroups to coincide.
Solvable kernels preserve a perfect group's simple two-core quotient; this
also excludes the actual central three-cover, without assuming it splits.

The literal consumer starts from the already authorized nontrivial common Q,
constructs I = K₀ ∨ L₂ with both original local markings, and removes the
triality and both alternating-seven rows. All quotient transports retain the
original maps and intrinsic two-cores. The remaining odd ternary, sporadic
and odd-extension comparisons, common-normal existence, SL₃(4) exclusion,
maximal-faithful placement and both orientations remain with
qt-d-1222-natural-relative-components. Earlier flag and Cartan inputs retain
their existing producers and final discharge by
qt-d-1222-natural-local-geometry. This is not the completed three-model
recognition or source 11.1.2.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--764, especially the A.3.14 comparison on p.763.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
public noncomputable section

private theorem local_perfect {A : Type*} [Group A] {B S : Subgroup A}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem perfect_le_triality_local (P : Parameters) (a : Node)
    (B : Subgroup (Carrier P)) [Group.IsPerfect B] (hp : P.prime = 2)
    (hB : B ≤ parabolic P a) : B ≤ localFactor P a := by
  let C := B.subgroupOf (parabolic P a)
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have h := le_of_isPerfect_of_solvable_quotient C
    ((localFactor P a).subgroupOf (parabolic P a))
  exact fun x hx => h (show (⟨x,hB hx⟩ : parabolic P a) ∈ C from hx)

private theorem aligned_triality_five_eq_central
    (B : Subgroup (BinaryCarrier 2 (by decide)))
    (hB : B ∈ localCComponents (unipotentSylow (binaryParameters 2 (by decide)) rfl))
    (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B = localFactor (binaryParameters 2 (by decide)) .central := by
  let P := binaryParameters 2 (by decide)
  have hjoin : B ⊔ unipotent P ≠ ⊤ := by
    intro he
    have hh := hB.subnormal
    change (B.subgroupOf (B ⊔ unipotent P)).IsSubnormal at hh
    rw [he] at hh
    have hs : B.IsSubnormal := by
      have h := hh.trans' IsSubnormal.top
      simpa only [map_subgroupOf_eq_of_le le_top] using h
    rcases hs.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
    · rw [hb] at hB
      exact hB.ne_bot (by simp)
    · exact hproper ht
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic 2 (by decide) (B ⊔ unipotent P)
    le_sup_right hjoin
  let := local_perfect hB
  have hBP := perfect_le_triality_local P a B rfl (le_sup_left.trans ha)
  have hSP := unipotentSylow_le_localFactor P rfl a
  let := localFactor_isPerfect P rfl (by decide : 2 < P.q) a
  cases a with
  | arms =>
    have he := FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .arms)
      (by rw [card_extensionField]; decide)
      ((localFactorArmsQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm)
      (unipotentSylow P rfl) B hB hBP hSP
    let a := MulEquiv.subgroupCongr he
    let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have hf := FiveLocalFF.field_four_of_sl2_five_section e
      (aq.trans ((localFactorArmsQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm))
    norm_num [card_extensionField,P,Parameters.q,binaryParameters] at hf
  | central =>
    exact FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .central)
      (by rw [GaloisField.card 2 2 (by decide)]; decide)
      ((localFactorCentralQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm)
      (unipotentSylow P rfl) B hB hBP hSP

private theorem five_equiv {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSL A 2 4) : Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).map
    (fun a => e.trans a)

/-- Two proper local A₅ sections at the same full Sylow cannot generate
an actual triality group over the field of order four. -/
theorem not_triality_four_of_local_five_pair
    {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) (B C : Subgroup A)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hBproper : B ≠ ⊤) (hCproper : C ≠ ⊤) (hgen : B ⊔ C = ⊤)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    ¬ IsTrialityGroupAt 4 A := by
  intro hm
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff A 2 (by decide)).mp hm
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    e S (unipotentSylow (binaryParameters 2 (by decide)) rfl)
  let f := a.toMonoidHom
  let : Group.IsSolvable f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr a.injective]
    infer_instance
  have step (D : Subgroup A) (hD : D ∈ localCComponents S) (hne : D ≠ ⊤)
      (hmodel : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 4) :
      D.map f = localFactor (binaryParameters 2 (by decide)) .central := by
    have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hD f
    change D.map f ∈ localCComponents ((S : Subgroup A).map f) at hl
    rw [hS] at hl
    have hn : D.map f ≠ ⊤ := by
      intro ht
      apply hne
      apply map_injective (f := f) a.injective
      rw [ht,map_top_of_surjective f a.surjective]
    let d := D.equivMapOfInjective f a.injective
    let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    exact aligned_triality_five_eq_central (D.map f) hl hn
      (dq.symm.trans (five_equiv hmodel).some)
  have he := congrArg (Subgroup.map f) hgen
  rw [Subgroup.map_sup,step B hB hBproper hmB,step C hC hCproper hmC,sup_idem,
    map_top_of_surjective f a.surjective] at he
  exact parabolic_ne_top_binary (binaryParameters 2 (by decide)) rfl .central
    (top_le_iff.mp (he ▸ localFactor_le_parabolic (binaryParameters 2 (by decide)) .central))

/-- The two original proper local components cannot generate a local
component whose actual two-core quotient is triality over four. -/
theorem local_join_not_triality_four
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C I : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hI : I ∈ localCComponents T) (hBI : B < I) (hCI : C < I)
    (hgen : B ⊔ C = I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    ¬ IsTrialityGroupAt 4 (I ⧸ pCore 2 I) := by
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI.le
  have hCS : C.subgroupOf I ∈ localCComponents S :=
    hS.symm ▸ local_restrict hC hCI.le
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using
      hI.subgroupOf_of_le (show I ≤ I from le_rfl) (show I ≤ I ⊔ T from le_sup_left)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have step (D : Subgroup G) (hD : D < I)
      (hDS : D.subgroupOf I ∈ localCComponents S)
      (hm : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 4) :
      (D.subgroupOf I).map q ∈ localCComponents (S.mapSurjective hq) ∧
      (D.subgroupOf I).map q ≠ ⊤ ∧
      ClassicalGroup.IsPSL (((D.subgroupOf I).map q) ⧸ pCore 2 ((D.subgroupOf I).map q)) 2 4 := by
    refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hDS q,?_,?_⟩
    · intro he
      have he' : (D.subgroupOf I).map q = (⊤ : Subgroup I).map q := by
        rw [he,map_top_of_surjective q hq]
      have ht := local_cComponent_eq_of_map_eq hDS htop le_top q
        (hk.le_sylow_of_normal S) he'
      exact hD.not_ge (subgroupOf_eq_top.mp ht)
    · let d := subgroupOfEquivOfLe hD.le
      let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
      have hker : IsPGroup 2 (q.subgroupMap (D.subgroupOf I)).ker := by
        rw [ker_subgroupMap]
        exact hk.comap_subtype
      let a := (q.subgroupMap (D.subgroupOf I)).quotientPCoreEquivOfSurjective
        (q.subgroupMap_surjective _) hker
      exact hm.of_mulEquiv (a.symm.trans dq)
  obtain ⟨hb,hbp,hbm⟩ := step B hBI hBS hmB
  obtain ⟨hc,hcp,hcm⟩ := step C hCI hCS hmC
  apply not_triality_four_of_local_five_pair (S.mapSurjective hq)
    ((B.subgroupOf I).map q) ((C.subgroupOf I).map q) hb hc hbp hcp ?_ hbm hcm
  rw [←Subgroup.map_sup,←subgroupOf_sup hBI.le hCI.le,hgen,subgroupOf_self,
    map_top_of_surjective q hq]

private theorem normalizer_preserves_fixed
    {A Ω : Type*} [Group A] [MulAction A Ω] (B : Subgroup A)
    {g : A} (hg : g ∈ normalizer (B : Set A)) {x : Ω}
    (hx : x ∈ MulAction.fixedPoints B Ω) :
    g • x ∈ MulAction.fixedPoints B Ω := by
  intro b
  have h := hx ⟨g⁻¹ * b.val * g,(mem_normalizer_iff''.mp hg b.val).mp b.property⟩
  simpa only [mul_smul,inv_smul_smul,smul_inv_smul,Subgroup.smul_def] using congrArg (fun y => g • y) h

private theorem aligned_seven_five_eq
    (B : Subgroup (alternatingGroup (Fin 7)))
    (hB : B ∈ localCComponents GorensteinWalter.a7SylowD8)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B = fixingSubgroup (alternatingGroup (Fin 7)) ({4,5} : Set (Fin 7)) := by
  classical
  let b := alternatingGroup.SevenFiveSection.fiveEquiv B e
  have hn := alternatingSeven_local_five_normalized B b GorensteinWalter.a7SylowD8 hB
  have hc := Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two
    B b GorensteinWalter.a7SylowD8 hn
  obtain ⟨i,j,hij,hfix⟩ := Set.ncard_eq_two.mp hc
  have hpres (x : Fin 7) (hx : x ∈ ({i,j} : Set (Fin 7))) :
      GorensteinWalter.d8rho x ∈ ({i,j} : Set (Fin 7)) := by
    rw [←hfix] at hx ⊢
    exact normalizer_preserves_fixed B (hn GorensteinWalter.a7D8rho_mem) hx
  have hp : ({i,j} : Set (Fin 7)) = {4,5} := by
    have hsmall : ∀ i j : Fin 7, i ≠ j →
        (GorensteinWalter.d8rho i = i ∨ GorensteinWalter.d8rho i = j) →
        (GorensteinWalter.d8rho j = i ∨ GorensteinWalter.d8rho j = j) →
        (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by decide +kernel
    rcases hsmall i j hij (hpres i (by simp)) (hpres j (by simp)) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Set.pair_comm 5 4
  have hF : MulAction.fixedPoints B (Fin 7) = {4,5} := hfix.trans hp
  apply eq_of_le_of_card_ge
  · intro x hx y
    have hy : y.val ∈ MulAction.fixedPoints B (Fin 7) := hF.symm ▸ y.property
    exact hy ⟨x,hx⟩
  · let a := Atlas.Families.Alternating.stabilizerComplementEquiv
      ({4,5} : Finset (Fin 7))
    have he : Nat.card (fixingSubgroup (alternatingGroup (Fin 7))
        ({4,5} : Set (Fin 7))) = 60 := by
      have hset : (({4,5} : Finset (Fin 7)) : Set (Fin 7)) = {4,5} := by
        simp only [Finset.coe_insert,Finset.coe_singleton]
      let : Nontrivial (↑(({4,5} : Finset (Fin 7))ᶜ)) :=
        ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩,by decide⟩⟩
      have hc : Nat.card (↑(({4,5} : Finset (Fin 7))ᶜ)) = 5 := by
        rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl]
        decide
      rw [←hset,Nat.card_congr a.toEquiv,nat_card_alternatingGroup,hc]
      norm_num [Nat.factorial]
    rw [he,Nat.card_congr b.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- At a fixed full Sylow of A₇ there is only one local component with
A₅ two-core quotient. The same literal five-letter fixer contains both. -/
theorem seven_local_five_eq
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (B C : Subgroup (alternatingGroup (Fin 7)))
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) : B = C := by
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (alternatingGroup (Fin 7))) S GorensteinWalter.a7SylowD8
  let f := a.toMonoidHom
  let : Group.IsSolvable f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr a.injective]
    infer_instance
  have step (D : Subgroup (alternatingGroup (Fin 7)))
      (hD : D ∈ localCComponents S)
      (eD : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 5)) :
      D.map f = fixingSubgroup (alternatingGroup (Fin 7)) ({4,5} : Set (Fin 7)) := by
    have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hD f
    change D.map f ∈ localCComponents ((S : Subgroup (alternatingGroup (Fin 7))).map f) at hl
    rw [hS] at hl
    let d := D.equivMapOfInjective f a.injective
    let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    exact aligned_seven_five_eq (D.map f) hl (dq.symm.trans eD)
  exact map_injective (f := f) a.injective ((step B hB eB).trans (step C hC eC).symm)

/-- Solvable kernels preserve the original two local A₅ sections, so
a group generated by them has no alternating-seven solvable quotient. -/
theorem no_seven_solvable_quotient_of_local_five_pair
    {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) (B C : Subgroup A)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hgen : B ⊔ C = ⊤)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (f : A →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] : False := by
  have step (D : Subgroup A) (hD : D ∈ localCComponents S)
      (hm : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 4) :
      Nonempty (((D.map f) ⧸ pCore 2 (D.map f)) ≃* alternatingGroup (Fin 5)) := by
    let := local_perfect hD
    let e := (five_equiv hm).some
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (D ⧸ pCore 2 D) := e.isSimpleGroup
    let : Group.IsSolvable (f.subgroupMap D).ker := by
      rw [ker_subgroupMap]
      let j : f.ker.subgroupOf D →* f.ker :=
        (D.subtype.comp (f.ker.subgroupOf D).subtype).codRestrict f.ker (fun x => x.property)
      exact Group.isSolvable_of_isSolvable_injective (f := j) (fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : A)) h)))
    let a := PerfectCoreTwoExtension.solvableKernelQuotientEquiv
      (f.subgroupMap D) (f.subgroupMap_surjective D)
    exact ⟨a.symm.trans e⟩
  obtain ⟨eB⟩ := step B hB hmB
  obtain ⟨eC⟩ := step C hC hmC
  have he := seven_local_five_eq (S.mapSurjective hf) (B.map f) (C.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hC f) eB eC
  have ht : B.map f = ⊤ := by
    have h := congrArg (Subgroup.map f) hgen
    simpa only [Subgroup.map_sup,←he,sup_idem,map_top_of_surjective f hf] using h
  have hcard := Nat.card_congr (alternatingGroup.SevenFiveSection.fiveEquiv (B.map f) eB).toEquiv
  rw [ht,card_top,nat_card_alternatingGroup,nat_card_alternatingGroup] at hcard
  norm_num [Nat.factorial] at hcard

/-- The original join excludes A₇ and its genuine central cover. Both
normal two-core and central quotient maps retain the local section. -/
theorem local_join_not_seven
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C I : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hI : I ∈ localCComponents T) (hBI : B ≤ I) (hCI : C ≤ I)
    (hgen : B ⊔ C = I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (I ⧸ pCore 2 I) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (I ⧸ pCore 2 I) 7) := by
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI
  have hCS : C.subgroupOf I ∈ localCComponents S := hS.symm ▸ local_restrict hC hCI
  let q := QuotientGroup.mk' (pCore 2 I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : Group.IsNilpotent q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hgen' : B.subgroupOf I ⊔ C.subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup hBI hCI,hgen,subgroupOf_self]
  let b := subgroupOfEquivOfLe hBI
  let c := subgroupOfEquivOfLe hCI
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  have step (k : (I ⧸ pCore 2 I) →* alternatingGroup (Fin 7))
      (hk : Function.Surjective k) (hks : Group.IsSolvable k.ker) : False := by
    let := hks
    let : Group.IsSolvable (k.comp q).ker := by
      rw [← MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker q k.ker
    exact no_seven_solvable_quotient_of_local_five_pair S (B.subgroupOf I) (C.subgroupOf I)
      hBS hCS hgen' (hmB.of_mulEquiv bq) (hmC.of_mulEquiv cq) (k.comp q) (hk.comp hq)
  rintro (⟨⟨e⟩⟩ | ⟨_,_,⟨e⟩⟩)
  · apply step e.toMonoidHom e.surjective
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  · let k := e.toMonoidHom.comp (QuotientGroup.mk' (center (I ⧸ pCore 2 I)))
    apply step k (e.surjective.comp (QuotientGroup.mk'_surjective _))
    change Group.IsSolvable (e.toMonoidHom.comp (QuotientGroup.mk' _)).ker
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The source common-normal construction and the two original local
markings exclude triality and both alternating-seven rows from the actual
third vertex. The remaining field-four rows retain their further comparisons. -/
theorem sp4_triangle_join_comparison_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    let A := I ⧸ pCore 2 I
    ¬ IsTrialityGroupAt 4 A ∧
      ¬ (Chapter1.Section02.LocalModels.IsAlternating A 7 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover A 7) ∧
      (Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4 ∨
        FieldFourOvergroup A) := by
  intro I A
  obtain ⟨_,hIL,_,_,_,_,hmark⟩ := sp4_triangle_marked_locals_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hb,_,_,hmb,_,_⟩ := hmark K₀ (.inl rfl)
  obtain ⟨hc,_,_,hmc,_,_⟩ := hmark (f.Li 1) (.inr rfl)
  have hn := local_join_not_triality_four T hK₀.1
    (flag_mem_local_of_model D S f 1 hm₂).1 hIL.1 hb hc rfl hmb hmc
  have hseven := local_join_not_seven T hK₀.1
    (flag_mem_local_of_model D S f 1 hm₂).1 hIL.1 hb.le hc.le rfl hmb hmc
  refine ⟨hn,hseven,?_⟩
  obtain ⟨_,_,hm,_⟩ := sp4_triangle_join_remaining_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  rcases hm with hm | hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · exact (hn hm).elim
  · exact .inr (.inr (.inr hm))

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
