module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Minimum
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage
public import Theory.SpecificGroups.PSL2.BinaryOuterGeometry

/-!
# Actual elementary images for the generation minimum

Every local E-member quotient kills the intersection with the ambient
O₂. Its image rank is therefore bounded by the rank of the same elementary
subgroup in the ambient two-core quotient. If every such image in the
prescribed Sylow had rank below n(H) > 1, the existing generation witness
would descend to n(H)-1. This constructs an actual elementary subgroup
of that Sylow with image rank at least n(H), without lifting an arbitrary
quotient subgroup or identifying n(H) with a model exponent.

For a normal source component with literal PSL₂(2^f) quotient, its image
in H/O₂(H) is self-centralizing. A selected elementary image outside this
component forces f = 2m and n(H) ≤ m+1 by the genuine outer-involution
fixed-group bound. Otherwise it lies in the root determined by the original
Sylow. Odd f, or n(H) > f/2+1, excludes the outer alternative.

A nonzero root image invariant under its full root normalizer is the whole
root: the binary torus acts by all nonzero scalar multipliers. The source
application retains the same elementary subgroup and quotient map, and
feeds this constructed full lift to Minimum. The final alternative thus
identifies two precise remaining cases: a large image failing root-normalizer
invariance, or the even-degree outer bound. Neither is excluded here.

Construction of an unconditional full root lift, the other model and FF
exclusions, and paired/doubled assembly remain with this theorem-family
owner. This module does not assert unconditional 11.3.5 or 11.3.6.
Source: Aschbacher--Smith E.1.2--6, pp.209--211, and 11.3.5(1),
pp.771--772 (refs/quasithin.pdf). The outer bound uses the concrete binary
PSL₂ automorphism geometry cited in the imported source module.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
open ChapterE
variable {X : Type*} [Group X] [Finite X]

private theorem rank_local_image_le_core_image (A B : Subgroup X) (hAB : A ≤ B)
    (N : Subgroup B) [N.Normal] (hN : (pCore 2 X).subgroupOf B ≤ N) :
    Group.rank ((A.subgroupOf B).map (QuotientGroup.mk' N)) ≤
      Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) := by
  let C := A.subgroupOf B
  let f := (QuotientGroup.mk' (pCore 2 X)).comp (B.subtype.comp C.subtype)
  let g := (QuotientGroup.mk' N).comp C.subtype
  have hk : f.ker ≤ g.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    change (QuotientGroup.mk' (pCore 2 X)) (x.val : X) = 1 at hx
    have hxcore : (x.val : X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp hx
    exact hN hxcore
  have hr := Group.rank_le_of_surjective
    (QuotientGroup.map f.ker g.ker (MonoidHom.id C) hk)
    (QuotientGroup.map_surjective_of_surjective _ _ _ QuotientGroup.mk_surjective hk)
  rw [Group.rank_congr (QuotientGroup.quotientKerEquivRange f),
    Group.rank_congr (QuotientGroup.quotientKerEquivRange g)] at hr
  have hf : f.range = A.map (QuotientGroup.mk' (pCore 2 X)) := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,range_subtype,
      map_subgroupOf_eq_of_le hAB]
  have hg : g.range = (A.subgroupOf B).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp,range_subtype]
  exact (Group.rank_congr (MulEquiv.subgroupCongr hg)).symm.le.trans
    (hr.trans (Group.rank_congr (MulEquiv.subgroupCongr hf)).le)

private theorem member_at_core_image_rank {T A B : Subgroup X}
    (h : IsEMember T A B) :
    IsEMemberAt (Group.rank (A.map (QuotientGroup.mk' (pCore 2 X)))) T A B := by
  have hb : (pCore 2 X).subgroupOf B ≤ pCore 2 B :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  refine ⟨h,?_⟩
  rcases h.2.2.2.2.2 with ho | hc
  · exact .inl ⟨ho,rank_local_image_le_core_image A B h.2.2.1 _ hb⟩
  · let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
    have hbr : pCore 2 B ≤ solvableRadical B :=
      le_solvableRadical _ inferInstance inferInstance
    exact .inr ⟨hc,rank_local_image_le_core_image A B h.2.2.1 _ (hb.trans hbr)⟩

/-- A bound on actual elementary images in one prescribed Sylow lowers any
existing generation bound, preserving both local quotient conventions. -/
theorem isEGeneratedAt_of_elementary_core_image_bound (P : Sylow 2 X)
    {i j : ℕ} (hgen : IsEGeneratedAt j P)
    (hr : ∀ A : Subgroup X, IsElementaryAbelian 2 A → A ≤ (P : Subgroup X) →
      Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) ≤ i) :
    IsEGeneratedAt i P := by
  intro Ω hΩ
  apply top_unique
  rw [← hgen Ω hΩ]
  apply sup_le_sup_right
  apply iSup_mono
  intro A
  apply sSup_le_sSup
  intro B hB
  exact (member_at_core_image_rank hB.1).mono (hr A.val (hΩ.1 _ A.property.1) A.property.2)

/-- A generation minimum above one is witnessed by an actual elementary
subgroup, in the specified Sylow, with at least that rank modulo O₂(X). -/
theorem exists_elementary_core_image_rank_ge (P : Sylow 2 X)
    (hn : 1 < generationParameter X) :
    ∃ A : Subgroup X, IsElementaryAbelian 2 A ∧ A ≤ (P : Subgroup X) ∧
      generationParameter X ≤ Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) := by
  by_contra hnone
  have hr : ∀ A : Subgroup X, IsElementaryAbelian 2 A → A ≤ (P : Subgroup X) →
      Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) ≤ generationParameter X - 1 := by
    intro A hA hAP
    have hh : ¬ generationParameter X ≤
        Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) :=
      fun h => hnone ⟨A,hA,hAP,h⟩
    omega
  have hgen := isEGeneratedAt_of_elementary_core_image_bound P
    (isEGenerated_generationParameter_of_pos (by omega) P) hr
  have hl := generationParameter_le (by omega : 0 < generationParameter X - 1)
    hgen.isEGenerated
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]

omit [Finite Y] in
private theorem linear_equiv {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL Y 2 (2 ^ f)) : Nonempty (Y ≃* Theory.PSL2.BinaryGroup f) := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let a : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using
      hc.trans (GaloisField.card 2 f (by omega)).symm)
  exact ⟨e.trans (Atlas.fieldEquivPSL 2 a)⟩

private theorem linear_outer_rank_bound (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f))
    (A : Subgroup Y) [IsElementaryAbelian 2 A] (hout : ¬ A ≤ J) :
    ∃ m : ℕ, 0 < m ∧ f = 2 * m ∧ Group.rank A ≤ m + 1 := by
  obtain ⟨e⟩ := linear_equiv hf hm
  obtain ⟨m,hm,hf,hr,_⟩ :=
    Theory.PSL2.BinaryOuterGeometry.outer_elementary_card_bound J e hC hf A hout
  exact ⟨m,hm,hf,IsElementaryAbelian.rank_le_of_card_le A hr⟩

/-- An elementary image of sufficiently large rank must lie in the original
normal binary PSL₂ component. The exceptional outer bound retains f = 2m. -/
theorem linear_image_inner_or_half_degree (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) {f k : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f))
    (A : Subgroup Y) [IsElementaryAbelian 2 A] (hk : k ≤ Group.rank A) :
    A ≤ J ∨ ∃ m : ℕ, 0 < m ∧ f = 2 * m ∧ k ≤ m + 1 := by
  by_cases hi : A ≤ J
  · exact .inl hi
  · obtain ⟨m,hm,hf,hr⟩ := linear_outer_rank_bound J hC hf hm A hi
    exact .inr ⟨m,hm,hf,hk.trans hr⟩

/-- A nontrivial elementary image invariant under the root normalizer is
already a full root. The same original image is retained. -/
theorem linear_root_image_eq_of_normalizer_invariant
    (J : Subgroup Y) {f : ℕ} (_hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f))
    (P : Sylow 2 J) (A : Subgroup Y)
    (hAP : A ≤ (P : Subgroup J).map J.subtype) (hne : A ≠ ⊥)
    (hn : (normalizer (P : Set J)).map J.subtype ≤ normalizer (A : Set Y)) :
    A = (P : Subgroup J).map J.subtype := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let B := A.subgroupOf J
  have hAJ : A ≤ J := hAP.trans (map_subtype_le _)
  have hBP : B ≤ (P : Subgroup J) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAP hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hB : B ≠ ⊥ := by
    intro hb
    apply hne
    have hb' : A.subgroupOf J = ⊥ := hb
    rw [← map_subgroupOf_eq_of_le hAJ,hb',Subgroup.map_bot]
  have hnorm : normalizer (P : Set J) ≤ normalizer (B : Set J) := by
    intro x hx
    have hh := hn (mem_map_of_mem J.subtype hx)
    rw [mem_normalizer_iff]
    intro b
    exact (mem_normalizer_iff.mp hh) b
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have heq : B.map a.toMonoidHom = (P : Subgroup J).map a.toMonoidHom := by
    apply Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant P'
      (B.map a.toMonoidHom) (map_mono hBP)
    · intro hb
      apply hB
      exact (map_eq_bot_iff_of_injective B a.injective).mp hb
    · change normalizer ((P : Subgroup J).map a.toMonoidHom : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
        normalizer (B.map a.toMonoidHom : Set (Matrix.SpecialLinearGroup (Fin 2) F))
      rw [← map_normalizer_eq_of_bijective _ a.bijective,
        ← map_normalizer_eq_of_bijective _ a.bijective]
      exact map_mono hnorm
  have hEq : B = (P : Subgroup J) := map_injective a.injective heq
  have hh := congrArg (map J.subtype) hEq
  rwa [map_subgroupOf_eq_of_le hAJ] at hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The original counterexample supplies an actual elementary subgroup in T,
with quotient rank at least the actual minimum. No quotient model is used. -/
theorem exists_large_elementary_core_image
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧
      A ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
      ChapterE.generationParameter H ≤
        Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) := by
  have hk := degree_le_parameter h pr hc hs
  have hn := S.nonbinary
  exact Models.exists_elementary_core_image_rank_ge (T.subtype h.outside.1.1.2) (by omega)

/-- Select the actual root in the image of the prescribed Sylow, and an
actual elementary subgroup above a large image. If the image is not in this
root, the independent model exponent is even with the sharp outer bound. -/
theorem ComponentSeed.exists_large_root_image_or_outer_bound (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    ∃ (P : Sylow 2 J) (A : Subgroup H), IsElementaryAbelian 2 A ∧
      A ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
      ChapterE.generationParameter H ≤ Group.rank (A.map q) ∧
      (P : Subgroup J).map J.subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map q ⊓ J ∧
      (A.map q ≤ (P : Subgroup J).map J.subtype ∨
        ∃ m : ℕ, 0 < m ∧ f = 2 * m ∧ ChapterE.generationParameter H ≤ m + 1) := by
  let B := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := B.map q
  let U := (T.subtype h.outside.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let : B.Normal := hn
  let : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hmJ : ClassicalGroup.IsPSL J 2 (2 ^ f) := hm.of_mulEquiv e.symm
  let : IsSimpleGroup J := by
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hmJ
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [hF]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf)
    exact a.isSimpleGroup
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hgen : J ⊔ (U : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change B.map q ⊔ (T.subtype h.outside.1.1.2 : Subgroup H).map q = ⊤
    rw [←Subgroup.map_sup,s.intrinsic_supplement h.outside.1.1.2,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hC : centralizer (J : Set (H ⧸ pCore 2 H)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient J (Group.IsPerfect.not_isMulCommutative J)
      (isPGroup_quotient_of_sup_eq_top J (U : Subgroup (H ⧸ pCore 2 H)) U.isPGroup' hgen)
      (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨P,hP⟩ := U.exists_sylow_map_eq_inf_of_normal J
  obtain ⟨A,hA,hAT,hr⟩ := exists_large_elementary_core_image h pr hc hs
  let := hA
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  refine ⟨P,A,hA,hAT,hr,hP,?_⟩
  rcases Models.linear_image_inner_or_half_degree J hC hf hmJ (A.map q) hr with hi | ho
  · exact .inl (hP ▸ le_inf (map_mono hAT) hi)
  · exact .inr ho

/-- In the normal PSL₂ row, root-normalizer invariance constructs the full
lift on the same elementary subgroup, then feeds the minimum recognition.
This is a conditional criterion; existence of such invariance is not assumed
by the source setup. -/
theorem ComponentSeed.rankOneReduction_of_normal_linear_invariant_image
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hAP : A.map (QuotientGroup.mk' (pCore 2 H)) ≤
      (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype)
    (hne : ¬ A ≤ pCore 2 H)
    (hinv : (normalizer (P : Set ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))).map
      ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype ≤
        normalizer (A.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))) :
    ChapterE.generationParameter H = f ∧ RankOneReduction S H := by
  let := s.quasisimple
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have he := Models.linear_root_image_eq_of_normalizer_invariant _ hf
    (hm.of_mulEquiv e.symm) P (A.map (QuotientGroup.mk' (pCore 2 H))) hAP
    (fun hz => hne (by simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp hz)) hinv
  exact ⟨s.linear_parameter_eq_of_normal_lift h pr hc hs hn hf hm P A he,
    s.rankOneReduction_of_normal_linear_lift h pr hc hs hn hf hm P A he⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The normal PSL₂ row either has its genuine generation minimum, or has
a concrete large elementary root image failing Borel invariance, or satisfies
the sharp even-degree outer bound. This does not assert that either remaining
obstruction is impossible under the source hypotheses. -/
theorem ComponentSeed.normal_linear_root_lift_alternative (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    (ChapterE.generationParameter H = f ∧ RankOneReduction S H) ∨
      (∃ (P : Sylow 2 J) (A : Subgroup H), IsElementaryAbelian 2 A ∧
        A ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
        ChapterE.generationParameter H ≤ Group.rank (A.map q) ∧
        (P : Subgroup J).map J.subtype =
          (T.subtype h.outside.1.1.2 : Subgroup H).map q ⊓ J ∧
        A.map q ≤ (P : Subgroup J).map J.subtype ∧
        ¬ (normalizer (P : Set J)).map J.subtype ≤ normalizer (A.map q : Set _)) ∨
      (∃ m : ℕ, 0 < m ∧ f = 2 * m ∧ ChapterE.generationParameter H ≤ m + 1) := by
  obtain ⟨P,A,hA,hAT,hr,hP,hi | ho⟩ :=
    s.exists_large_root_image_or_outer_bound h pr hc hs hn hf hm
  · let := hA
    by_cases hinv : (normalizer
        (P : Set ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))).map
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype ≤
        normalizer (A.map (QuotientGroup.mk' (pCore 2 H)) : Set _)
    · have hne : ¬ A ≤ pCore 2 H := by
        intro hcore
        have hzero : A.map (QuotientGroup.mk' (pCore 2 H)) = ⊥ :=
          (map_eq_bot_iff A).mpr (by simpa only [QuotientGroup.ker_mk'] using hcore)
        rw [hzero,Group.rank_eq_zero] at hr
        have hl := degree_le_parameter h pr hc hs
        have hh := S.nonbinary
        omega
      exact .inl (s.rankOneReduction_of_normal_linear_invariant_image h pr hc hs
        hn hf hm P A hi hne hinv)
    · exact .inr (.inl ⟨P,A,hA,hAT,hr,hP,hi,hinv⟩)
  · exact .inr (.inr ho)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Odd model degree, or a generation minimum above the outer bound,
constructs an actual large elementary lift into the original root. Its
image is not silently enlarged from a proper subspace to the full root. -/
theorem ComponentSeed.exists_large_root_image (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (hinner : Odd f ∨ f / 2 + 1 < ChapterE.generationParameter H) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    ∃ (P : Sylow 2 J) (A : Subgroup H), IsElementaryAbelian 2 A ∧
      A ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
      ChapterE.generationParameter H ≤ Group.rank (A.map q) ∧
      (P : Subgroup J).map J.subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map q ⊓ J ∧
      A.map q ≤ (P : Subgroup J).map J.subtype := by
  obtain ⟨P,A,hA,hAT,hr,hP,hi | ⟨m,hm0,hfm,hkm⟩⟩ :=
    s.exists_large_root_image_or_outer_bound h pr hc hs hn hf hm
  · exact ⟨P,A,hA,hAT,hr,hP,hi⟩
  · rcases hinner with ⟨a,ha⟩ | hh <;> omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
