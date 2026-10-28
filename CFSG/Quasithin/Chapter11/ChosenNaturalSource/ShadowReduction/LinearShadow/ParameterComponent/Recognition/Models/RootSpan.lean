module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RootLift
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Saturating an actual root lift inside the original Sylow

Let A be an elementary subgroup whose nonzero image lies in the root of
an actual normal PSL₂ component. Conjugate A under the full inverse image
of the root normalizer. The resulting span stays in the prescribed Sylow
and maps onto the entire root, since the root torus acts irreducibly.
If the conjugates commute, this span is an elementary full-root lift and
the existing minimum theorem identifies n(H) with the model exponent.

The original ComponentSeed application constructs this span without an
invariance assumption on A. Failure of its commutativity gives explicit
noncommuting elements in the original Sylow whose commutator lies in
O₂(H). The even-degree outer-image alternative remains separate. Neither
remaining case is excluded here, and this does not assert unconditional
11.3.5 or 11.3.6. All source assembly remains with the parameter-component
owner and its linear-geometry consumer.

Source: Aschbacher--Smith, 11.3.5(1), printed pp.771--772 and E.1.2--6,
pp.210--211; compare the numerical E.2.2 quotient audit in
`docs/quasithin-proof-basis.md`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
variable {X Y : Type*} [Group X] [Group Y] [Finite Y]

/-- The normalizer of the full root preimage, expressed through the original map. -/
def rootLiftNormalizer (q : X →* Y) (J : Subgroup Y) (P : Sylow 2 J) : Subgroup X :=
  (normalizer ((P : Subgroup J).map J.subtype : Set Y)).comap q

/-- The actual conjugate span of the elementary seed under the lifted root normalizer. -/
def rootLiftSpan (q : X →* Y) (J : Subgroup Y) (P : Sylow 2 J)
    (A : Subgroup X) : Subgroup X := conjugateSpanBy A (rootLiftNormalizer q J P)

private theorem linear_root_commutative (J : Subgroup Y) {f : ℕ}
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f)) (P : Sylow 2 J) :
    IsMulCommutative ((P : Subgroup J).map J.subtype) := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : P ≃* P' := (P : Subgroup J).equivMapOfInjective a.toMonoidHom a.injective
  let c := b.trans (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P').symm
  let : IsMulCommutative P := .of_comm fun x y => c.injective (by
    simp only [map_mul,mul_comm])
  exact Subgroup.map_isMulCommutative (H := (P : Subgroup J)) (f := J.subtype)

omit [Finite Y] in
/-- Saturation stays in every subgroup containing the kernel and the full root preimage. -/
theorem rootLiftSpan_le (q : X →* Y) (hq : Function.Surjective q)
    (J : Subgroup Y) (P : Sylow 2 J) (A U : Subgroup X)
    (hk : q.ker ≤ U)
    (hP : (P : Subgroup J).map J.subtype ≤ U.map q)
    (hA : A.map q ≤ (P : Subgroup J).map J.subtype) :
    rootLiftSpan q J P A ≤ U := by
  let B := (P : Subgroup J).map J.subtype
  have hn : rootLiftNormalizer q J P ≤ normalizer (B.comap q : Set X) := by
    change (normalizer (B : Set Y)).comap q ≤ _
    rw [comap_normalizer_eq_of_surjective B hq]
  have he : rootLiftSpan q J P A ≤ B.comap q :=
    conjugateSpanBy_le (map_le_iff_le_comap.mp hA) hn
  have hu := comap_mono (f := q) hP
  rw [comap_map_eq,sup_eq_left.mpr hk] at hu
  exact he.trans hu

/-- A nonzero image saturates to the full binary root, without assuming its lift is elementary. -/
theorem rootLiftSpan_map_eq_root (q : X →* Y) (hq : Function.Surjective q)
    (J : Subgroup Y) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f)) (P : Sylow 2 J)
    (A : Subgroup X) (hA : A.map q ≤ (P : Subgroup J).map J.subtype)
    (hne : ¬ A ≤ q.ker) :
    (rootLiftSpan q J P A).map q = (P : Subgroup J).map J.subtype := by
  let B := (P : Subgroup J).map J.subtype
  have he : (rootLiftSpan q J P A).map q =
      conjugateSpanBy (A.map q) (normalizer (B : Set Y)) := by
    rw [rootLiftSpan,map_conjugateSpanBy,rootLiftNormalizer,
      map_comap_eq_self_of_surjective hq]
  rw [he]
  apply linear_root_image_eq_of_normalizer_invariant J hf hm P
  · exact conjugateSpanBy_le hA le_rfl
  · intro hz
    apply hne
    apply (map_eq_bot_iff A).mp
    exact le_bot_iff.mp ((le_conjugateSpanBy _ _).trans hz.le)
  · exact ((P : Subgroup J).le_normalizer_map J.subtype).trans
      (le_normalizer_conjugateSpanBy _ _)

private theorem span_commutative_of_conjugates (A N : Subgroup X)
    (hc : ∀ x ∈ N, ∀ a ∈ A, ∀ b ∈ A, Commute a (x*b*x⁻¹)) :
    IsMulCommutative (conjugateSpanBy A N) := by
  apply (conjugateSpanBy_commutative_iff A N).mpr
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨x,hx,b,hb,rfl⟩ a ha
  exact (hc x hx a ha b hb).eq

omit [Finite Y] in
/-- Commuting conjugates give an actual elementary subgroup, rather than merely an elementary image. -/
theorem rootLiftSpan_elementary_of_conjugates (q : X →* Y)
    (J : Subgroup Y) (P : Sylow 2 J) (A : Subgroup X)
    [IsElementaryAbelian 2 A]
    (hc : ∀ x ∈ rootLiftNormalizer q J P, ∀ a ∈ A, ∀ b ∈ A,
      Commute a (x*b*x⁻¹)) : IsElementaryAbelian 2 (rootLiftSpan q J P A) := by
  let : IsMulCommutative (conjugateSpanBy A (rootLiftNormalizer q J P)) :=
    span_commutative_of_conjugates A _ hc
  exact conjugateSpanBy_elementary_of_commutative A _

/-- Failure of the elementary saturation produces a nontrivial commutator in the actual kernel. -/
theorem rootLiftSpan_elementary_or_kernel_commutator
    (q : X →* Y) (J : Subgroup Y) {f : ℕ}
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f)) (P : Sylow 2 J)
    (A : Subgroup X) [IsElementaryAbelian 2 A]
    (hA : A.map q ≤ (P : Subgroup J).map J.subtype) :
    IsElementaryAbelian 2 (rootLiftSpan q J P A) ∨
      ∃ x ∈ rootLiftNormalizer q J P, ∃ a ∈ A, ∃ b ∈ A,
        ⁅a,x*b*x⁻¹⁆ ≠ 1 ∧ ⁅a,x*b*x⁻¹⁆ ∈ q.ker := by
  by_cases hc : ∀ x ∈ rootLiftNormalizer q J P, ∀ a ∈ A, ∀ b ∈ A,
      Commute a (x*b*x⁻¹)
  · exact .inl (rootLiftSpan_elementary_of_conjugates q J P A hc)
  · push Not at hc
    obtain ⟨x,hx,a,ha,b,hb,hcomm⟩ := hc
    refine .inr ⟨x,hx,a,ha,b,hb,?_,?_⟩
    · exact fun hh => hcomm (commutatorElement_eq_one_iff_commute.mp hh)
    · let B := (P : Subgroup J).map J.subtype
      let : IsMulCommutative B := linear_root_commutative J hm P
      have hqa : q a ∈ B := hA (mem_map_of_mem q ha)
      have hqb : q b ∈ B := hA (mem_map_of_mem q hb)
      have hqx : q x ∈ normalizer (B : Set Y) := hx
      have hqc : q (x*b*x⁻¹) ∈ B := by
        simpa only [map_mul,map_inv] using (mem_normalizer_iff.mp hqx (q b)).mp hqb
      change q ⁅a,x*b*x⁻¹⁆ = 1
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact setLike_mul_comm hqa hqc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Commuting conjugates under the actual root-preimage normalizer construct
an elementary lift inside the prescribed Sylow. The original subgroup is
retained inside that lift, whose full image then recognizes n(H). -/
theorem ComponentSeed.normal_linear_full_lift_of_commuting_conjugates
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hP : (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype ≤
      (T.subtype h.outside.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))
    (hA : A.map (QuotientGroup.mk' (pCore 2 H)) ≤
      (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype)
    (hne : ¬ A ≤ pCore 2 H)
    (hcomm : ∀ x ∈ Models.rootLiftNormalizer (QuotientGroup.mk' (pCore 2 H))
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) P,
      ∀ a ∈ A, ∀ b ∈ A, Commute a (x*b*x⁻¹)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    let E := Models.rootLiftSpan q J P A
    IsElementaryAbelian 2 E ∧ A ≤ E ∧
      E ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
      E.map q = (P : Subgroup J).map J.subtype ∧
      ChapterE.generationParameter H = f ∧ RankOneReduction S H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let E := Models.rootLiftSpan q J P A
  let := s.quasisimple
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hmJ : ClassicalGroup.IsPSL J 2 (2 ^ f) := hm.of_mulEquiv e.symm
  let : IsElementaryAbelian 2 E :=
    Models.rootLiftSpan_elementary_of_conjugates q J P A hcomm
  have hk : q.ker ≤ (T.subtype h.outside.1.1.2 : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal _
  have he := Models.rootLiftSpan_map_eq_root q (QuotientGroup.mk'_surjective _) J hf hmJ
    P A hA (by simpa only [q,QuotientGroup.ker_mk'] using hne)
  exact ⟨inferInstance,le_conjugateSpanBy A _,
    Models.rootLiftSpan_le q (QuotientGroup.mk'_surjective _) J P A _ hk hP hA,he,
    s.linear_parameter_eq_of_normal_lift h pr hc hs hn hf hm P E he,
    s.rankOneReduction_of_normal_linear_lift h pr hc hs hn hf hm P E he⟩

/-- The noninvariant-image case is reduced to an actual nontrivial
commutator in O₂(H). Both entries lie in the original Sylow: one belongs
to the selected elementary subgroup, the other to one of its conjugates
under the normalizer of the full root preimage. The independent even-field
outer alternative is retained. -/
theorem ComponentSeed.normal_linear_root_commutator_alternative
    (s : ComponentSeed T H K)
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
        Models.rootLiftSpan q J P A ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
        (Models.rootLiftSpan q J P A).map q = (P : Subgroup J).map J.subtype ∧
        ∃ x ∈ Models.rootLiftNormalizer q J P, ∃ a ∈ A, ∃ b ∈ A,
          x*b*x⁻¹ ∈ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
          ⁅a,x*b*x⁻¹⁆ ≠ 1 ∧ ⁅a,x*b*x⁻¹⁆ ∈ pCore 2 H) ∨
      (∃ m : ℕ, 0 < m ∧ f = 2 * m ∧ ChapterE.generationParameter H ≤ m + 1) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let := s.quasisimple
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hmJ : ClassicalGroup.IsPSL J 2 (2 ^ f) := hm.of_mulEquiv e.symm
  obtain ⟨P,A,hA,hAT,hr,hP,hi | ho⟩ :=
    s.exists_large_root_image_or_outer_bound h pr hc hs hn hf hm
  · let := hA
    have hne : ¬ A ≤ q.ker := by
      intro hcore
      have hz : A.map q = ⊥ := (map_eq_bot_iff A).mpr hcore
      rw [hz,Group.rank_eq_zero] at hr
      have hk := degree_le_parameter h pr hc hs
      have hn := S.nonbinary
      omega
    have hk : q.ker ≤ (T.subtype h.outside.1.1.2 : Subgroup H) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal _
    have hP' : (P : Subgroup J).map J.subtype ≤
        (T.subtype h.outside.1.1.2 : Subgroup H).map q := hP.trans_le inf_le_left
    have hspan := Models.rootLiftSpan_le q (QuotientGroup.mk'_surjective _) J P A _ hk hP' hi
    have himage := Models.rootLiftSpan_map_eq_root q (QuotientGroup.mk'_surjective _) J hf hmJ
      P A hi hne
    rcases Models.rootLiftSpan_elementary_or_kernel_commutator q J hmJ P A hi with he | ho
    · let := he
      exact .inl ⟨s.linear_parameter_eq_of_normal_lift h pr hc hs hn hf hm P _ himage,
        s.rankOneReduction_of_normal_linear_lift h pr hc hs hn hf hm P _ himage⟩
    · obtain ⟨x,hx,a,ha,b,hb,hc,hmem⟩ := ho
      exact .inr (.inl ⟨P,A,hA,hAT,hr,hP,hi,hspan,himage,x,hx,a,ha,b,hb,
        hspan (subset_closure ⟨x,hx,b,hb,rfl⟩),hc,by
          simpa only [q,QuotientGroup.ker_mk'] using hmem⟩)
  · exact .inr (.inr ho)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
