module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RootSpan
public import Theory.GroupTheory.TIElementaryOrbit
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner

/-!
# Full root lifting from the original TI module

For the normal PSL₂ component, the normalizer of the root preimage is
proper and contains the prescribed Sylow. The original H*-minimality
therefore places it inside N_G(L), where the source TI property of V
applies. Intersect V with the root preimage. This intersection and each
of its normalizer conjugates are normal in that same preimage; the TI
property makes them commute. Their actual span is elementary abelian.

The full root is self-centralizing in the faithful almost-simple image:
an automorphism fixing the Sylow pointwise is inner by that Sylow. Since
T normalizes the original V, its image cannot meet the root trivially
unless its entire image is trivial. Thus V escaping O₂(H) constructs a
full elementary root lift and identifies the literal field exponent
with the actual generationParameter H, without a parity or inner-image
assumption. The source application returns that lift inside the original
Sylow and feeds it to the existing RankOneReduction assembly.

The final unconditional alternative leaves exactly V ≤ O₂(H) in this
normal model row. Source 11.3.3 only puts its weak closure outside O₂(H),
so that remaining branch still needs an argument with actual conjugates
of V. Other model/FF exclusions and paired/doubled assembly also remain;
this module does not assert unconditional 11.3.5 or 11.3.6.

Source: Aschbacher--Smith, 11.0.3(4), 11.3.3--5, printed pp.759--760,
771--772; the pointwise PSL₂ Sylow-fixer calculation is cited in
Theory/SpecificGroups/PSL2/SylowPointwiseInner.lean. The numerical E.2.2
quotient audit in docs/quasithin-proof-basis.md remains in force.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
variable {Y : Type*} [Group Y] [Finite Y]

/-- The normalizer of the actual binary root is proper, even in an ambient overgroup. -/
theorem linear_root_normalizer_ne_top (J : Subgroup Y) {f : ℕ}
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f)) (P : Sylow 2 J) :
    normalizer ((P : Subgroup J).map J.subtype : Set Y) ≠ ⊤ := by
  intro hn
  let : ((P : Subgroup J).map J.subtype).Normal := normalizer_eq_top_iff.mp hn
  have hPN : (P : Subgroup J).Normal := by
    have hh : (((P : Subgroup J).map J.subtype).comap J.subtype).Normal := inferInstance
    simpa only [comap_map_eq_self_of_injective J.subtype_injective] using hh
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hn' : (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).Normal :=
    Subgroup.Normal.map hPN a.toMonoidHom a.surjective
  exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 P' hn'

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The normalizer of the full root preimage lies in the original N_G(L), by H*-minimality. -/
theorem ComponentSeed.rootLiftNormalizer_le_original_normalizer
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal) {f : ℕ}
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (hP : (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
      ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
          (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    (Models.rootLiftNormalizer (QuotientGroup.mk' (pCore 2 H))
      ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) P).map H.subtype ≤
        normalizer (L : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let U := (T.subtype h.outside.1.1.2 : Subgroup H)
  let B := (P : Subgroup J).map J.subtype
  let N := Models.rootLiftNormalizer q J P
  let := hn
  let : J.Normal := Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
  let := s.quasisimple
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hmJ : ClassicalGroup.IsPSL J 2 (2 ^ f) := hm.of_mulEquiv e.symm
  have hN : N ≠ ⊤ := by
    intro he
    have hh := congrArg (map q) he
    change ((normalizer (B : Set _)).comap q).map q = (⊤ : Subgroup H).map q at hh
    rw [map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _),map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact Models.linear_root_normalizer_ne_top J hmJ P hh
  have hUN : U ≤ N := by
    apply map_le_iff_le_comap.mp
    change U.map q ≤ normalizer (B : Set _)
    rw [show B = U.map q ⊓ J from hP]
    exact (le_inf (U.map q).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  apply Chapter3.HStar.proper_overgroup_le T h.outside
  · have hh := map_mono (f := H.subtype) hUN
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ N.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le h.outside.1.1.2] at hh
  · apply lt_of_le_of_ne (map_subtype_le N)
    intro he
    apply hN
    apply map_injective H.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact he

/-- Relative normality and the original TI property make the root-intersection orbit elementary. -/
theorem ComponentSeed.original_root_intersection_span_elementary
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (pr : Preceding1133 D S U₁ H)
    (hn : (K.subgroupOf H).Normal) {f : ℕ}
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (hP : (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
      ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
          (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    let R := ((P : Subgroup J).map J.subtype).comap q
    IsElementaryAbelian 2 (Models.rootLiftSpan q J P ((V.subgroupOf H) ⊓ R)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let U := (T.subtype h.outside.1.1.2 : Subgroup H)
  let B := (P : Subgroup J).map J.subtype
  let R := B.comap q
  let N := Models.rootLiftNormalizer q J P
  let W := V.subgroupOf H
  let A := W ⊓ R
  have hNM := s.rootLiftNormalizer_le_original_normalizer h hn hm P hP
  have hRU : R ≤ U := by
    have hh := comap_mono (f := q) (hP.trans_le inf_le_left)
    have hk : q.ker ≤ U := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal _
    rwa [comap_map_eq,sup_eq_left.mpr hk] at hh
  have hNR : N ≤ normalizer (R : Set H) := by
    change (normalizer (B : Set _)).comap q ≤ _
    rw [comap_normalizer_eq_of_surjective B (QuotientGroup.mk'_surjective _)]
  have hUW : U ≤ normalizer (W : Set H) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro w
    exact (mem_normalizer_iff.mp (S.sylow_normalizes hx)) w
  have hRA : R ≤ normalizer (A : Set H) :=
    (le_inf (hRU.trans hUW) R.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hVH : V ≤ H := D.le_sylow.trans h.outside.1.1.2
  have hW : W.map H.subtype = V := map_subgroupOf_eq_of_le hVH
  let := D.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hTI : ∀ x ∈ N, W.map (MulAut.conj x).toMonoidHom = W ∨
      Disjoint W (W.map (MulAut.conj x).toMonoidHom) := by
    intro x hx
    have he : (W.map (MulAut.conj x).toMonoidHom).map H.subtype =
        V.map (MulAut.conj (x : G)).toMonoidHom := by
      rw [map_map,show H.subtype.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x : G)).toMonoidHom.comp H.subtype from rfl,←map_map,hW]
    rcases pr.ti x (hNM (mem_map_of_mem H.subtype hx)) with hz | hv
    · right
      apply disjoint_def.mpr
      intro y hy hyx
      have hyx' : (y : G) ∈ V.map (MulAut.conj (x : G)).toMonoidHom :=
        he ▸ mem_map_of_mem H.subtype hyx
      exact Subtype.ext (mem_bot.mp (hz ▸ (show (y : G) ∈ V ⊓
        V.map (MulAut.conj (x : G)).toMonoidHom from ⟨hy,hyx'⟩)))
    · left
      apply map_injective H.subtype_injective
      rw [he,hW,hv]
  have hh := elementary_orbit_of_relative_ti (p := 2) A W R N
    inf_le_left inf_le_right hRA hNR hTI
  change IsElementaryAbelian 2 (conjugateSpanBy A N)
  rw [conjugateSpanBy_eq_iSup_conj]
  exact hh

/-- A nonzero original root intersection constructs a full elementary lift and recognizes n(H). -/
theorem ComponentSeed.full_root_lift_of_original_root_escape
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (hP : (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
      ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
          (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    (hescape : ¬ (V.subgroupOf H ⊓
        ((P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
          ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype).comap
            (QuotientGroup.mk' (pCore 2 H))) ≤ pCore 2 H) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    let A := V.subgroupOf H ⊓ ((P : Subgroup J).map J.subtype).comap q
    let E := Models.rootLiftSpan q J P A
    IsElementaryAbelian 2 E ∧ A ≤ E ∧
      E ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
      E.map q = (P : Subgroup J).map J.subtype ∧
      ChapterE.generationParameter H = f ∧ RankOneReduction S H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let A := V.subgroupOf H ⊓ ((P : Subgroup J).map J.subtype).comap q
  let E := Models.rootLiftSpan q J P A
  let : IsElementaryAbelian 2 E :=
    s.original_root_intersection_span_elementary h pr hn hm P hP
  let := s.quasisimple
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hmJ : ClassicalGroup.IsPSL J 2 (2 ^ f) := hm.of_mulEquiv e.symm
  have hA : A.map q ≤ (P : Subgroup J).map J.subtype :=
    map_le_iff_le_comap.mpr inf_le_right
  have he := Models.rootLiftSpan_map_eq_root q (QuotientGroup.mk'_surjective _) J hf hmJ
    P A hA (by simpa only [q,QuotientGroup.ker_mk'] using hescape)
  have hk : q.ker ≤ (T.subtype h.outside.1.1.2 : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal _
  exact ⟨inferInstance,le_conjugateSpanBy A _,
    Models.rootLiftSpan_le q (QuotientGroup.mk'_surjective _) J P A _ hk
      (hP.trans_le inf_le_left) hA,he,
    s.linear_parameter_eq_of_normal_lift h pr hc hs hn hf hm P E he,
    s.rankOneReduction_of_normal_linear_lift h pr hc hs hn hf hm P E he⟩

/-- The normal source row is recognized unless the original root intersection lies in O₂(H). -/
theorem ComponentSeed.normal_linear_recognition_or_original_root_core
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    ∃ P : Sylow 2 J,
      (P : Subgroup J).map J.subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map q ⊓ J ∧
      ((ChapterE.generationParameter H = f ∧ RankOneReduction S H) ∨
        V.subgroupOf H ⊓ ((P : Subgroup J).map J.subtype).comap q ≤ pCore 2 H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let U := (T.subtype h.outside.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let : (K.subgroupOf H).Normal := hn
  let : J.Normal := Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := U.exists_sylow_map_eq_inf_of_normal J
  refine ⟨P,hP,?_⟩
  by_cases hcore : V.subgroupOf H ⊓ ((P : Subgroup J).map J.subtype).comap q ≤ pCore 2 H
  · exact .inr hcore
  · have hh := s.full_root_lift_of_original_root_escape h pr hc hs hn hf hm P hP hcore
    exact .inl hh.2.2.2.2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent


namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
variable {Y : Type*} [Group Y] [Finite Y]

/-- The full root is self-centralizing in a faithful ambient extension of binary PSL₂. -/
theorem linear_root_centralizer_le (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) {f : ℕ}
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f)) (P : Sylow 2 J) :
    centralizer ((P : Subgroup J).map J.subtype : Set Y) ≤
      (P : Subgroup J).map J.subtype := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let ρ := Theory.GroupAction.ModelConjugation.action ⊤ J le_normalizer_of_normal e
  have hρ : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    rw [Theory.GroupAction.ModelConjugation.action_ker,hC,bot_subgroupOf]
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  intro y hy
  have hfix : ∀ x ∈ P', ρ ⟨y,mem_top _⟩ x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e ((J.normalizerMonoidHom ⟨y,le_normalizer_of_normal (mem_top y)⟩)
      (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change y*x*y⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (hy x (mem_map_of_mem J.subtype hx)).symm
  obtain ⟨g,hg,he⟩ := Theory.PSL2.aut_fixing_sylow_inner P' (ρ ⟨y,mem_top _⟩) hfix
  obtain ⟨x,hx,rfl⟩ := hg
  have hxact := Theory.GroupAction.ModelConjugation.action_conj ⊤ J
    le_normalizer_of_normal e x (mem_top _)
  have heq : y = (x : Y) := congrArg Subtype.val (hρ (he.trans hxact.symm))
  exact heq.symm ▸ mem_map_of_mem J.subtype hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

private theorem ComponentSeed.linear_image_self_centralizing
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    let J := (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    ClassicalGroup.IsPSL J 2 (2 ^ f) ∧ centralizer (J : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let B := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := B.map q
  let U := (T.subtype h.outside.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let : B.Normal := hn
  let : J.Normal := Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
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
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hgen : J ⊔ (U : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change B.map q ⊔ (T.subtype h.outside.1.1.2 : Subgroup H).map q = ⊤
    rw [←Subgroup.map_sup,s.intrinsic_supplement h.outside.1.1.2,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact ⟨hmJ,centralizer_eq_bot_of_simple_two_quotient J
    (Group.IsPerfect.not_isMulCommutative J)
    (isPGroup_quotient_of_sup_eq_top J (U : Subgroup (H ⧸ pCore 2 H)) U.isPGroup' hgen)
    (pCore_quotient_pCore_eq_bot 2)⟩

/-- The original Sylow-normal V meets the root nontrivially modulo O₂(H) whenever it escapes that core. -/
theorem ComponentSeed.original_le_core_of_root_intersection_le_core
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (hP : (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
      ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
          (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    (hcore : V.subgroupOf H ⊓
        ((P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
          ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype).comap
            (QuotientGroup.mk' (pCore 2 H)) ≤ pCore 2 H) :
    V ≤ H.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let U := (T.subtype h.outside.1.1.2 : Subgroup H)
  let B := (P : Subgroup J).map J.subtype
  let W := V.subgroupOf H
  let : J.Normal := Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
  obtain ⟨hmJ,hC⟩ := s.linear_image_self_centralizing h hn hf hm
  have hBcentral := Models.linear_root_centralizer_le J hC hmJ P
  have hWU : W ≤ U := fun x hx => D.le_sylow hx
  have hUW : U ≤ normalizer (W : Set H) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro w
    exact (mem_normalizer_iff.mp (S.sylow_normalizes hx)) w
  have hUB : U.map q ≤ normalizer (B : Set _) := by
    rw [show B = U.map q ⊓ J from hP]
    exact (le_inf (U.map q).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hBW : B ≤ normalizer (W.map q : Set _) :=
    (hP.trans_le inf_le_left).trans ((map_mono hUW).trans (W.le_normalizer_map q))
  have hWB : W.map q ≤ normalizer (B : Set _) := (map_mono hWU).trans hUB
  have hz : W.map q ⊓ B = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨⟨w,hw,rfl⟩,hb⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hcore ⟨hw,hb⟩)
  have hc : ⁅W.map q,B⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans _ hz.le
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hBW)
      (le_normalizer_iff_commutator_le_right.mp hWB)
  have hle : W.map q ≤ B := (commutator_eq_bot_iff_le_centralizer.mp hc).trans hBcentral
  have hWzero : W.map q = ⊥ := by
    rw [←inf_eq_left.mpr hle]
    exact hz
  have hWcore : W ≤ pCore 2 H := by
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp hWzero
  have hh := map_mono (f := H.subtype) hWcore
  change (V.subgroupOf H).map H.subtype ≤ _ at hh
  rwa [map_subgroupOf_eq_of_le (D.le_sylow.trans h.outside.1.1.2)] at hh

/-- The actual normal PSL₂ source row is recognized unless the original V lies in O₂(H). -/
theorem ComponentSeed.normal_linear_recognition_or_original_core
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    (ChapterE.generationParameter H = f ∧ RankOneReduction S H) ∨ V ≤ H.pCoreIn 2 := by
  obtain ⟨P,hP,hrec | hcore⟩ :=
    s.normal_linear_recognition_or_original_root_core h pr hc hs hn hf hm
  · exact .inl hrec
  · exact .inr (s.original_le_core_of_root_intersection_le_core h hn hf hm P hP hcore)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- If the original V escapes O₂(H), construct a full elementary root lift
in the prescribed Sylow and recognize the literal PSL₂ model at n(H).
This uses the original relative TI and normality hypotheses, with no root
invariance, commutativity, inner-image or field-parity premise. -/
theorem ComponentSeed.full_root_lift_of_original_not_le_core
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (hV : ¬ V ≤ H.pCoreIn 2) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    ∃ (P : Sylow 2 J) (E : Subgroup H), IsElementaryAbelian 2 E ∧
      E ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧
      (P : Subgroup J).map J.subtype =
        (T.subtype h.outside.1.1.2 : Subgroup H).map q ⊓ J ∧
      E.map q = (P : Subgroup J).map J.subtype ∧
      ChapterE.generationParameter H = f ∧ RankOneReduction S H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let U := (T.subtype h.outside.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let : J.Normal := Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := U.exists_sylow_map_eq_inf_of_normal J
  have hescape : ¬ V.subgroupOf H ⊓ ((P : Subgroup J).map J.subtype).comap q ≤ pCore 2 H :=
    fun he => hV (s.original_le_core_of_root_intersection_le_core h hn hf hm P hP he)
  have hh := s.full_root_lift_of_original_root_escape h pr hc hs hn hf hm P hP hescape
  exact ⟨P,_,hh.1,hh.2.2.1,hP,hh.2.2.2⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
