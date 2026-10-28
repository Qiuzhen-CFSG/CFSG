module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RootSpanTI

/-!
# Actual source conjugates in the normal binary rank-one row

On the prescribed Sylow, C_H(V_H) and O₂(H) cut out the same kernel.
Thus the actual offender A = V^g supplied by 11.3.3 has image rank at
least s(G,V) in H/O₂(H), as well as in the source action quotient H*.
This image has order greater than two. The cyclic outer quotient of a
self-centralizing normal binary PSL₂ component forces its intersection
with the component, and hence with the prescribed root, to be nonzero.

Saturating that actual root intersection under the full root-preimage
normalizer constructs a subgroup of the original Sylow mapping onto the
whole root. If it is elementary, the established minimum obstruction
recognizes the component at generationParameter H. Otherwise there are
explicit noncommuting elements from A and A^x, for the same x in
H ∩ N_G(L), with nontrivial commutator in O₂(H). Combining with RootSpanTI
retains V ≤ O₂(H) and g outside N_G(V) in this remaining alternative.
There is no separate outer-image or even-field alternative.

The noncommuting alternative is not excluded here: it is not asserted
that A or its root intersection is normal in the Sylow. Its exclusion,
the remaining model/FF sieve and paired/doubled assembly stay with the
parameter-component owner. The earlier §§11.0–11.2 inputs retain their
producer qt-d-1222-natural-local-geometry, with final source discharge by
qt-d-1222-shadow-linear-geometry. No unconditional 11.3.5–6 is asserted.

Source: Aschbacher–Smith, 11.3.3–5, printed pp.771–772; E.3.6/8,
pp.232–233; the binary outer calculation is cited in
Theory/SpecificGroups/PSL2/BinaryOuterGeometry.lean. The numerical E.2.2
quotient warning in docs/quasithin-proof-basis.md remains in force.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- On the prescribed Sylow, the source action kills exactly the original two-core. -/
theorem sylow_inf_orbit_centralizer_eq_core
    (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    (T : Subgroup G) ⊓ centralizer (omegaOrbit T H : Set G) = H.pCoreIn 2 := by
  apply le_antisymm (sylow_inf_orbit_centralizer_le_core h hw)
  refine le_inf ?_ ?_
  · have hh := pCoreIn_le_sylow H (T.subtype h.outside.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le h.outside.1.1.2] at hh
  · rintro _ ⟨x,hx,rfl⟩ w hw
    have hc := le_centralizer_iff.mp (omegaOrbit_reduced h).le_centralizer_pCore hx
    exact congrArg H.subtype (hc ⟨w,omegaOrbit_le h.outside.1.1.2 hw⟩ hw)

/-- Every subgroup in T has the same actual kernel in H* and H/O₂(H). -/
theorem sylow_actor_kernel_eq_core
    (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2)
    (A : Subgroup G) (hAT : A ≤ T) :
    A.subgroupOf H ⊓ centralizer ((omegaOrbit T H).subgroupOf H : Set H) =
      A.subgroupOf H ⊓ pCore 2 H := by
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    refine ⟨hx,?_⟩
    have hh : (x : G) ∈ H.pCoreIn 2 :=
      (sylow_inf_orbit_centralizer_eq_core h hw).le ⟨hAT hx,fun w hw =>
        congrArg H.subtype (hc ⟨w,omegaOrbit_le h.outside.1.1.2 hw⟩ hw)⟩
    obtain ⟨y,hy,he⟩ := hh
    exact (Subtype.ext he : y = x) ▸ hy
  · rintro ⟨hx,hq⟩
    exact ⟨hx,le_centralizer_iff.mp (omegaOrbit_reduced h).le_centralizer_pCore hq⟩

/-- The source conjugate has logarithmic image rank at least s(G,V), also modulo O₂(H). -/
theorem active_conjugate_core_image_rank
    (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaOrbit T H : Set G)) :
    letI := D.elementary
    (ChapterE.globalS V).toNat ≤ Nat.log 2 (Nat.card
      (((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))) := by
  let := D.elementary
  let := omegaOrbit_elementary h
  have hr := active_conjugate_rank h g hg ha
  let e := quotientImageEquivOfInfEq
    ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H)
    (centralizer ((omegaOrbit T H).subgroupOf H : Set H)) (pCore 2 H)
    (sylow_actor_kernel_eq_core h hw _ hg)
  change (ChapterE.globalS V).toNat ≤ Nat.log 2 (Nat.card (actorImage T H
    (V.map (MulAut.conj g).toMonoidHom))) at hr
  exact hr.trans_eq (congrArg (Nat.log 2) (Nat.card_congr e.toEquiv))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
variable {Y : Type*} [Group Y] [Finite Y]

/-- An elementary actor of order greater than two meets the self-centralizing binary component. -/
theorem linear_elementary_intersection_ne_bot (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f))
    (A : Subgroup Y) [IsElementaryAbelian 2 A] (hA : 2 < Nat.card A) :
    A ⊓ J ≠ ⊥ := by
  intro hz
  by_cases hAJ : A ≤ J
  · have hzero : A = ⊥ := (inf_eq_left.mpr hAJ).symm.trans hz
    rw [hzero,card_bot] at hA
    omega
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    let a : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card] using
        hF.trans (GaloisField.card 2 f (by omega)).symm)
    let b := e.trans (Atlas.fieldEquivPSL 2 a)
    obtain ⟨_,_,_,_,hbound⟩ :=
      Theory.PSL2.BinaryOuterGeometry.outer_elementary_card_bound J b hC hf A hAJ
    exact (Nat.not_le_of_gt hA) (hbound hz)

/-- The root intersection of a source-sized elementary image is nonzero, without an inner-image hypothesis. -/
theorem linear_root_intersection_ne_bot (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL J 2 (2 ^ f)) (U A : Subgroup Y)
    [IsElementaryAbelian 2 A] (hAU : A ≤ U) (hA : 2 < Nat.card A)
    (P : Sylow 2 J) (hP : (P : Subgroup J).map J.subtype = U ⊓ J) :
    A ⊓ (P : Subgroup J).map J.subtype ≠ ⊥ := by
  rw [hP,←inf_assoc,inf_eq_left.mpr hAU]
  exact linear_elementary_intersection_ne_bot J hC hf hm A hA

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

private theorem ComponentSeed.source_root_model
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

/-- An actual source conjugate has a nonzero root intersection whose saturation covers the full root.
Neither normalization of that conjugate by T nor containment of its whole image in the component is assumed. -/
theorem ComponentSeed.exists_source_root_span
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    letI := D.elementary
    letI := omegaOrbit_elementary h
    let q := QuotientGroup.mk' (pCore 2 H)
    let J := (K.subgroupOf H).map q
    ∃ (g : G) (P : Sylow 2 J),
      let A := V.map (MulAut.conj g).toMonoidHom
      let B := (P : Subgroup J).map J.subtype
      let C := A.subgroupOf H ⊓ B.comap q
      let E := Models.rootLiftSpan q J P C
      A ≤ T ∧ actorImage T H A ∈
        ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS V).toNat ∧
      (ChapterE.globalS V).toNat ≤ Nat.log 2 (Nat.card ((A.subgroupOf H).map q)) ∧
      B = (T.subtype h.outside.1.1.2 : Subgroup H).map q ⊓ J ∧
      ¬ C ≤ pCore 2 H ∧ C ≤ E ∧
      E ≤ (T.subtype h.outside.1.1.2 : Subgroup H) ∧ E.map q = B ∧
      (Models.rootLiftNormalizer q J P).map H.subtype ≤ normalizer (L : Set G) := by
  let := D.elementary
  let := omegaOrbit_elementary h
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  let U := (T.subtype h.outside.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let : J.Normal := Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective _)
  obtain ⟨hmJ,hJ⟩ := s.source_root_model h hn hf hm
  obtain ⟨P,hP⟩ := U.exists_sylow_map_eq_inf_of_normal J
  obtain ⟨g,hg,ha⟩ := exists_active_conjugate h pr hc
  let A := V.map (MulAut.conj g).toMonoidHom
  let W := A.subgroupOf H
  let B := (P : Subgroup J).map J.subtype
  let C := W ⊓ B.comap q
  let E := Models.rootLiftSpan q J P C
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
    (hg.trans h.outside.1.1.2)
  let : IsElementaryAbelian 2 (W.map q) := IsElementaryAbelian.map q
  have hr := active_conjugate_core_image_rank h
    (weakClosure_not_le_core_of_counterexample h pr hc) g hg ha
  have hnS : S.field.degree ≤ (ChapterE.globalS V).toNat := by
    apply ENat.natCast_le_natCast.mp
    rw [ENat.natCast_toNat (ChapterE.globalS_ne_top V)]
    exact hs
  have hcard : 2 < Nat.card (W.map q) := by
    by_contra hh
    have hlog : Nat.log 2 (Nat.card (W.map q)) ≤ 1 :=
      (Nat.log_mono_right (Nat.le_of_not_gt hh)).trans (by decide)
    have hnon := S.nonbinary
    change (ChapterE.globalS V).toNat ≤ Nat.log 2 (Nat.card (W.map q)) at hr
    omega
  have hWU : W ≤ (T.subtype h.outside.1.1.2 : Subgroup H) := fun x hx => hg hx
  have hnon := Models.linear_root_intersection_ne_bot J hJ hf hmJ
    (U : Subgroup (H ⧸ pCore 2 H)) (W.map q) (map_mono hWU) hcard P hP
  have hC : C.map q ≤ B := map_le_iff_le_comap.mpr inf_le_right
  have hescape : ¬ C ≤ pCore 2 H := by
    intro he
    apply hnon
    apply le_bot_iff.mp
    rintro _ ⟨⟨a,ha,rfl⟩,hb⟩
    exact (QuotientGroup.eq_one_iff _).mpr (he ⟨ha,hb⟩)
  have hk : q.ker ≤ (T.subtype h.outside.1.1.2 : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal _
  refine ⟨g,P,hg,active_conjugate_fixedSpaceFamily h g hg ha,hr,hP,hescape,
    le_conjugateSpanBy C _,
    Models.rootLiftSpan_le q (QuotientGroup.mk'_surjective _) J P C _ hk
      (hP.trans_le inf_le_left) hC,
    Models.rootLiftSpan_map_eq_root q (QuotientGroup.mk'_surjective _) J hf hmJ
      P C hC (by simpa only [q,QuotientGroup.ker_mk'] using hescape),
    s.rootLiftNormalizer_le_original_normalizer h hn hm P hP⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Recognition at the actual minimum, or a nontrivial core commutator between actual source conjugates.
The latter alternative retains V ≤ O₂(H), the same offender A = V^g, and a conjugator in H ∩ N_G(L).
There is no independent outer-image alternative. -/
theorem ComponentSeed.normal_linear_recognition_or_source_commutator
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    letI := D.elementary
    letI := omegaOrbit_elementary h
    (ChapterE.generationParameter H = f ∧ RankOneReduction S H) ∨
      (V ≤ H.pCoreIn 2 ∧ ∃ g : G,
        let A := V.map (MulAut.conj g).toMonoidHom
        A ≤ T ∧ g ∉ normalizer (V : Set G) ∧
        actorImage T H A ∈
          ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS V).toNat ∧
        ∃ x ∈ H ⊓ normalizer (L : Set G), ∃ a ∈ A, ∃ b ∈ A,
          x*b*x⁻¹ ∈ (T : Subgroup G) ∧ ⁅a,x*b*x⁻¹⁆ ≠ 1 ∧
            ⁅a,x*b*x⁻¹⁆ ∈ H.pCoreIn 2) := by
  let := D.elementary
  let := omegaOrbit_elementary h
  rcases s.normal_linear_recognition_or_original_core h pr hc hs hn hf hm with hrec | hV
  · exact .inl hrec
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (K.subgroupOf H).map q
  obtain ⟨g,P,hg,hfamily,_,hP,hescape,hCE,hET,himage,hNM⟩ :=
    s.exists_source_root_span h pr hc hs hn hf hm
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := (P : Subgroup J).map J.subtype
  let C := A.subgroupOf H ⊓ B.comap q
  let E := Models.rootLiftSpan q J P C
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf (hg.trans h.outside.1.1.2)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le
    (show C ≤ A.subgroupOf H from inf_le_left)
  obtain ⟨hmJ,_⟩ := s.source_root_model h hn hf hm
  have hC : C.map q ≤ B := map_le_iff_le_comap.mpr inf_le_right
  rcases Models.rootLiftSpan_elementary_or_kernel_commutator q J hmJ P C hC with he | ho
  · let := he
    exact .inl ⟨s.linear_parameter_eq_of_normal_lift h pr hc hs hn hf hm P E himage,
      s.rankOneReduction_of_normal_linear_lift h pr hc hs hn hf hm P E himage⟩
  · have hgN : g ∉ normalizer (V : Set G) := by
      intro hgn
      have he : A = V := mem_normalizer_iff_map_conj_eq.mp hgn
      apply hescape
      intro a ha
      obtain ⟨v,hv,heq⟩ := hV (he.le (show (a : G) ∈ A from ha.1))
      exact (Subtype.ext heq : v = a) ▸ hv
    obtain ⟨x,hx,a,ha,b,hb,hcomm,hmem⟩ := ho
    refine .inr ⟨hV,g,hg,hgN,hfamily,x,
      ⟨x.property,hNM (mem_map_of_mem H.subtype hx)⟩,a,ha.1,b,hb.1,
      hET (subset_closure ⟨x,hx,b,hb,rfl⟩),?_,?_⟩
    · exact fun heq => hcomm (Subtype.ext heq)
    · exact mem_map_of_mem H.subtype
        (show ⁅a,x*b*x⁻¹⁆ ∈ pCore 2 H from by
          simpa only [q,QuotientGroup.ker_mk'] using hmem)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
