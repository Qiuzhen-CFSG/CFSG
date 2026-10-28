module
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Natural
public import Theory.Representation.SL2SylowFixedRecognition.Complementary
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Models

/-!
# Recognition of the literal rank-one pair

The proper normalizer of V O₂(H) separates the images of V and Vʰ. Two
such Sylow subgroups generate the marked SL₂ quotient, which gives K ≤ I.
The action kernel on H is O₂(H): its intersection with the two-residual
and its quotient by that residual are two-groups. This connects the argument
to the actual starred quotient in 11.3.7, with every original map retained.

For a specified surjection I → SL₂ with kernel P, conjugation descends to
SL₂ acting on the elementary group P. The two Sylow fixed spaces are
complementary, so G.1.7 constructs natural coordinates. The Sylow
omega-center proves P is nontrivial. Restriction to K identifies the
quotient by O₂(K), producing a `PairNaturalMarking` for the literal action.
No compatibility with the field coordinates on V is assumed.

Construction of the surjection with kernel P remains with task
qt-d-1222-shadow-common-identification; E.2.10(7) alone does not exclude
its extra central two-factor. Parent qt-d-1222-shadow-common-core retains
discharge of the preceding 11.3.7 inputs and the final source assembly.
The SL₃ block and the application of the field-four obstruction also remain
with the common-identification owner.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
first two paragraphs of printed p.774 and G.1.7, printed pp.329--330.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL2SylowFixedRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

/-- A source-local proper-normalizer argument separates the two Sylow images. -/
theorem seed_core_normalizer_le_M
    (s : Hypothesis1131At D S U₁ H) (hnot : ¬ V ≤ H.pCoreIn 2) :
    H ⊓ normalizer (V ⊔ H.pCoreIn 2 : Subgroup G) ≤ normalizer (L : Set G) := by
  let A := V ⊔ H.pCoreIn 2
  let N := H ⊓ normalizer (A : Set G)
  have hTH : (T : Subgroup G) ≤ H := s.outside.1.1.2
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hh
  have hAT : A ≤ (T : Subgroup G) := sup_le D.le_sylow hQT
  have hTN : (T : Subgroup G) ≤ N := by
    apply le_inf hTH
    apply (le_inf S.sylow_normalizes ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (hTH.trans H.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  apply Chapter3.HStar.proper_overgroup_le T s.outside hTN
  apply lt_of_le_of_ne inf_le_left
  intro he
  have hn : H ≤ normalizer (A : Set G) := he ▸ inf_le_right
  have hAQ : A ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hAT) (hAT.trans hTH) hn
  exact hnot (le_sup_left.trans hAQ)

/-- An element outside M cannot fix the Sylow image of the original V. -/
theorem pair_core_quotient_images_ne
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G)) (hnot : ¬ V ≤ H.pCoreIn 2) :
    (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≠
      ((V.map (MulAut.conj h).toMonoidHom).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)) := by
  intro he
  let q := QuotientGroup.mk' (pCore 2 H)
  have hVI : V ≤ H := D.le_sylow.trans s.outside.1.1.2
  have hWI : V.map (MulAut.conj h).toMonoidHom ≤ H :=
    (show V.map (MulAut.conj h).toMonoidHom ≤ pairGroup V h from le_sup_right).trans
      (pairGroup_le s hh)
  have hpre := congrArg (fun A : Subgroup (H ⧸ pCore 2 H) => (A.comap q).map H.subtype) he
  change (((V.subgroupOf H).map q).comap q).map H.subtype =
    ((((V.map (MulAut.conj h).toMonoidHom).subgroupOf H).map q).comap q).map H.subtype at hpre
  simp only [comap_map_eq,show q.ker = pCore 2 H from QuotientGroup.ker_mk' _,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hVI,map_subgroupOf_eq_of_le hWI] at hpre
  have hQ : (H.pCoreIn 2).map (MulAut.conj h).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      ((H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) hh)
  have hn : h ∈ normalizer (V ⊔ H.pCoreIn 2 : Subgroup G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (V ⊔ H.pCoreIn 2).map (MulAut.conj h).toMonoidHom = _
    rw [Subgroup.map_sup,hQ]
    exact hpre.symm
  exact hm (seed_core_normalizer_le_M s hnot ⟨hh,hn⟩)

/-- Literal projection to H/O₂(H); the residual marking is on its actual image. -/
theorem residual_le_pairGroup_of_sylow_quotient
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G)) (hnot : ¬ V ≤ H.pCoreIn 2)
    (e : ((outsideResidual H).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≃*
      SL(2,S.field.Carrier))
    (R : Sylow 2 (((outsideResidual H).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (hR : (R : Subgroup _).map
        (((outsideResidual H).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype =
      (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    outsideResidual H ≤ pairGroup V h := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let K₀ := ((outsideResidual H).subgroupOf H).map q
  let : ((outsideResidual H).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer (outsideResidual_le H)).mpr (outsideResidual_normalized H)
  let : K₀.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let a : MulAut K₀ := MulAut.conjNormal (q ⟨h,hh⟩)
  let R' := R.mapSurjective (f := a.toMonoidHom) a.surjective
  have hconj : (((V.map (MulAut.conj h).toMonoidHom).subgroupOf H).map q) =
      ((V.subgroupOf H).map q).map (MulAut.conj (q ⟨h,hh⟩)).toMonoidHom := by
    have hs : (V.map (MulAut.conj h).toMonoidHom).subgroupOf H =
        (V.subgroupOf H).map (MulAut.conj (⟨h,hh⟩ : H)).toMonoidHom :=
      (conj_smul_subgroupOf (D.le_sylow.trans s.outside.1.1.2) ⟨h,hh⟩).symm
    rw [hs,map_map,map_map]
    congr 1
  have hR' : (R' : Subgroup K₀).map K₀.subtype =
      ((V.map (MulAut.conj h).toMonoidHom).subgroupOf H).map q := by
    rw [hconj,← hR]
    change ((R : Subgroup K₀).map a.toMonoidHom).map K₀.subtype = _
    rw [map_map,map_map]
    rfl
  have hne : R ≠ R' := by
    intro he
    apply pair_core_quotient_images_ne s hh hm hnot
    rw [← hR,← hR',he]
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q := R'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPQ : P ≠ Q := by
    intro he
    apply hne
    apply Sylow.ext
    exact map_injective e.injective (congrArg Sylow.toSubgroup he)
  have hgen : (R : Subgroup K₀) ⊔ R' = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup,map_top_of_surjective _ e.surjective]
    exact Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 P Q hPQ
  have him : ((pairGroup V h).subgroupOf H).map q = K₀ := by
    have hv : V ≤ H := D.le_sylow.trans s.outside.1.1.2
    have hw : V.map (MulAut.conj h).toMonoidHom ≤ H :=
      (show V.map (MulAut.conj h).toMonoidHom ≤ pairGroup V h from le_sup_right).trans (pairGroup_le s hh)
    change ((V ⊔ V.map (MulAut.conj h).toMonoidHom).subgroupOf H).map q = K₀
    rw [subgroupOf_sup hv hw,Subgroup.map_sup,← hR,← hR',← Subgroup.map_sup,hgen]
    rw [← MonoidHom.range_eq_map,range_subtype]
  apply residual_le_pairGroup_of_cover s hh
  have hc := congrArg (fun A : Subgroup (H ⧸ pCore 2 H) => (A.comap q).map H.subtype) him
  change ((((pairGroup V h).subgroupOf H).map q).comap q).map H.subtype =
    ((((outsideResidual H).subgroupOf H).map q).comap q).map H.subtype at hc
  simp only [comap_map_eq,show q.ker = pCore 2 H from QuotientGroup.ker_mk' _,Subgroup.map_sup,
    map_subgroupOf_eq_of_le (pairGroup_le s hh),
    map_subgroupOf_eq_of_le (outsideResidual_le H)] at hc
  exact (show outsideResidual H ≤ outsideResidual H ⊔ H.pCoreIn 2 from le_sup_left).trans hc.ge




/-- The whole action kernel is the two-core, since its residual kernel and
its quotient by the residual are both two-groups. -/
theorem source_star_denominator_eq_core
    (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    (centralizer (omegaClosure T H : Set G)).subgroupOf H = pCore 2 H := by
  let := source_residualQuotient_simple hmodel
  let K₀ := (outsideResidual H).subgroupOf H
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer (outsideResidual_le H)).mpr
    (outsideResidual_normalized H)
  let e : K₀ ≃* outsideResidual H := subgroupOfEquivOfLe (outsideResidual_le H)
  have hk : ((localAction T H).comp K₀.subtype).ker =
      (residualAction T H).ker.comap e.toMonoidHom := by
    ext x
    rfl
  have hp : IsPGroup 2 ((localAction T H).comp K₀.subtype).ker := by
    rw [hk,residualAction_ker_eq_core T H s.outside.1.1.2 s.moves_omega_center]
    exact pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hgen : K₀ ⊔ (T.subtype s.outside.1.1.2 : Subgroup H) = ⊤ := by
    change (outsideResidual H).subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup (outsideResidual_le H) s.outside.1.1.2,
      outsideResidual_sup_sylow T H s.outside.1.1.2,subgroupOf_self]
  have hpC := (localAction T H).kernel_isPGroup_of_normal_supplement
    K₀ (T.subtype s.outside.1.1.2) (T.subtype s.outside.1.1.2).isPGroup' hgen hp
  rw [← localAction_ker]
  apply le_antisymm
  · exact le_sSup (show (localAction T H).ker ∈
        {N : Subgroup H | N.Normal ∧ IsPGroup 2 N} from ⟨inferInstance,hpC⟩)
  rw [localAction_ker]
  intro x hx
  exact core_centralizes_omegaClosure T H s.outside.1.1.2 (mem_map_of_mem H.subtype hx)

/-- The preceding 11.3.7 model and literal starred Sylow image imply K ≤ I. -/
theorem source_residual_le_pairGroup
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G)) (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H)) :
    outsideResidual H ≤ pairGroup V h := by
  have hd := source_star_denominator_eq_core s hmodel
  obtain ⟨_,e,_⟩ := source_compatible_matrix_equivs s hmodel
  have hi : ∃ (e' : residualStar T H ≃* SL(2,S.field.Carrier))
      (R' : Sylow 2 (residualStar T H)),
      (R' : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (V.subgroupOf H).map (starProjection T H) := ⟨e,R,hR⟩
  have transport (N : Subgroup H) [N.Normal]
      (hN : (centralizer (omegaClosure T H : Set G)).subgroupOf H = N) : ∃
      (e' : ((outsideResidual H).subgroupOf H).map (QuotientGroup.mk' N) ≃*
        SL(2,S.field.Carrier))
      (R' : Sylow 2 (((outsideResidual H).subgroupOf H).map (QuotientGroup.mk' N))),
      (R' : Subgroup _).map
          (((outsideResidual H).subgroupOf H).map (QuotientGroup.mk' N)).subtype =
        (V.subgroupOf H).map (QuotientGroup.mk' N) := by
    subst N
    exact hi
  have hi' := transport (pCore 2 H) hd
  obtain ⟨e',R',hR'⟩ := hi'
  exact residual_le_pairGroup_of_sylow_quotient s hh hm hnot e' R' hR'


/-- The actual pair core contains a nontrivial subgroup of the Sylow omega-center. -/
theorem pairCore_ne_bot (s : Hypothesis1131At D S U₁ H) (h : G) :
    pairCore V H h ≠ ⊥ := by
  have hZQ : omegaCenter T ≤ H.pCoreIn 2 := by
    have hi := map_mono (f := H.subtype) (ParameterComponent.omegaOrbit_reduced s).le_pCore
    rw [map_subgroupOf_eq_of_le (ParameterComponent.omegaOrbit_le s.outside.1.1.2)] at hi
    apply (omegaCenter_le_closure T H).trans
    rw [omegaClosure_eq_omegaOrbit]
    exact hi
  intro he
  apply D.ne_bot
  apply subgroup_eq_bot_of_central_omega_disjoint V D.le_sylow S.sylow_normalizes
  apply bot_unique
  exact (inf_le_inf_left V hZQ).trans ((show axis V H ≤ pairCore V H h from le_sup_left).trans he.le)

/-- A specified projection with kernel P identifies the literal O₂(I). -/
theorem pairCore_eq_twoCore_of_projection
    (hh : h ∈ H)
    (q : pairGroup V h →* SL(2,S.field.Carrier)) (hq : Function.Surjective q)
    (hker : q.ker = (pairCore V H h).subgroupOf (pairGroup V h)) :
    pairCore V H h = (pairGroup V h).pCoreIn 2 := by
  have hp : IsPGroup 2 q.ker := by
    rw [hker]
    exact ((isPGroup_pCoreIn 2 H).to_le (pairCore_le_core hh)).comap_subtype
  have he := q.comap_pCore_of_ker_isPGroup hq hp
  rw [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot,MonoidHom.comap_bot,hker] at he
  have hi := congrArg (Subgroup.map (pairGroup V h).subtype) he
  rwa [map_subgroupOf_eq_of_le (pairCore_le_pairGroup h)] at hi

private theorem pair_projection_residual_surjective
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hk : outsideResidual H ≤ pairGroup V h)
    (q : pairGroup V h →* SL(2,S.field.Carrier)) (hq : Function.Surjective q) :
    Function.Surjective (q.comp (inclusion hk)) := by
  have hfour : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_le_pow_right (n := 2) (by decide) S.nonbinary
  let := SL2SylowFixedRecognition.perfect hfour
  have hp : pResidual 2 SL(2,S.field.Carrier) = ⊤ := by
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hP
    let := hN
    have : Subsingleton (SL(2,S.field.Carrier) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hP.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have him : (outsideResidual H).subgroupOf (pairGroup V h) =
      pResidual 2 (pairGroup V h) := by
    rw [← pairGroup_residual_eq s hh hk]
    change ((pResidual 2 (pairGroup V h)).map (pairGroup V h).subtype).comap
      (pairGroup V h).subtype = _
    exact comap_map_eq_self_of_injective Subtype.val_injective _
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, inclusion_range, him, map_pResidual_of_surjective 2 q hq, hp]

/-- Complementary fixed spaces construct coordinates for the literal P-action.
The projection is an explicit recognition input, not an asserted source conclusion. -/
theorem natural_pair_of_projection
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (q : pairGroup V h →* SL(2,S.field.Carrier)) (hq : Function.Surjective q)
    (hker : q.ker = (pairCore V H h).subgroupOf (pairGroup V h))
    (R Q : Sylow 2 SL(2,S.field.Carrier))
    (hR : (V.subgroupOf (pairGroup V h)).map q = (R : Subgroup SL(2,S.field.Carrier)))
    (hQ : ((V.map (MulAut.conj h).toMonoidHom).subgroupOf (pairGroup V h)).map q =
      (Q : Subgroup SL(2,S.field.Carrier))) :
    Nonempty (PairNaturalMarking V H h S.field) := by
  let P := pairCore V H h
  let I := pairGroup V h
  let K := outsideResidual H
  let := pairCore_elementary s hh (pair_intersection_eq_bot s hf hk)
  let α : I →* MulAut P := P.normalizerMonoidHom.comp
    (inclusion (pairGroup_normalizes_pairCore s hh))
  have hkerα : q.ker ≤ α.ker := by
    intro x hx
    rw [hker] at hx
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (x : G) * (v : G) * (x : G)⁻¹ = (v : G)
    apply mul_inv_eq_iff_eq_mul.mpr
    have he := mem_centralizer_iff.mp (P.le_centralizer hx) v v.property
    exact he.symm
  let β : SL(2,S.field.Carrier) →* MulAut P := q.liftOfSurjective hq ⟨α,hkerα⟩
  have hβ (x : I) (v : P) : (β (q x) v : G) = (x : G) * (v : G) * (x : G)⁻¹ := by
    change ((q.liftOfSurjective hq ⟨α,hkerα⟩) (q x) v : G) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  let ρ := elementaryRepresentation (p := 2) β
  have hfix (A : Subgroup G) (hAI : A ≤ I)
      (R₀ : Subgroup SL(2,S.field.Carrier)) (hA : (A.subgroupOf I).map q = R₀)
      (v : Additive P) :
      v ∈ fixedSpace ρ R₀ ↔ (v.toMul : G) ∈ centralizer (A : Set G) := by
    constructor
    · intro hv a ha
      have hqa : q ⟨a,hAI ha⟩ ∈ R₀ := hA ▸ mem_map_of_mem q ha
      have he := congrArg (fun z : Additive P => (z.toMul : G)) (hv ⟨_,hqa⟩)
      change (β (q ⟨a,hAI ha⟩) v.toMul : G) = (v.toMul : G) at he
      rw [hβ] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hv a
      have ha : a.val ∈ (A.subgroupOf I).map q := hA.symm ▸ a.property
      obtain ⟨x,hx,hxa⟩ := ha
      apply Additive.toMul.injective
      apply Subtype.ext
      change (β (a : SL(2,S.field.Carrier)) v.toMul : G) = (v.toMul : G)
      rw [← hxa]
      rw [hβ]
      exact mul_inv_eq_iff_eq_mul.mpr (hv x hx)
  have hcomp : IsCompl (fixedSpace ρ R) (fixedSpace ρ Q) := by
    refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
    · intro v hvR hvQ
      have hvV := (hfix V le_sup_left R hR v).mp hvR
      have hvW := (hfix _ le_sup_right Q hQ v).mp hvQ
      have hvB : (v.toMul : G) ∈ axis V H := by
        rw [← pairCore_fixed_eq_axis s hf hh hk]
        exact ⟨v.toMul.property,hvV⟩
      have hvK : (v.toMul : G) ∈ centralizer (K : Set G) := by
        have hI : I ≤ centralizer ({(v.toMul : G)} : Set G) := by
          apply sup_le
          · intro a ha
            exact mem_centralizer_singleton_iff.mpr (hvV a ha)
          · intro a ha
            exact mem_centralizer_singleton_iff.mpr (hvW a ha)
        intro a ha
        exact mem_centralizer_singleton_iff.mp (hI (hk ha))
      have hv0 := (seed_residual_fixed_eq_bot s hf).le ⟨hvB.1,hvK⟩
      exact congrArg Additive.ofMul (Subtype.ext hv0)
    · apply top_unique
      intro v _
      obtain ⟨b,hb,c,hc,he⟩ := Set.mem_mul.mp
        ((pairCore_product s hh) ▸ (show (v.toMul : G) ∈ (P : Set G) from v.toMul.property))
      let bP : P := ⟨b,mem_sup_left hb⟩
      let cP : P := ⟨c,mem_sup_right hc⟩
      refine Submodule.mem_sup.mpr ⟨Additive.ofMul bP,?_,Additive.ofMul cP,?_,?_⟩
      · apply (hfix V le_sup_left R hR _).mpr
        let := D.elementary
        exact V.le_centralizer hb.1
      · apply (hfix _ le_sup_right Q hQ _).mpr
        let := D.elementary
        let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj h).toMonoidHom
        exact (V.map (MulAut.conj h).toMonoidHom).le_centralizer (map_mono inf_le_left hc)
      · exact congrArg Additive.ofMul (Subtype.ext he)
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra _ 2
  obtain ⟨m,e,he⟩ := natural_of_complementary_sylow_fixed ρ R Q hcomp
    S.field.degree S.nonbinary S.field.card_eq
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hn
    apply pairCore_ne_bot s h
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hz : e (Additive.ofMul (⟨x,hx⟩ : P)) = 0 := by
      ext i
      exact Fin.elim0 (hm0 ▸ i)
    have hz' := e.injective (hz.trans e.map_zero.symm)
    exact congrArg (fun v : Additive P => (v.toMul : G)) hz'
  let qK := q.comp (inclusion hk)
  have hqK : Function.Surjective qK := pair_projection_residual_surjective s hh hk q hq
  have hqKp : IsPGroup 2 qK.ker := by
    have hhker : qK.ker ≤ P.subgroupOf K := by
      intro x hx
      have hx' : inclusion hk x ∈ q.ker := hx
      rw [hker] at hx'
      exact hx'
    exact ((IsElementaryAbelian.isPGroup 2 P).comap_subtype).to_le hhker
  have hcore : qK.ker = pCore 2 K := by
    have hc := qK.comap_pCore_of_ker_isPGroup hqK hqKp
    rwa [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot,MonoidHom.comap_bot] at hc
  let qbar : (K ⧸ pCore 2 K) →* SL(2,S.field.Carrier) :=
    QuotientGroup.lift _ qK hcore.ge
  have hbar : Function.Bijective qbar := by
    refine ⟨?_,?_⟩
    · apply (MonoidHom.ker_eq_bot_iff qbar).mp
      apply bot_unique
      intro z hz
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
      apply (QuotientGroup.eq_one_iff k).mpr
      exact hcore.le hz
    · intro z
      obtain ⟨k,rfl⟩ := hqK z
      exact ⟨QuotientGroup.mk' _ k,rfl⟩
  let eK := MulEquiv.ofBijective qbar hbar
  let eP : P ≃* Multiplicative (Fin m → Fin 2 → S.field.Carrier) :=
    { toFun v := Multiplicative.ofAdd (e (Additive.ofMul v))
      invFun w := (e.symm w.toAdd).toMul
      left_inv v := congrArg Additive.toMul (e.symm_apply_apply _)
      right_inv w := congrArg Multiplicative.ofAdd (e.apply_symm_apply _)
      map_mul' v w := e.map_add (Additive.ofMul v) (Additive.ofMul w) }
  refine ⟨⟨m,hm,hk.trans (pairGroup_normalizes_pairCore s hh),eK,eP,?_⟩⟩
  intro k v i
  have ha : ρ (qK k) (Additive.ofMul v) =
      Additive.ofMul (pairResidualAction V H h (hk.trans (pairGroup_normalizes_pairCore s hh)) k v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hβ (inclusion hk k) v
  have hh := he (qK k) (Additive.ofMul v) i
  rw [ha] at hh
  exact hh
end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
