module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Assembly
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# Characteristic-normalizer control from the actual A.3.12 embedding

The source containment theorem supplies a component normal in N_G(C), where
C is nontrivial and characteristic in R = O₂(Ξ_p(L)T). The only remaining
classification premise is the A.3.12 embedding of the literal quotient images
of Y = N_L(R)^∞ and this component. The existing case elimination then forces
p = 5 and retains the elementary order-25 kernel and its actual SL₂(5) quotient.
Thompson factorization and the marked parabolic argument give C(G,R) ≤ N_G(L).

`MarkedA312Input` is an unproved earlier-source obligation. This conditional
reduction does not supply it; final canonical-radical assembly must do so.
Source: Aschbacher–Smith, proof of 1.3.8, printed pp.512–513; A.3.12, pp.47–48.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
open Section02 Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The remaining A.3.12 model assertion only for the actual escaping
characteristic normalizers in the proof of 1.3.8. `SourceData` contains the
proved local, relative-normality and radical hypotheses; it contains no
embedding or starred-membership conclusion. -/
@[expose] def MarkedA312Input (p : ℕ) (L : Subgroup G) (T : Sylow 2 G) : Prop :=
  ∀ (C : Subgroup (radicalCore p L T)) (K : Subgroup G),
    FiveCase.SourceData KnownSimple.IsKnownSimple p 5 L T C K →
    A312Embedding
      (FiveCase.quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (FiveCase.quotientImage K
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))

private theorem exists_normal_component_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (p : ℕ) (L : Subgroup G) (T : Sylow 2 G)
    (hL : L ∈ Chapter1.L G T) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hY : ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent)
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let Y := normalizerResidual L (radicalCore p L T)
    ∃ K : Subgroup G, K ∈ cComponentsIn N ∧ Y ≤ K ∧
      (K.subgroupOf N).Normal ∧ (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let R := radicalCore p L T
  let N := normalizer (C.map R.subtype : Set G)
  let Y := normalizerResidual L R
  have hRN : normalizer (R : Set G) ≤ N :=
    normalizer_le_normalizer_characteristic_image R C
  have hTN : (T : Subgroup G) ≤ N := (t_le_normalizer_radicalCore p L T).trans hRN
  have hYN : Y ≤ N := (normalizerResidual_le_normalizer L R).trans hRN
  let S : Sylow 2 N := T.subtype hTN
  have hYL : Y.subgroupOf N ∈ Chapter1.L N S := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (mem_LIn_iff_subgroupOf hTN hYN).mp
      ⟨hYN, Y_mem_L_of_cComponent p hL hY⟩
  have hSY : (S : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hYN]
    exact comap_mono (t_le_normalizer_Y p hTL)
  obtain ⟨K₀, ⟨hK₀, hYK₀, hn⟩, _⟩ :=
    lemma_1_2_4_containment_normality_source
      (characteristic_normalizer_quotient_sqtk hG p L T C hC) S hYL hSY
  have hKm : (K₀.map N.subtype).subgroupOf N = K₀ :=
    comap_map_eq_self_of_injective N.subtype_injective _
  have hnormal : ((K₀.map N.subtype).subgroupOf N).Normal := hKm.symm ▸ hn
  have hNK : N ≤ normalizer (K₀.map N.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K₀)).mp hnormal
  refine ⟨K₀.map N.subtype, ⟨map_subtype_le _, hKm.symm ▸ hK₀⟩,
    ?_, hnormal, hTN.trans hNK⟩
  simpa only [map_subgroupOf_eq_of_le hYN] using map_mono (f := N.subtype) hYK₀

private theorem exists_marked_five_component_of_marked_input
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (L : Subgroup G) (T : Sylow 2 G)
    (hL : L ∈ LStar G T) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → L ⊔ T ≤ M →
      M = normalizer (L : Set G))
    (hX : XiMember T (XiP p L))
    (hcore : (XiP p L).pCoreIn 2 ≠ ⊥)
    (hshape : XiOddQuotient p (XiQuotient (XiP p L)))
    (hfit : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hnil : A36Nilpotent (XiQuotient L))
    (hrmodel : IsSL (fittingQuotient L) 2 5)
    (hsecond : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hY : ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hYq : ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T))))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (hLC : normalizerResidual L (C.map (radicalCore p L T).subtype) ∈ Chapter1.L G T)
    (hcomm : ⁅normalizerResidual L (C.map (radicalCore p L T).subtype),
      normalizerResidual L (radicalCore p L T)⁆ =
        normalizerResidual L (C.map (radicalCore p L T).subtype))
    (hMarked : MarkedA312Input p L T)
    (hescape : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
      normalizer (L : Set G)) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let Y := normalizerResidual L (radicalCore p L T)
    let LC := normalizerResidual L (C.map (radicalCore p L T).subtype)
    normalizer (L : Set G) = normalizer (XiP p L : Set G) ∧
    ∃ K : Subgroup G, K ∈ cComponentsIn N ∧ Y ≤ K ∧
      (K.subgroupOf N).Normal ∧ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LC ≤ K ∧ ¬ ((XiP p L).subgroupOf K).Normal ∧
      ¬ XiP p L ≤ (solvableRadical K).map K.subtype ∧ Y < K ∧
      CaseTen (quotientImage Y N) (quotientImage K N) 5 ∧
      p = 5 ∧
      Nonempty (XiQuotient K ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5)) ∧
      Y = LC ∧
      (∀ q : ℕ, q.Prime → Odd q →
        (q ∣ Nat.card (fittingSubgroup (XiQuotient LC)) ↔ q = 5)) ∧
      ∀ P : Sylow p (XiP p L),
        let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
        MarkedFiveExtension (quotientImage Y K) (quotientImage P₀ K) ∧
        MarkedFiveExtension (quotientImage Y N) (quotientImage P₀ N) ∧
        ∀ (U : Subgroup (quotientImage Y N)) [U.Normal],
          ElementaryModel 5 2 U →
          (quotientImage Y N ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) →
          (quotientImage P₀ N).subgroupOf (quotientImage Y N) = U := by
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hM := normalizer_eq_of_LT_uniqueness p L T hTL hcore hunique
  obtain ⟨K, hK, hYK, hn, hTK⟩ :=
    exists_normal_component_source hG p L T hL.1 hTL hY C hC
  obtain ⟨hXn, hXrad, hstrict⟩ :=
    escaping_component_rigidity hG hA36 hp3 L T hX hshape C hC K hK hn hTK
      hXY hYK hM hescape
  have hYL := Y_mem_L_of_cComponent p hL.1 hY
  have hdata : SourceData KnownSimple.IsKnownSimple p 5 L T C K :=
    { ambient := hG
      prime := hp
      large := hp3
      prime_r := by decide
      maximal := hL
      invariant := hTL
      xi := hX
      xi_shape := hshape
      fitting_prime := hfit
      nilpotent := hnil
      quotient_r := hrmodel
      second_prime := hsecond
      characteristic := inferInstance
      nontrivial := hC
      normalizers := hM
      escape := hescape
      contains_xi := hXY
      local_Y := hYL
      nonsimple_Y := hYq
      local_LC := hLC
      commutator := hcomm
      component := hK
      contains_Y := hYK
      normal := hn
      nonnormal_xi := hXn
      radical_exclusion := hXrad }
  obtain ⟨s, hs, _, hs3, hsmall, hlarge⟩ :=
    Alternatives.exists_case_ten hG hA36 p hp ho L T C hC K hK hstrict hYL
      hXY hYq hXrad (hMarked C K hdata)
  have hcase : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s :=
    ⟨hs, hs3, hsmall, hlarge⟩
  obtain ⟨hp5, hs5, _, hmodel, heq, hsupport, hmark⟩ :=
    hdata.caseTen_deduction hA36 hcase
  subst s
  refine ⟨hM, K, hK, hYK, hn, hTK,
    residual_le_component L _ K C hK.1 hn hYK hcomm,
    hXn, hXrad, hstrict, hcase, hp5, hmodel, heq, hsupport, ?_⟩
  intro P
  refine ⟨hmark P, ?_, ?_⟩
  · exact (markedFiveExtension_componentQuotient_iff hYK
      ((map_subtype_le _).trans (hXY.trans hYK)) hK.1 hK.2).mp (hmark P)
  · intro U hU hmodel e
    exact hdata.caseTen_sylow_image_eq_kernel hcase P U hmodel e

/-- Characteristic-normalizer control using only the marked embeddings of the actual source pairs. -/
theorem characteristicNormalizerClosure_le_of_marked_A312
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    (hA38q : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B)
    (hB216 : ThompsonSource.TheoremB216.{u})
    (T : Sylow 2 G)
    (h127 : ∀ K ∈ LStar G (T : Subgroup G),
      IsMaximalTwoLocal (normalizer (componentOrbit K (T : Subgroup G) : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K (T : Subgroup G) : Set G))
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hMarked : MarkedA312Input p L T) :
    characteristicNormalizerClosure (radicalCore p L T) ≤ normalizer (L : Set G) := by
  classical
  have hQall : ∀ K ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK KnownSimple.IsKnownSimple ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)) := by
    intro K hK
    exact uniqueness_local_quotient_sqtk hG hK.2.2
  have hQ := hQall L hL.1
  have hTL := radicalLocal_invariant_of_A38 hA38q hL.1 hQ hn
  have hunique := (radical_normalizer_maximal_of_127 h127 hL hTL).2
  by_cases hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) → q = p
  · exact (radical_singlePrime_normalizers_of_source hA36 hA38q h127 hL hQ hn hp hd hs).2
  push Not at hs
  obtain ⟨q, hq, hqo, hqd, hqp⟩ := hs
  let _ : Fact q.Prime := ⟨hq⟩
  have hnil := nilpotent_of_two_fitting_primes hA36 hL.1 hQ hn Fact.out hq hqp hd hqd
  have hfive : IsSL (fittingQuotient L) 2 5 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hnil.2.2.1
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hnil.1).symm.trans e⟩⟩
  obtain ⟨hp3, hshape⟩ := XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn hp hd
  have hq3 : 3 < q := (XiP_oddQuotient_of_A36 (p := q) hA36 hL.1 hQ hn hqo hqd).1
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hqo
    omega
  have hX : XiMember T (XiP p L) :=
    lemma_1_3_3 hA36 hA38q hQall ⟨L, hL.1, hn, p, Fact.out, hp, hd, rfl⟩
  have hlocal := lemma_1_1_4_6 T (hG.evenCharacteristic T)
  have hcore := XiP_pCoreIn_ne_bot (Fact.out : p.Prime) hL.1 hTL hshape
    (fun _ hM _ hne hNM hsub => lemma_1_1_3_1 hM hne hNM hsub) hlocal
  have hres := residual_normalizer_data_of_source hA36 hA38q hL hQ hn hp hd
  have hsecond : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) := ⟨q, hq, hqo, hqp, hqd⟩
  have escape (C : Subgroup (radicalCore p L T)) (hchar : C.Characteristic)
      (hne : C ≠ ⊥)
      (he : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
        normalizer (L : Set G)) := by
    let _ := hchar
    have hc := hres.characteristic_local C hchar hne
    exact exists_marked_five_component_of_marked_input hG hA36
      p Fact.out hp3 L T hL hTL hunique hX hcore hshape hd hnil hfive
      hsecond hres.Y_cComponent hres.X_le_Y hres.Y_not_quasisimple C hne hc.1 hc.2.2 hMarked he
  obtain ⟨C₀, _, hC₀, hchar₀, _, _, _, hpC₀, hqC₀⟩ :=
    exists_thompsonChoice_fittingPrimes_of_B216 hB216 p q hp hqo hq5 L T
      hL.1 hTL hlocal hd hqd hres.X_le_Y (hres.actions q hq hqo hqd).2
      (hres.actions q hq hqo hqd).1
  let _ : C₀.Characteristic := hchar₀
  have hC₀M : normalizer (C₀.map (radicalCore p L T).subtype : Set G) ≤
      normalizer (L : Set G) := by
    by_contra he
    obtain ⟨_, K, _, _, _, _, _, _, _, _, _, _, _, _, hsupport, _⟩ :=
      escape C₀ hchar₀ hC₀ he
    have hp5 := (hsupport p Fact.out hp).mp hpC₀
    have hq5 := (hsupport q hq hqo).mp hqC₀
    exact hqp (hq5.trans hp5.symm)
  have hRM : normalizer (radicalCore p L T : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_normalizer_characteristic_image _ C₀).trans hC₀M
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hchar hne
  let _ := hchar
  by_contra he
  obtain ⟨hM, K, hK, hYK, hKn, hTK, _, hXn, _, _, _, _,
      ⟨emodel⟩, _, _, hmarked⟩ := escape C hchar hne he
  let P : Sylow p (XiP p L) := Classical.arbitrary _
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  have hRcore : radicalCore p L T ≤ (K ⊔ radicalCore p L T).pCoreIn 2 :=
    radical_le_join_core_of_marked_five K (radicalCore p L T) _
      (normalizerResidual L (radicalCore p L T)) P₀ hK hKn
      ((radicalCore p L T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ C))
      (radicalCore_isTwoGroup p L T) hYK ((map_subtype_le _).trans hres.X_le_Y)
      ((map_subtype_le _).trans (le_sup_left.trans (join_le_normalizer_radicalCore p L T)))
      emodel (hmarked P).1
  have heq : radicalCore p L T = (K ⊔ radicalCore p L T).pCoreIn 2 :=
    le_antisymm hRcore (twoCore_join_le_radicalCore p L K T hTK (hres.X_le_Y.trans hYK))
  have hKR : K ≤ normalizer (radicalCore p L T : Set G) := by
    rw [heq]
    exact le_sup_left.trans ((K ⊔ radicalCore p L T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  apply hXn
  exact normal_subgroupOf_of_le_normalizer ((hKR.trans hRM).trans
    (normalizer_le_normalizer_XiP p L))

end CFSG.Quasithin.Chapter1.RadicalNormalizers
