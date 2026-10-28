module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.CanonicalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Source
public import Theory.SpecificGroups.SL2.PointStabilizerLifts

/-!
# Both radical conclusions for the original chosen flag

In the surviving odd-extension case, the actual two-odd quotient is SL₂(p).
Its order-two center and Grün's lemma exclude central Fitting subgroups
after passage through O₂(K). The canonical A.3.6 action calculation therefore
applies without a noncentrality, kernel, or prime-action premise.

The local action overgroup is KR₁X, contained in the original point
normalizer. Its two-core quotient retains the literal seed and component.
Intersecting the resulting bound with KR₁ and using O₂(KR₁) = O₂(KT)
returns the original commutator. In particular, X need not normalize T.
The equality and prime PSL₂ branches then give both conclusions of 11.4.1(3).
The final application combines them with the established triangle exclusion
to give the full (2–3) output on the unchanged chosen geometry.

The registered earlier geometry and source implications retain their final
discharge with qt-d-1222-shadow-components and
qt-d-1222-natural-shadow-reduction. They supply relative component normality,
point centralization, seed containment, X-normalization of V₁ and R₁,
central-omega placement, the complete 11.1.2 alternatives, the exact 3.2.5
and 7.0.1 recognition inputs, Proposition1132At and the G₂ weak-closure
clauses of 11.2.2. No triangle-placement or action premise remains.
The independent Fitting-index calculation remains conditional and is not
needed for this source output; its existing APIs are preserved.
Source: Aschbacher–Smith, A.3.6, pp.43–45, and 11.4.1(2–3), pp.775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical

private theorem noncentral_fitting_of_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hn : ¬ fittingSubgroup A ≤ center A) : ¬ fittingSubgroup B ≤ center B := by
  intro hz
  apply hn
  intro x hx
  have he : e x ∈ center B := hz (by
    rw [← map_fitting_equiv e]
    exact mem_map_of_mem e.toMonoidHom hx)
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul] using mem_center_iff.mp he (e y)

/-- The odd SL₂ quotient forces noncentral Fitting: a perfect central quotient is centerless. -/
theorem noncentral_fitting_of_odd_sl2_quotient
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    {κ : GroupClass} (hs : IsSQTK κ Q) (hO : pCore 2 Q = ⊥)
    (hQ : (⊤ : Subgroup Q).IsCComponent) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : Source.IsSL (Q ⧸ pPrimeCore 2 Q) 2 p) :
    ¬ fittingSubgroup Q ≤ center Q := by
  intro hz
  have hfit := intrinsic_fitting_eq_oddCore hs hO hQ hp hm
  have hFZ : fittingSubgroup Q = center Q :=
    le_antisymm hz (le_sSup ⟨inferInstance,inferInstance⟩)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let a := (QuotientGroup.quotientMulEquivOfEq (hFZ.symm.trans hfit)).trans e
  have ho : Odd (Nat.card F) := hF ▸ (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hc : Nat.card (center (Q ⧸ center Q)) = 2 :=
    (Nat.card_congr (centerCongr a).toEquiv).trans
      (Matrix.SpecialLinearGroup.center_rank_two_card (GorensteinWalter.two_ne_zero_of_odd_card F ho))
  rw [Group.IsPerfect.center_quotient_center_eq_bot,card_bot] at hc
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The original point-local SQTK hypotheses discharge the noncentrality premise. -/
theorem ofFlag_quotient_fitting_noncentral_of_sl2
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K : Subgroup G) (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    ¬ fittingSubgroup (K ⧸ pCore 2 K) ≤ center (K ⧸ pCore 2 K) := by
  have hs := S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)
  have hKs := (IsSQTK.equiv (subgroupOfEquivOfLe hK.1)).mp
    (hs.subgroup (K.subgroupOf (normalizer (f.Vi 0 : Set G))))
  let Q := K ⧸ pCore 2 K
  have hQs : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hKs.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hKs.stronglyQuasithin r hr ho)
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 K)
  let : Group.IsPerfect K := relative_component_perfect hK
  exact noncentral_fitting_of_odd_sl2_quotient hQs (pCore_quotient_pCore_eq_bot 2) hQ hp hm

/-- Apply the canonical odd-core actions in KR₁X and return the bound to the original O₂(KT). -/
theorem ofFlag_commutator_le_core_of_noncentral_quotient
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hn : ¬ fittingSubgroup (K ⧸ pCore 2 K) ≤ center (K ⧸ pCore 2 K)) :
    ⁅(ofFlag S f X z H).R₁,X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let N := normalizer (f.Vi 0 : Set G)
  let R := (ofFlag S f X z H).R₁
  let J := (K ⊔ R) ⊔ X
  have hNK : N ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := (f.invariant 0).trans hNK
  have hRT : R ≤ T := by
    change (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (f.Li 0 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hKJ : K ≤ J := le_sup_left.trans le_sup_left
  have hRJ : R ≤ J := le_sup_right.trans le_sup_left
  have hXJ : X ≤ J := le_sup_right
  have hAJ : f.Li 0 ≤ J := hAK.trans hKJ
  have hJN : J ≤ N := sup_le (sup_le hK.1.1 (hRT.trans (f.invariant 0))) hX
  let B := K.subgroupOf J
  let A := (f.Li 0).subgroupOf J
  let U := R.subgroupOf J
  let Y := X.subgroupOf J
  let : B.Normal := normal_subgroupOf_of_le_normalizer (hJN.trans hNK)
  have hnormal : ((K ⊔ R).subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (K ⊔ R).le_normalizer
      ((le_inf (hX.trans hNK) hXR).trans (normalizer_inf_normalizer_le_normalizer_sup K R)))
  let : (B ⊔ U).Normal := by
    change (K.subgroupOf J ⊔ R.subgroupOf J).Normal
    rw [← subgroupOf_sup hKJ hRJ]
    exact hnormal
  let : Group.IsPerfect (f.Li 0) := LocalGeometry.localResidual_perfect _
  let eA : A ≃* f.Li 0 := subgroupOfEquivOfLe hAJ
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := eA.symm.toMonoidHom) eA.symm.surjective
  have hA : ¬ Group.IsSolvable A := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable (Triangle.Reselection.flag_residual_mem_local D S f 0)
      (Group.isSolvable_of_surjective (f := eA.toMonoidHom) eA.surjective)
  have hY : Y ≤ normalizer (U : Set J) := by
    rw [← subgroupOf_normalizer_eq hRJ]
    exact comap_mono hXR
  have hc : ⁅U,A⁆ ≤ A.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hRJ,map_subgroupOf_eq_of_le hAJ,
      map_pCoreIn_of_injective 2 A J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hAJ]
    exact local_core_seed_commutator T (f.Li 0) (f.sylow_normalizes_Li 0)
  let eB : B ≃* K := subgroupOfEquivOfLe hKJ
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  have hnB : ¬ fittingSubgroup (B ⧸ pCore 2 B) ≤ center (B ⧸ pCore 2 B) :=
    noncentral_fitting_of_equiv eQ.symm hn
  have hsN := S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)
  have hsJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJN)).mp (hsN.subgroup (J.subgroupOf N))
  have hh := commutator_le_core_of_noncentral_component hsJ A B U Y
    (hK.1.2.subgroupOf_of_le hKJ hJN) hnB (comap_mono hAK) hA
    (isPGroup_pCoreIn 2 _).comap_subtype hY hc
  have hm := map_mono (f := J.subtype) hh
  rw [map_commutator,map_subgroupOf_eq_of_le hRJ,map_subgroupOf_eq_of_le hXJ] at hm
  have hCR : ⁅R,X⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hXR
  have hbound : ⁅R,X⁆ ≤ (K ⊔ R).pCoreIn 2 :=
    (le_inf (hCR.trans le_sup_right) hm).trans (inf_pCoreIn_le_of_le 2 le_sup_left)
  have he : (K ⊔ R).pCoreIn 2 = (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
    core_join_radical_eq T (f.Li 0) K hAK hTK
  exact hbound.trans_eq he

/-- The surviving odd-extension branch has no remaining action or Fitting-index premise. -/
theorem ofFlag_commutator_le_core_of_twoOdd_sl2
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    ⁅(ofFlag S f X z H).R₁,X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
  ofFlag_commutator_le_core_of_noncentral_quotient S f X z H K hK hAK hX hXR
    (ofFlag_quotient_fitting_noncentral_of_sl2 S f K hK.1 hp hm)

/-- Both original radical bounds in every surviving branch, with the original R₁ and X. -/
theorem ofFlag_surviving_bounds
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKC : K ≤ centralizer (f.Vi 0 : Set G)) (hAK : f.Li 0 ≤ K)
    (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree) :
    (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z H).R₁,X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hNK : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have hTK := (f.invariant 0).trans hNK
  have hKC' : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K :=
    ⟨⟨hKC,hK.1.2.subgroupOf_of_le hKC (Subgroup.centralizer_le_normalizer _)⟩,
      (normal_subgroupOf_iff_le_normalizer hKC).mpr ((Subgroup.centralizer_le_normalizer _).trans hNK)⟩
  have hA : f.Li 0 ≠ ⊥ := by
    intro he
    apply (Triangle.Reselection.flag_residual_mem_local D S f 0).1.ne_bot
    rw [he]
    exact bot_subgroupOf _
  refine ⟨ofFlag_surviving_radical_containment S f X z H K hKC' hA hAK hTK hcase,?_⟩
  cases hcase with
  | equal he => exact (ofFlag_equality_bounds S f X z H K he hXR).2
  | sl2Prime hi hn p hp hm =>
      have hprime : p.Prime ∧ 3 < p := by
        rcases hp with rfl | ⟨hp,hl⟩
        · exact ⟨by decide,by decide⟩
        · exact ⟨hp,by omega⟩
      let : Fact p.Prime := ⟨hprime.1⟩
      exact ofFlag_commutator_le_core_of_twoOdd_sl2 S f X z H K hK hAK hX hXR hprime.2 hm
  | psl2Prime hi hn p hp hlarge hm hL =>
      let : Fact p.Prime := ⟨hp⟩
      exact (ofFlag_psl_bounds S f X z H K hKC' hA hAK hTK (hX.trans hNK) hXR (by omega) hm).2

open LocalGeometry Triangle.Reselection

/-- Source 11.4.1(2–3) on the unchanged flag, conditional only on the registered preceding inputs. -/
theorem ofFlag_refinement_and_bounds_of_preceding_sources
    {L V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (K X : Subgroup G) (z : G) (H : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKC : K ≤ centralizer (f.Vi 0 : Set G)) (hAK : f.Li 0 ≤ K)
    (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h325 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      D_J.Source325Alternatives)
    (h1132 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) H,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) H →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) H)
    (h1122 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree) :
    Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree ∧
      (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z H).R₁,X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hc := (ofFlag_refinement_and_radical_of_preceding_sources D S f K X z H
    hK hKC hAK hKZ h701 h325 h1132 h1122 href).1
  exact ⟨hc,ofFlag_surviving_bounds S f X z H K hK hKC hAK hX hXR hc⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
