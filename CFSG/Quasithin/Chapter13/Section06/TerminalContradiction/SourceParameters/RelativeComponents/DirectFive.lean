module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.RelativeComponents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Generators
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The direct A₅ component exclusion in 13.6.26(1)

For the actual relative C-component K of H, retain Y = ⟨Kᵀ⟩. The earlier
A.3.8 orbit implication makes Y normal in H, and K makes Y perfect. The
actual A₅ quotient of L gives a conjugation action of N_G(L) on five letters.
The perfect image of Y is either trivial or A₅. In the latter case the
commutators with T ∩ L force L ≤ H. In the former case L normalizes Y,
since Y is the two-residual of Y O₂(L). Characteristic two supplies the
nontrivial core of Y, and uniqueness over LT gives a contradiction in both
cases. Every normalizer, action and span is the original source object.

This is a specialization of the argument of 13.3.8 to the perfect span
needed by 13.6.26(1). It requires neither the full earlier 13.3.8 implication
nor universal 13.3.2 normality: the marked A₅ setup already supplies the
actual quotient and unique maximal two-local overgroup. The genuine A.3.8
input remains with its existing producer and final source assembly. The
separate 13.6.26(2) residual consumer retains Earlier1338Two unchanged.

Source: Aschbacher–Smith, 13.3.8 and 13.6.26(1), printed pp.886–887, 934.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup Theory.GroupTheory
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]

private abbrev A5 := alternatingGroup (Fin 5)
private abbrev S5 := Equiv.Perm (Fin 5)
private def autFive : S5 ≃* MulAut A5 :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

private def fiveActor (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* A5) :
    normalizer (L : Set G) →* S5 :=
  autFive.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom))

omit [Finite G] in
private theorem fiveActor_on_L (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* A5) (l : L) :
    fiveActor L e ⟨l.val, L.le_normalizer l.property⟩ =
      (e (QuotientGroup.mk' (pCore 2 L) l)).val := by
  have hq : quotientAut (pCore 2 L)
      (L.normalizerMonoidHom ⟨l.val, L.le_normalizer l.property⟩) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (l * a * l⁻¹) = _
    simp only [map_mul, map_inv, MulAut.conj_apply]
  apply autFive.injective
  change autFive (autFive.symm ((MulAut.congr e)
    (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom ⟨l.val, L.le_normalizer l.property⟩)))) = _
  rw [autFive.apply_symm_apply, hq]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change (e ((QuotientGroup.mk' (pCore 2 L) l) * e.symm a *
    (QuotientGroup.mk' (pCore 2 L) l)⁻¹)).val = _
  simp only [map_mul, map_inv, e.apply_symm_apply]
  rfl

omit [Finite G] in
private theorem fiveActor_trivial_commutator (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* A5) (n : normalizer (L : Set G))
    (hn : fiveActor L e n = 1) (l : L) : ⁅n.val, l.val⁆ ∈ L.pCoreIn 2 := by
  have ha : quotientAut (pCore 2 L) (L.normalizerMonoidHom n) = 1 := by
    apply (MulAut.congr e).injective
    apply autFive.symm.injective
    simpa only [fiveActor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_one] using hn
  have he := congrArg (fun a : MulAut (L ⧸ pCore 2 L) =>
    a (QuotientGroup.mk' (pCore 2 L) l)) ha
  rw [quotientAut_apply_mk] at he
  have hk : L.normalizerMonoidHom n l * l⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom n l * l⁻¹) = 1
    rw [map_mul, map_inv, he]
    exact mul_inv_cancel _
  exact mem_map.mpr ⟨_, hk, rfl⟩

private theorem perfect_five_image (B : Subgroup S5) [Group.IsPerfect B] :
    B = ⊥ ∨ B = alternatingGroup (Fin 5) := by
  have hBA : B ≤ alternatingGroup (Fin 5) :=
    le_of_isPerfect_of_index_eq_two B _ alternatingGroup.index_eq_two
  let C := B.subgroupOf (alternatingGroup (Fin 5))
  let e := subgroupOfEquivOfLe hBA
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  by_cases hC : C = ⊤
  · right
    have h := congrArg (map (alternatingGroup (Fin 5)).subtype) hC
    simpa only [C, map_subgroupOf_eq_of_le hBA, ← MonoidHom.range_eq_map,
      range_subtype] using h
  · left
    let : Group.IsSolvable C := alternatingGroup.isSolvable_subgroup_five_of_ne_top C hC
    have hbot : C = ⊥ := by
      by_contra h
      let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot _).mpr h
      exact Group.IsPerfect.not_isSolvable C inferInstance
    have h := congrArg (map (alternatingGroup (Fin 5)).subtype) hbot
    simpa only [C, map_subgroupOf_eq_of_le hBA, Subgroup.map_bot] using h

private theorem five_commutator (A : Subgroup S5)
    (hA : A ≤ alternatingGroup (Fin 5)) (hne : A ≠ ⊥) :
    ⁅alternatingGroup (Fin 5), A⁆ = alternatingGroup (Fin 5) := by
  let B := A.subgroupOf (alternatingGroup (Fin 5))
  have hB : B ≠ ⊥ := by
    intro h
    have hm := congrArg (map (alternatingGroup (Fin 5)).subtype) h
    simp only [B, map_subgroupOf_eq_of_le hA, Subgroup.map_bot] at hm
    exact hne hm
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  let D := ⁅(⊤ : Subgroup A5), B⁆
  let : D.Normal := normalizer_eq_top_iff.mp
    (top_unique (normalizer_commutator_ge_left ⊤ B))
  have hD : D = ⊤ := by
    rcases (inferInstance : D.Normal).eq_bot_or_eq_top with h | h
    · have hb := (commutator_top_left_eq_bot_iff_le_center (H := B)).mp h
      rw [alternatingGroup.center_eq_bot (by simp)] at hb
      exact (hB (bot_unique hb)).elim
    · exact h
  have hm := congrArg (map (alternatingGroup (Fin 5)).subtype) hD
  simpa only [D, B, map_commutator, map_subgroupOf_eq_of_le hA,
    ← MonoidHom.range_eq_map, range_subtype] using hm

private theorem sylow_meets_five_quotient (T : Sylow 2 G) (L : Subgroup G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* A5) :
    ∃ t : L, t.val ∈ (T : Subgroup G) ∧ e (QuotientGroup.mk' (pCore 2 L) t) ≠ 1 := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let S := T.subtype hTN
  let : D.Normal := (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  let f : D →* A5 := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).comp
    (subgroupOfEquivOfLe L.le_normalizer).toMonoidHom
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe L.le_normalizer).surjective)
  have hcard : 2 ∣ Nat.card A5 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hn : (P : Subgroup D).map f ≠ ⊥ := by
    simpa only [Sylow.coe_mapSurjective] using (P.mapSurjective hf).ne_bot_of_dvd_card hcard
  by_contra h
  push Not at h
  apply hn
  apply bot_unique
  rintro _ ⟨x, hx, rfl⟩
  change f x = 1
  apply h ((subgroupOfEquivOfLe L.le_normalizer) x)
  rw [hP] at hx
  exact hx

omit [Finite G] in
private theorem core_le_sylow_of_normalized (T : Sylow 2 G) (L : Subgroup G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G)) : L.pCoreIn 2 ≤ (T : Subgroup G) := by
  let N := normalizer (L : Set G)
  have hQN : L.pCoreIn 2 ≤ N := (map_subtype_le _).trans L.le_normalizer
  have hNQ : N ≤ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hQQ : L.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) hQN hNQ
  have hNT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow N (T.subtype hTN)
    rw [Sylow.coe_subtype] at hc
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hc hx
    exact ht
  exact hQQ.trans hNT

private theorem normalizer_le_from_unique
    (T : Sylow 2 G) (L M : Subgroup G)
    (hu : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {M})
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G)) :
    normalizer (Q : Set G) ≤ M := by
  obtain ⟨N, hNN, hmax⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (Q : Set G)) from ⟨Q, hne, hQ, rfl⟩)
  have hm : N ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) :=
    ⟨hmax, hN.trans hNN⟩
  have he : N = M := Set.mem_singleton_iff.mp (hu ▸ hm)
  exact hNN.trans_eq he

private theorem not_contains_L_from_unique
    (T : Sylow 2 G) (L M H : Subgroup G)
    (hu : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) : ¬ L ≤ H := by
  intro hLH
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  exact hH.2 (hn.trans (normalizer_le_from_unique T L M hu _
    (isPGroup_pCoreIn 2 H) hH.1.1 ((sup_le hLH hH.1.2).trans hn)))

omit [Finite G] in
private theorem normal_perfect_kernel_normalized
    (T : Sylow 2 G) (L H Y : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hQ : L.pCoreIn 2 ≤ (T : Subgroup G)) (hp : IsPPerfect 2 Y)
    (hc : ⁅Y, L⁆ ≤ L.pCoreIn 2) : L ≤ normalizer (Y : Set G) := by
  let Q := L.pCoreIn 2
  let B := Y ⊔ Q
  have hLQ : L ≤ normalizer (Q : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLB : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    have hm : B.map (MulAut.conj l).toMonoidHom ≤ B := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have hc' : ⁅l, y⁆ ∈ Q := by
          rw [commutator_comm] at hc
          exact hc (commutator_mem_commutator hl hy)
        have hh := B.mul_mem (mem_sup_right hc') (mem_sup_left hy)
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one,
          MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hh
      · rintro _ ⟨q, hq, rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hLQ hl) q).mp hq)
    exact hm (mem_map_of_mem _ hx)
  let : (Y.subgroupOf B).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le Y.le_normalizer ((hQ.trans hTH).trans hHY))
  have hp' : IsPPerfect 2 (Y.subgroupOf B) :=
    hp.of_surjective (subgroupOfEquivOfLe (show Y ≤ B from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y ≤ B from le_sup_left)).symm.surjective
  have hs : Y.subgroupOf B ⊔ Q.subgroupOf B = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ B from le_sup_left) (show Q ≤ B from le_sup_right)]
    exact subgroupOf_self B
  have he : (pResidual 2 B).map B.subtype = Y := by
    rw [pResidual_eq_of_isPPerfect_sup (Y.subgroupOf B) (Q.subgroupOf B)
      hp' (isPGroup_pCoreIn 2 L).comap_subtype hs,
      map_subgroupOf_eq_of_le (show Y ≤ B from le_sup_left)]
  rw [← he]
  exact hLB.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))

/-- The original A₅ quotient and unique maximal two-local exclude any
nontrivial perfect normal span contained in the marked normalizer. -/
theorem perfect_normal_span_excluded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (L M H Y : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hM : M = normalizer (L : Set G))
    (hu : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    [Group.IsPerfect Y] (hp : IsPPerfect 2 Y) (hYne : Y ≠ ⊥) (hYM : Y ≤ M) : False := by
  let N := normalizer (L : Set G)
  let θ := fiveActor L e
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans
    (show L ⊔ (T : Subgroup G) ≤ M from
      (show M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) from
        hu.symm ▸ Set.mem_singleton M).2)
  have hTN : (T : Subgroup G) ≤ N := hTM.trans_eq hM
  have hYN : Y ≤ N := hYM.trans_eq hM
  have hQT := core_le_sylow_of_normalized T L hTN
  let Yn := Y.subgroupOf N
  let Ln := L.subgroupOf N
  let A := ((T : Subgroup G).subgroupOf N) ⊓ Ln
  let : Group.IsPerfect Yn := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hYN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hYN).symm.surjective
  let : Group.IsPerfect (Yn.map θ) := Group.IsPerfect.map θ
  rcases perfect_five_image (Yn.map θ) with hzero | hfull
  · have hc : ⁅Y, L⁆ ≤ L.pCoreIn 2 := by
      apply commutator_le.mpr
      intro y hy l hl
      apply fiveActor_trivial_commutator L e ⟨y, hYN hy⟩ _ ⟨l, hl⟩
      have hm : θ ⟨y, hYN hy⟩ ∈ Yn.map θ := mem_map_of_mem θ hy
      rw [hzero] at hm
      exact hm
    have hLY := normal_perfect_kernel_normalized T L H Y hH.1.2 hHY hQT hp hc
    have hHe : H ∈ Chapter1.He G :=
      Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1
    have hYNH : (Y.subgroupOf H).Normal :=
      (normal_subgroupOf_iff_le_normalizer hYH).mpr hHY
    have hYe : Y ∈ Chapter1.He G :=
      Chapter1.lemma_1_1_3_1 hHe hYne hYH hYNH.isSubnormal
    have hcore : Y.pCoreIn 2 ≠ ⊥ := by
      intro hz
      change Y ⊓ centralizer (Y.pCoreIn 2 : Set G) ≤ Y.pCoreIn 2 at hYe
      have hc : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
      rw [hz, hc, inf_top_eq] at hYe
      exact hYne (bot_unique hYe)
    have hNC : normalizer (Y : Set G) ≤ normalizer (Y.pCoreIn 2 : Set G) :=
      normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
    exact hH.2 ((hHY.trans hNC).trans (normalizer_le_from_unique T L M hu _
      (isPGroup_pCoreIn 2 Y) hcore
      ((sup_le hLY (hH.1.2.trans hHY)).trans hNC)))
  · have hAalt : A.map θ ≤ alternatingGroup (Fin 5) := by
      rintro _ ⟨a, ha, rfl⟩
      have he := fiveActor_on_L L e (⟨a.val, ha.2⟩ : L)
      change θ a ∈ alternatingGroup (Fin 5)
      rw [he]
      exact (e (QuotientGroup.mk' (pCore 2 L) ⟨a.val, ha.2⟩)).property
    have hAne : A.map θ ≠ ⊥ := by
      obtain ⟨t, ht, hne⟩ := sylow_meets_five_quotient T L hTN e
      intro hz
      have hm : θ ⟨t.val, L.le_normalizer t.property⟩ ∈ A.map θ :=
        mem_map_of_mem θ ⟨ht, t.property⟩
      rw [hz] at hm
      have he := fiveActor_on_L L e t
      have hz' : (e (QuotientGroup.mk' (pCore 2 L) t)).val = 1 := he.symm.trans hm
      exact hne (Subtype.ext hz')
    let D := ⁅Yn, A⁆
    have hDmap : D.map θ = alternatingGroup (Fin 5) := by
      rw [map_commutator, hfull]
      exact five_commutator (A.map θ) hAalt hAne
    have hDY : D ≤ Yn := by
      apply commutator_le.mpr
      intro y hy a ha
      change ⁅y.val, a.val⁆ ∈ Y
      exact (le_normalizer_iff_commutator_le_left.mp
        (hH.1.2.trans hHY)) (commutator_mem_commutator hy ha.1)
    let : Ln.Normal := (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
    have hDL : D ≤ Ln :=
      (commutator_mono le_rfl inf_le_right).trans (commutator_le_right Yn Ln)
    apply not_contains_L_from_unique T L M H hu hH
    intro l hl
    let ln : N := ⟨l, L.le_normalizer hl⟩
    have hlmap : θ ln ∈ D.map θ := by
      rw [hDmap]
      rw [fiveActor_on_L L e ⟨l, hl⟩]
      exact (e (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩)).property
    obtain ⟨d, hd, he⟩ := hlmap
    let dl : L := ⟨d.val, hDL hd⟩
    have hq : QuotientGroup.mk' (pCore 2 L) dl =
        QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩ := by
      apply e.injective
      apply Subtype.ext
      exact (fiveActor_on_L L e dl).symm.trans
        (he.trans (fiveActor_on_L L e ⟨l, hl⟩))
    have hker : dl⁻¹ * (⟨l, hl⟩ : L) ∈ pCore 2 L := QuotientGroup.eq.mp hq
    have hqH : (dl⁻¹ * (⟨l, hl⟩ : L)).val ∈ H :=
      hH.1.2 (hQT (mem_map.mpr ⟨_, hker, rfl⟩))
    have hdH : d.val ∈ H := hYH (hDY hd)
    have hprod := H.mul_mem hdH hqH
    simpa only [coe_mul, coe_inv, dl, mul_inv_cancel_left] using hprod

/-- Source 13.6.26(1) from the actual earlier A₅ setup and the genuine A.3.8
orbit theorem. The original relative component and T-span are retained;
no 13.3.8 conclusion is requested as a premise. -/
theorem source_13_6_26_1_of_A5_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u})
    (T : Sylow 2 G) (L V M MV L₁ G₁ : Subgroup G)
    [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M) :
    ∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M := by
  intro K hK hKM
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨hYH, hHY, hperfect, hp⟩ :=
    relative_component_span_properties hG hA38 T hH.1.1 hTH hK
  let := hperfect
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans
    (show M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) from
      s.unique_overgroup.symm ▸ Set.mem_singleton M).2
  have hYM : conjugateSpanBy K T ≤ M :=
    conjugateSpanBy_le hKM (hTM.trans M.le_normalizer)
  have hYne : conjugateSpanBy K T ≠ ⊥ := by
    intro hz
    have hKbot : K = ⊥ := bot_unique ((le_conjugateSpanBy K T).trans_eq hz)
    have hrel : K.subgroupOf H = ⊥ := by rw [hKbot]; simp
    apply hK.2.not_isSolvable
    rw [hrel]
    infer_instance
  exact perfect_normal_span_excluded hG T L M H (conjugateSpanBy K T)
    s.quotient s.local_normalizer s.unique_overgroup ⟨⟨hH.1.1, hTH⟩, hH.2.2⟩
    hYH hHY hp hYne hYM

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
