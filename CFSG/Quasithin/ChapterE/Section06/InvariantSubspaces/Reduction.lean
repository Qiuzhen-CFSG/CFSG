module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Centralizers of invariant subspaces

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Proposition E.6.13 and Lemma E.6.14, printed
pp.250–251 (PDF pp.261–262).

For E.6.13 a minimal local overgroup of T outside M, inside C_G(W)T,
satisfies the genuine relative-normality hypotheses of Theorem 3.1.1.
Its common normal two-subgroup contradicts uniqueness. The only earlier
input here is the exact statement of 3.1.1; E.6.5(1) is already proved.

For E.6.14 the normalizer of a selected block is either the given maximal
normalizer of W or all of M₀. In the second case C_V(L) contradicts E.6.13;
in the first case the local index theorem gives index two.

The latter is a conditional assembly, not yet E.6.14: `SingleBlockInput`
still requires the rank/faithful-action reduction from E.6.7, and
`SingleBlockIndexInput` requires the localization of the C.5.7 argument.
In particular, separate SQTK hypotheses on the local groups must not be
confused with the printed ambient SQTK hypothesis of C.5.1.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The relative-normality statement of source Theorem 3.1.1. -/
def CommonNormalInput (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  IsSimpleQTKE K G → ∀ A H R : Subgroup G,
    A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
    Order.HasUniqueMaximalOver (T : Subgroup G) H →
    R ≠ ⊥ → R ≤ T →
    Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
    A ≤ normalizer (R : Set G) →
    ∃ N : Subgroup G, N ≤ R ∧ N ≠ ⊥ ∧ Chapter3.NormalIn N (Chapter3.generated A H)

omit [Finite G] in
private theorem residual_le_of_normalized_supplement {H A Y : Subgroup G}
    (hA : IsPGroup 2 A) (hAH : A ≤ normalizer (H : Set G))
    (hY : Y ≤ H ⊔ A) : (pResidual 2 Y).map Y.subtype ≤ H := by
  let J := H ⊔ A
  let N := H.subgroupOf J
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le H.le_normalizer hAH)
  have hgen : N ⊔ A.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show H ≤ J from le_sup_left) (show A ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (A.subgroupOf J) hA.comap_subtype hgen
  have hr : pResidual 2 J ≤ N := sInf_le ⟨inferInstance, hquot⟩
  have hi := (map_pResidual_le 2 (inclusion hY)).trans hr
  rintro x ⟨y, hy, rfl⟩
  exact hi (mem_map_of_mem (inclusion hY) hy)

omit [Finite G] in
private theorem normalizer_mem_HOver {R : Subgroup G} (T : Sylow 2 G)
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G)) :
    normalizer (R : Set G) ∈ Chapter1.HOver G (T : Set G) := by
  refine ⟨?_, hTR⟩
  have hr := le_pCoreIn_of_normalizes hR R.le_normalizer (le_refl (normalizer (R : Set G)))
  exact fun he => hne (le_bot_iff.mp (he ▸ hr))

private theorem sylow_normalizes_Q {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 K T M V) :
    (T : Subgroup G) ≤ normalizer (sylowCentralizer (T : Subgroup G) V : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    (h.sylow_le_normalizer.trans (normalizer_le_normalizer_centralizer V))).trans
    inf_normalizer_le_normalizer_inf

/-- E.6.13, conditional only on the exact source statement of 3.1.1. -/
theorem centralizer_le_of_normal_in_sylow
    {K : GroupClass.{u}} {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 K T M V)
    (h311 : CommonNormalInput K T)
    (hne : W ≠ ⊥) (hWV : W ≤ V) (hodd : oddCentralizerCondition M V W)
    (hnormal : (W.subgroupOf (T : Subgroup G)).Normal) :
    centralizer (W : Set G) ≤ M := by
  by_contra hescape
  have hW : W ∈ obstructionFamily M V := ⟨hWV, hne, hescape, hodd⟩
  let H := centralizer (W : Set G)
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQ : IsPGroup 2 Q :=
    T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hWN : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hWV.trans h.le_sylow)).mp hnormal
  have hTH : (T : Subgroup G) ≤ normalizer (H : Set G) :=
    hWN.trans (normalizer_le_normalizer_centralizer W)
  have hW2 : IsPGroup 2 W :=
    T.isPGroup'.of_injective (inclusion (hWV.trans h.le_sylow))
      (inclusion_injective (hWV.trans h.le_sylow))
  have hlocal : H ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show (T : Subgroup G) ≤ H ⊔ (T : Subgroup G) from le_sup_right⟩
    have hcore := le_pCoreIn_of_normalizes hW2
      ((hWV.trans h.le_sylow).trans le_sup_right)
      (sup_le (centralizer_le_normalizer _) hWN)
    exact fun he => hne (le_bot_iff.mp (he ▸ hcore))
  obtain ⟨H₁, hH₁, hminimal⟩ := Finite.exists_le_minimal
    (p := fun Y : Subgroup G => Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M)
    (a := H ⊔ (T : Subgroup G)) ⟨hlocal, fun he => hescape (le_sup_left.trans he)⟩
  have hstar : H₁ ∈ Chapter3.HStar (T : Subgroup G) M := hminimal
  have hres : (pResidual 2 H₁).map H₁.subtype ≤ H :=
    residual_le_of_normalized_supplement T.isPGroup' hTH hH₁
  have hQH : Chapter1.IsSylowIn 2 Q H := h.sylow_obstruction hW
  have hSyl := hQH.restrict le_sup_right
    (sup_le hres (Chapter1.isSylowIn_iff.mp hQH).2.1)
  have hcommon := h311 h.simpleQTKE (normalizer (Q : Set G)) H₁ Q
    (normalizer_mem_HOver T hQ h.sylowCentralizer_ne_bot (sylow_normalizes_Q h))
    hstar.1.1 (Chapter3.HStar.hasUniqueMaximalOver T h.sylow_le hstar)
    h.sylowCentralizer_ne_bot inf_le_left hSyl le_rfl
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → normalizer (Q : Set G) ≤ N → N = M := by
    intro N hN hQN
    exact h.unique N hN (inf_le_right.trans hQN)
  exact Chapter3.no_common_normal_of_unique_maximal hQ hunique hstar.1.2 hcommon


/-- Proposition E.6.13, including the stated exclusion from Γ. The input
`CommonNormalInput` is discharged by the owner of source Theorem 3.1.1. -/
theorem proposition_E_6_13
    {K : GroupClass.{u}} {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 K T M V) (h311 : CommonNormalInput K T)
    (hne : W ≠ ⊥) (hWV : W ≤ V) (hodd : oddCentralizerCondition M V W)
    (hnormal : (W.subgroupOf (T : Subgroup G)).Normal) :
    centralizer (W : Set G) ≤ M ∧ W ∉ obstructionFamily M V := by
  have hc := centralizer_le_of_normal_in_sylow h h311 hne hWV hodd hnormal
  exact ⟨hc, fun hW => hW.2.2.1 hc⟩


omit [Finite G] in
private theorem map_primeToResidual_le_all {A B : Type*} [Group A] [Group B]
    (p : ℕ) (f : A →* B) : (primeToResidual p A).map f ≤ primeToResidual p B := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  have hr := primeToResidual_le_ker ((QuotientGroup.mk' N).comp f)
    (show Nat.Coprime p (Nat.card (B ⧸ N)) by rwa [← N.index_eq_card])
  rintro x ⟨y, hy, rfl⟩
  exact (QuotientGroup.eq_one_iff (f y)).mp (MonoidHom.mem_ker.mp (hr hy))

omit [Finite G] in
/-- The odd induced-centralizer condition passes to larger subspaces. -/
theorem oddCentralizerCondition_mono {M V U W : Subgroup G} (hUW : U ≤ W)
    (hU : oddCentralizerCondition M V U) : oddCentralizerCondition M V W := by
  let C := M ⊓ centralizer (U : Set G)
  let D := M ⊓ centralizer (W : Set G)
  have hDC : D ≤ C := inf_le_inf_left M (Subgroup.centralizer_le hUW)
  have hr := map_primeToResidual_le_all 2 (inclusion hDC)
  rintro x ⟨d, hd, rfl⟩
  exact hU (mem_map.mpr ⟨inclusion hDC d, hr (mem_map_of_mem _ hd), rfl⟩)

/-- An actual order-three subgroup acts injectively by conjugation on W. -/
def HasFaithfulThreeAction (W : Subgroup G) : Prop :=
  ∃ (A : Subgroup G) (hAW : A ≤ normalizer (W : Set G)),
    Nat.card A = 3 ∧ Function.Injective (W.normalizerMonoidHom.comp (inclusion hAW))

/-- The full second alternative in E.6.14(ii). -/
def ThreeCondition (W : Subgroup G) : Prop :=
  primeRank 3 (centralizer (W : Set G)) ≤ 1 ∨ HasFaithfulThreeAction W

/-- The single-block configuration constructed in the proof on source p.251.
This is an intermediate proof obligation, not the statement of E.6.7.
The actual block and its residual are specified; no centralizer containment
or exclusion from the obstruction family is included. -/
structure SingleBlock (T : Sylow 2 G) (M V W L : Subgroup G) : Prop where
  le_centralizer : L ≤ centralizer (W : Set G)
  generated : centralizer (W : Set G) = (centralizer (W : Set G) ⊓ M) ⊔ L
  type : ChapterC.IsChiZeroBlock L
  residual_three : L = (primeToResidual 3 (centralizer (W : Set G))).map
    (centralizer (W : Set G)).subtype
  unique_maximal : Order.HasUniqueMaximalOver (sylowCentralizer (T : Subgroup G) V)
    (L ⊔ sylowCentralizer (T : Subgroup G) V)

/-- Block selection remains a separate proof obligation, with all of the
hypotheses from E.6.14(i),(ii), independent of the choice of M₀. -/
def SingleBlockInput (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ W ∈ obstructionFamily M V, HasCharacteristicTwo (centralizer (W : Set G)) →
    ThreeCondition W → ∃ L : Subgroup G, SingleBlock T M V W L

/-- The required localization of the index conclusion of C.5.7.
This is a separate proof obligation, not a restatement of the printed lemma: its SQTK
hypotheses are on the two actual local groups, not on the simple ambient
QTKE group. Here s=1 is expressed by the actual residual L being a chi-zero
block. Normality is relative to A, and the common-normal exclusion is
relative to the subgroup generated by A and H. Only the case R = T_H
used in E.6.14 is requested. -/
def SingleBlockIndexInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G,
    IsSQTK K A → IsSQTK K H → HasCharacteristicTwo H →
    Chapter1.IsSylowIn 2 R H → Order.HasUniqueMaximalOver R H → R ≤ A →
    A ≤ normalizer (R : Set G) →
    (¬ ∃ N : Subgroup G, N ≤ R ∧ N ≠ ⊥ ∧ Chapter3.NormalIn N (Chapter3.generated A H)) →
    (pResidual 2 H).map H.subtype = L → ChapterC.IsChiZeroBlock L →
    localNormalizer A L ⋖ A → (localNormalizer A L).relIndex A = 2

omit [Finite G] in
private theorem characteristicTwo_of_sylow_overgroup {Q H J : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 Q H) (hQJ : Q ≤ J) (hJH : J ≤ H)
    (hc : HasCharacteristicTwo H) : HasCharacteristicTwo J := by
  obtain ⟨P, hP⟩ := hS
  have hPJ : (P : Subgroup H) ≤ J.subgroupOf H := by
    intro x hx
    exact hQJ (hP ▸ mem_map_of_mem H.subtype hx)
  exact (show HasCharacteristicTwo (J.subgroupOf H) from
    centralizer_pCore_le_of_sylow_le P (J.subgroupOf H) hPJ hc).of_equiv
      (subgroupOfEquivOfLe hJH)

omit [Finite G] in
private theorem SingleBlock.normalized {T : Sylow 2 G} {M V W L : Subgroup G}
    (hL : SingleBlock T M V W L) : normalizer (W : Set G) ≤ normalizer (L : Set G) := by
  rw [hL.residual_three]
  exact (normalizer_le_normalizer_centralizer W).trans
    (normalizer_le_normalizer_characteristic_image (centralizer (W : Set G))
      (primeToResidual 3 (centralizer (W : Set G))))


/-- Conditional assembly for E.6.14 after single-block selection and
localization of C.5.7. It is not the completed source lemma. Every source
condition is retained. The branch where M₀ normalizes the block is ruled out
using E.6.13 on C_V(L); the other branch uses the index conclusion of C.5.7. -/
theorem centralizer_le_of_singleBlock
    {K : GroupClass.{u}} {T : Sylow 2 G} {M V W M₀ : Subgroup G}
    (h : HypothesisE61 K T M V)
    (h311 : CommonNormalInput K T)
    (h57 : SingleBlockIndexInput (G := G) K) (hblocks : SingleBlockInput T M V)
    (hne : W ≠ ⊥) (hWV : W ≤ V) (hodd : oddCentralizerCondition M V W)
    (hchar : HasCharacteristicTwo (centralizer (W : Set G))) (hthree : ThreeCondition W)
    (hTM₀ : (T : Subgroup G) ≤ M₀)
    (hM₀Q : M₀ ≤ normalizer (sylowCentralizer (T : Subgroup G) V : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hmax : localNormalizer M₀ W ⋖ M₀) (hindex : (localNormalizer M₀ W).relIndex M₀ ≠ 2) :
    centralizer (W : Set G) ≤ M := by
  by_contra hescape
  have hW : W ∈ obstructionFamily M V := ⟨hWV, hne, hescape, hodd⟩
  obtain ⟨L, hL⟩ := hblocks W hW hchar hthree
  have hLM : ¬ L ≤ M := by
    intro hLM
    apply hescape
    rw [hL.generated]
    exact sup_le inf_le_right hLM
  have hbetween : localNormalizer M₀ W ≤ localNormalizer M₀ L :=
    inf_le_inf_left M₀ hL.normalized
  rcases hmax.eq_or_eq hbetween inf_le_left with heq | heq
  · let Q := sylowCentralizer (T : Subgroup G) V
    let H₁ := L ⊔ Q
    have hSyl := show Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (W : Set G)) from h.sylow_obstruction hW
    have hQH : Q ≤ centralizer (W : Set G) := (Chapter1.isSylowIn_iff.mp hSyl).2.1
    have hH₁H : H₁ ≤ centralizer (W : Set G) := sup_le hL.le_centralizer hQH
    have hQ2 : IsPGroup 2 Q := (Chapter1.isSylowIn_iff.mp hSyl).1
    have hQNL : Q ≤ normalizer (L : Set G) :=
      hQH.trans ((centralizer_le_normalizer _).trans hL.normalized)
    have hres : (pResidual 2 H₁).map H₁.subtype = L :=
      embedded_pResidual_join_pGroup L Q hL.type.chi.short.twoPerfect hQ2 hQNL
    have hH₁Syl : Chapter1.IsSylowIn 2 Q H₁ := hSyl.restrict le_sup_right hH₁H
    have hH₁char : HasCharacteristicTwo H₁ :=
      characteristicTwo_of_sylow_overgroup hSyl le_sup_right hH₁H hchar
    have hW2 : IsPGroup 2 W :=
      T.isPGroup'.of_injective (inclusion (hWV.trans h.le_sylow))
        (inclusion_injective (hWV.trans h.le_sylow))
    have hSQTKW := h.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal (normalizer (W : Set G)) from ⟨W, hne, hW2, rfl⟩)
    have hSQTKH₁ : IsSQTK K H₁ :=
      ⟨hSQTKW.stronglyQuasithin.of_injective
        (inclusion (hH₁H.trans (centralizer_le_normalizer _)))
        (inclusion_injective (hH₁H.trans (centralizer_le_normalizer _))),
       hSQTKW.isKGroup.of_injective
        (inclusion (hH₁H.trans (centralizer_le_normalizer _)))
        (inclusion_injective (hH₁H.trans (centralizer_le_normalizer _)))⟩
    have hSQTKQ := h.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal (normalizer (Q : Set G)) from ⟨Q, h.sylowCentralizer_ne_bot, hQ2, rfl⟩)
    have hSQTKM₀ : IsSQTK K M₀ :=
      ⟨hSQTKQ.stronglyQuasithin.of_injective (inclusion hM₀Q) (inclusion_injective hM₀Q),
       hSQTKQ.isKGroup.of_injective (inclusion hM₀Q) (inclusion_injective hM₀Q)⟩
    have hnocommon := Chapter3.no_common_normal_of_unique_maximal hQ2 hunique
      (show ¬ H₁ ≤ M from fun hh => hLM (le_sup_left.trans hh))
    have hi := h57 M₀ H₁ Q L hSQTKM₀ hSQTKH₁ hH₁char hH₁Syl
      hL.unique_maximal (inf_le_left.trans hTM₀) hM₀Q hnocommon hres hL.type
      (heq.symm ▸ hmax)
    exact hindex (heq ▸ hi)
  · let W₁ := V ⊓ centralizer (L : Set G)
    have hWW₁ : W ≤ W₁ := le_inf hWV (le_centralizer_iff.mp hL.le_centralizer)
    have hW₁ne : W₁ ≠ ⊥ := fun hb => hne (le_bot_iff.mp (hb ▸ hWW₁))
    have hW₁V : W₁ ≤ V := inf_le_left
    have hM₀NL : M₀ ≤ normalizer (L : Set G) := heq ▸ inf_le_right
    have hTNW₁ : (T : Subgroup G) ≤ normalizer (W₁ : Set G) :=
      (le_inf h.sylow_le_normalizer
        ((hTM₀.trans hM₀NL).trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
    have hW₁normal : (W₁.subgroupOf (T : Subgroup G)).Normal :=
      (normal_subgroupOf_iff_le_normalizer (hW₁V.trans h.le_sylow)).mpr hTNW₁
    have hc := centralizer_le_of_normal_in_sylow h h311 hW₁ne hW₁V
      (oddCentralizerCondition_mono hWW₁ hodd) hW₁normal
    exact hLM ((le_centralizer_iff.mpr (show W₁ ≤ centralizer (L : Set G) from inf_le_right)).trans hc)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
