module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalPrimitive
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.ReducedNormal.SylowSupplement
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer

/-!
# The original odd-chief radical and Thompson movement

A normal subgroup of the plus kernel has its two-core inside R1=O2(L1T).
For an odd-chief primitive witness, R1 is therefore Sylow in KR1. The
normal elementary detecting layer U0 also lies in R1, so A.1.19 gives
C_KR1(R2(KR1))=O2(KR1). If J(R1) centralized this reduced subgroup,
B.2.3(5) would identify Baum(R1) with Baum(O2(KR1)); K would normalize it,
contrary to the original Baumann normalizer bound and K escaping M.

The final theorem applies all reductions to the actual selected primitive
witness. The source Baumann bound remains explicit; its natural-six
producer is developed separately. No kernel equality is asserted here.

Source: Aschbacher--Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Section08.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The two-core of a normal plus-kernel subgroup lies in the original R1. -/
theorem source_normal_kernel_core_le_point_radical
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    K.pCoreIn 2 ≤ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hKH : K ≤ H := hKC.trans (kernel_le_H (D := F))
  have hQH : K.pCoreIn 2 ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes hKH hKn
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTH : (T : Subgroup G) ≤ H := h.T_le_H
    have ht := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using ht
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
    (hQH.trans (hQT.trans le_sup_right))
  exact h.local_le.trans (hKn.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))

/-- In the odd-chief case R1 is a Sylow subgroup of KR1. -/
theorem source_primitive_odd_sylow
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (ho : Odd (Nat.card (J ⧸ pCore 2 J))) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R₁ := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    Chapter1.IsSylowIn 2 R₁ (J.map H.subtype ⊔ R₁) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  have hoK : Odd (Nat.card (K ⧸ pCore 2 K)) := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact ho
  have hindex : ¬ 2 ∣ (pCore 2 K).index := by
    rw [index_eq_card]
    exact hoK.not_two_dvd_nat
  have hRH : R ≤ H := (pCoreIn_le 2 _).trans h.local_le
  exact IsPGroup.exists_sylow_sup_of_coprime_index K R (isPGroup_pCoreIn 2 _)
    (hRH.trans hJn) (pCore 2 K) hindex
    (source_normal_kernel_core_le_point_radical h hJC hJn)

/-- The detecting layer lies in the literal point radical R1. -/
theorem source_fixedLayer_le_point_radical
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    fixedLayer F ≤ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTH : (T : Subgroup G) ≤ H := h.T_le_H
    have ht := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using ht
  have hUQ : fixedLayer F ≤ H.pCoreIn 2 := inf_le_left.trans h.UH_le_QH
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le hUQ)
    (hUQ.trans (hQT.trans le_sup_right))
    (h.local_le.trans (fixedLayer_normalized (D := F)))

/-- For the original odd primitive witness, R2(KR1) has centralizer exactly
O2(KR1). The detecting module and the Sylow supplement are constructed. -/
theorem source_primitive_odd_reduced_centralizer
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (ho : Odd (Nat.card (J ⧸ pCore 2 J))) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R₁ := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    let X := J.map H.subtype ⊔ R₁
    X ⊓ centralizer ((reducedTwoSubgroup X).map X.subtype : Set G) = X.pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let : IsElementaryAbelian 2 F.V := h.elementary
  let : IsElementaryAbelian 2 F.Vplus := IsElementaryAbelian.of_le h.plus_le
  let : IsMulCommutative (conjugateSpanBy F.Vplus H) := hU
  let : IsElementaryAbelian 2 F.UH := conjugateSpanBy_elementary_of_commutative F.Vplus H
  let : IsElementaryAbelian 2 (fixedLayer F) := IsElementaryAbelian.of_le inf_le_left
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F)))
    ((pCoreIn_le 2 _).trans h.local_le)
  have hUX : fixedLayer F ≤ X := (source_fixedLayer_le_point_radical h).trans le_sup_right
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hJn
  obtain ⟨S, hS⟩ := source_primitive_odd_sylow h J hJC hJn ho
  have hgen : K.subgroupOf X ⊔ (S : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left), hS,
      ← MonoidHom.range_eq_map, range_subtype]
  exact centralizer_reducedTwo_eq_pCoreIn_of_sylow_supplement
    K X (fixedLayer F) le_sup_left hUX (hXH.trans hJn)
    (hXH.trans (fixedLayer_normalized (D := F)))
    (subnormal_fixedLayer_centralizer h hJC (inferInstance : (K.subgroupOf H).Normal).isSubnormal)
    S hgen

/-- The original Baumann normalizer bound forces Thompson movement on
R2(KR1), as required by the odd-chief step of 13.7.4. -/
theorem source_primitive_odd_thompson_movement
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (ho : Odd (Nat.card (J ⧸ pCore 2 J)))
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R₁ := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    let X := J.map H.subtype ⊔ R₁
    ¬ elementaryAbelianMaxJ R₁ ≤ centralizer
      ((reducedTwoSubgroup X).map X.subtype : Set G) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let U := (reducedTwoSubgroup X).map X.subtype
  let : IsElementaryAbelian 2 (reducedTwoSubgroup X) := isPReduced_reducedPSubgroup.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map X.subtype
  obtain ⟨S, hS⟩ := source_primitive_odd_sylow h J hJC hJn ho
  have hQR : X.pCoreIn 2 ≤ R := (pCoreIn_le_sylow X S).trans_eq hS
  have hUR : U ≤ R := (map_mono (reducedPSubgroup_le_pCore 2 X)).trans hQR
  have hc : X ⊓ centralizer (U : Set G) = X.pCoreIn 2 :=
    source_primitive_odd_reduced_centralizer h hU J hJC hJn ho
  have hRC : R ⊓ centralizer (U : Set G) = X.pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_right (centralizer (U : Set G)) (show R ≤ X from le_sup_right)).trans hc.le
    · exact le_inf hQR (hc.ge.trans inf_le_right)
  change ¬ elementaryAbelianMaxJ R ≤ centralizer (U : Set G)
  intro hmove
  have hb : ChapterB.baumann R = ChapterB.baumann (X.pCoreIn 2) := by
    rw [ChapterB.lemma_B_2_3_5 R U hUR hmove, hRC]
  apply hout
  apply (show K ≤ X from le_sup_left).trans
  apply le_trans ?_ hB
  change X ≤ normalizer (ChapterB.baumann R : Set G)
  rw [hb]
  exact (X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      (Stellmacher.normalizer_le_normalizer_baumann _)

/-- The selected odd primitive source witness carries the actual point-radical
Sylow subgroup. This is the odd branch of the original kernel alternatives. -/
theorem source_ordinary_kernel_odd_branch
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hk : kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) ≠ H.pCoreIn 2)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R₁ := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    ∃ J : Subgroup H, let K := J.map H.subtype
      K ≤ kernel F ∧ IsPPerfect 2 K ∧ K ≠ ⊥ ∧ ¬ F.L₁ ≤ K ∧
      K ⊓ centralizer (fixedLayer F : Set G) = K.pCoreIn 2 ∧
      ((J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J)) ∨
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ H ≤ normalizer (K : Set G) ∧ ¬ K ≤ M ∧
          ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥ ∧
          IsElementaryAbelian p (J ⧸ pCore 2 J) ∧
          (Nat.card (J ⧸ pCore 2 J) = p ∨ Nat.card (J ⧸ pCore 2 J) = p ^ 2) ∧
          K.pCoreIn 2 ≤ R₁ ∧ Chapter1.IsSylowIn 2 R₁ (K ⊔ R₁) ∧
          let X := K ⊔ R₁
          X ⊓ centralizer ((reducedTwoSubgroup X).map X.subtype : Set G) = X.pCoreIn 2 ∧
          ¬ elementaryAbelianMaxJ R₁ ≤ centralizer
            ((reducedTwoSubgroup X).map X.subtype : Set G))) := by
  obtain ⟨J, hres, hKC, hs, hp, hKne, hf, hL, hc, hcomm, hmove, h1, h2, h3, hm⟩ :=
    source_ordinary_kernel_alternatives d h1221 h hU eL hne hV hk
  dsimp only at *
  refine ⟨J, hKC, hp, hKne, hL, hc, ?_⟩
  rcases hm with hm | ⟨p, hprime, ho, hn, hout, hchief, hE, hcard⟩
  · exact Or.inl hm
  · have hoJ : Odd (Nat.card (J ⧸ pCore 2 J)) := by
      rcases hcard with he | he
      · exact he ▸ ho
      · exact he ▸ ho.pow
    exact Or.inr ⟨p, hprime, ho, hn, hout, hchief, hE, hcard,
      source_normal_kernel_core_le_point_radical h hKC hn,
      source_primitive_odd_sylow h J hKC hn hoJ,
      source_primitive_odd_reduced_centralizer h hU J hKC hn hoJ,
      source_primitive_odd_thompson_movement h hU J hKC hn hoJ hout hB⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
