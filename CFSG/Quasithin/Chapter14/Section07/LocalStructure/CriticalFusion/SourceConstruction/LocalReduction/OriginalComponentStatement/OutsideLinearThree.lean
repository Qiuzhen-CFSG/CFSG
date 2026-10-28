module
public import Theory.GroupTheory.CubicCoreCentralizerRank
public import Theory.SpecificGroups.PSL3.SplitThreeRank
public import Theory.SpecificGroups.PSL3.LiftedBorelInner
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoNormality

/-!
# The original outside-component large projective linear row

Suppose the actual C-component C of an original local I has
C/O₂(C) ≃ PSL₃(2ⁿ), n ≥ 3. When L₁ is outside C, the established
B_C = B makes the original inverter fix the lifted Borel residual modulo
its own two-core. The large linear Borel detector makes this inverter
inner on C/O₂(C). Correcting it inside the original Sylow yields a
centralizing inverter, forces L₁ to centralize the component quotient,
and proves that C normalizes L₁. In I = C L₁ T the point residual is normal.

The original local three-rank bound then gives m₃(C)=1. An explicit
projective elementary nine contradicts this when n is even, proving
L₁ ≤ C for those actual original components. All quotient maps, the
original Sylow and the actual component inclusion are retained.

This proves these rows of the 14.7.41 action and field reductions.
It does not supply the remaining other-model cases, the
14.7.42 module recognition or the all-component 14.7.47 input. The
structural, faithful and earlier-source premises remain explicit with
their existing producers; no universal premise is inferred from guarded
same-group facts.

Source: Aschbacher–Smith 14.7.41–42, printed pp.1061–1062,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_eq_one_iff coreAction_mk)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem normalizer_image_eq (I : Subgroup G) (C : Subgroup I)
    (P : Sylow 2 C)
    (hP : (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C) :
    (normalizer (P : Set C)).map (I.subtype.comp C.subtype) =
      componentSylowNormalizer T I C := by
  have he : (normalizer (P : Set C)).map C.subtype =
      C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I) := by
    change (normalizer (↑(P : Subgroup C) : Set C)).map C.subtype = _
    have hi : ((T : Subgroup G).subgroupOf I ⊓ C).subgroupOf C =
        ((T : Subgroup G).subgroupOf I).subgroupOf C := by
      ext x
      exact and_iff_left x.property
    rw [hP,←hi,←subgroupOf_normalizer_eq (show
      (T : Subgroup G).subgroupOf I ⊓ C ≤ C from inf_le_right),
      subgroupOf_map_subtype,inf_comm]
    rfl
  rw [←Subgroup.map_map,he]
  rfl

private theorem component_actor_inner_of_fixed_borel
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 3 ≤ n)
    (I : Subgroup G) (C : Subgroup I) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) (P : Sylow 2 C)
    (hP : (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C)
    (x : I) (hx : ∃ k : ℕ, x ^ (2^k) = 1)
    (hxP : (P : Subgroup C).map (MulAut.conjNormal x).toMonoidHom = P)
    (hdisp : let B₀ := componentSylowNormalizer T I C
      let B := (pResidual 2 B₀).map B₀.subtype
      ∀ b ∈ B, (x : G)*b*(x : G)⁻¹*b⁻¹ ∈ B.pCoreIn 2) :
    normalQuotientAction C (pCore 2 C) x ∈ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  let f := I.subtype.comp C.subtype
  have hf : Function.Injective f := I.subtype_injective.comp C.subtype_injective
  let R := (pResidual 2 (normalizer (P : Set C))).map (normalizer (P : Set C)).subtype
  let B₀ := componentSylowNormalizer T I C
  let B := (pResidual 2 B₀).map B₀.subtype
  have hRB : R.map f = B := by
    rw [show R = (pResidual 2 (normalizer (P : Set C))).map _ from rfl,
      map_embedded_pResidual,normalizer_image_eq I C P hP]
  have haction : normalQuotientAction C (pCore 2 C) x =
      (pCore 2 C).quotientAut (MulAut.conjNormal x) := by
    ext y
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) y
    rw [normalQuotientAction_apply_mk,quotientAut_apply_mk]
  rw [haction]
  apply Matrix.PSL3.LiftedBorelInner.quotient_inner_of_borelResidual_fixed_three hE hn e P
    (MulAut.conjNormal x) (by
      obtain ⟨k,hk⟩ := hx
      exact ⟨k,by rw [←map_pow,hk,map_one]⟩) hxP
  intro b hb
  have hbB : f b ∈ B := hRB ▸ mem_map_of_mem f hb
  have hd := hdisp (f b) hbB
  have hnB : (f b)⁻¹ ∈ normalizer (B.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image B (pCore 2 B)
      (B.le_normalizer (B.inv_mem hbB))
  have hh := (mem_normalizer_iff.mp hnB _).mp hd
  have hval : f (b⁻¹ * MulAut.conjNormal x b) ∈ B.pCoreIn 2 := by
    convert hh using 1
    change (f b)⁻¹ * ((x : G) * f b * (x : G)⁻¹) = _
    group
  have hcore : (R.pCoreIn 2).map f = B.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 R f hf,hRB]
  exact (mem_map_iff_mem hf).mp (hcore.symm ▸ hval)

/-- The original inverter acts inner on the large linear-three quotient. -/
theorem local_above_four_linearThree_component_inner_inverter
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 3 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) :
    ∃ hCN : C.Normal, letI := hCN
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        (∀ y : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural)
              t.property.1⟩ y = y⁻¹) ∧
        normalQuotientAction C (pCore 2 C)
          ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩ ∈
            MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hCN := local_cComponent_normal d h hab structural previous faithful earlier
    I (C.map I.subtype) hI (map_subtype_le _) hC'
  let hNC : C.Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hCN
  let := hNC
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  obtain ⟨_,_,_,t,htB,hti,htfix⟩ := local_component_borel_fixed_actions
    d h hab structural previous faithful earlier I hI C hC hout
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  have hpow : ∃ k : ℕ, tI ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := T.isPGroup' (⟨t,t.property.1⟩ : (T : Subgroup G))
    exact ⟨k,Subtype.ext (show (t : G) ^ (2^k) = 1 from congrArg Subtype.val hk)⟩
  have hpres : (P : Subgroup C).map (MulAut.conjNormal tI).toMonoidHom = P := by
    apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective
      (f := (MulAut.conjNormal tI : MulAut C).toMonoidHom)
      (K := (P : Subgroup C)) (MulAut.conjNormal tI : MulAut C).injective).symm)
    rintro _ ⟨c,hc,rfl⟩
    rw [hP] at hc ⊢
    change (t : G) * (c : I) * (t : G)⁻¹ ∈ (T : Subgroup G)
    exact T.mul_mem (T.mul_mem t.property.1 hc) (T.inv_mem t.property.1)
  refine ⟨hNC,t,hti,?_⟩
  apply component_actor_inner_of_fixed_borel hE hn I C e P hP tI hpow hpres
  dsimp only
  intro b hb
  have hh := (coreAction_eq_one_iff _ _).mp htfix ⟨b,hb⟩
  exact mem_map_of_mem _ hh

/-- The actual component normalizes the point and admits an original-Sylow centralizing inverter. -/
theorem local_above_four_linearThree_component_normalizes_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 3 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) :
    ∃ hCN : C.Normal, letI := hCN
      C.map I.subtype ≤ normalizer (F.Li L 1 : Set G) ∧
      (F.Li L 1).subgroupOf I ≤ (normalQuotientAction C (pCore 2 C)).ker ∧
      ∃ s : (T : Subgroup G),
        normalQuotientAction C (pCore 2 C)
          ⟨s,F.sylow_le_of_mem_Hz hI s.property⟩ = 1 ∧
        ∀ y : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨s,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural)
              s.property⟩ y = y⁻¹ := by
  obtain ⟨hCN,t,hti,htinner⟩ := local_above_four_linearThree_component_inner_inverter
    d h hab structural previous faithful earlier I hI C hC hout hE hn e
  let := hCN
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  have hnorm : (S : Subgroup I) ≤ normalizer (A : Set I) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li
      (h.sylow_normalizes structural) hx) (a : G)
  have hnot : ¬ A ≤ C := by
    intro hh
    apply hout
    have hh' := map_mono (f := I.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAI] at hh'
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    let : Group.IsPerfect SL(3,E) := Atlas.sl_perfect 3 (by decide)
    have hze : center PSL(3,E) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,E)
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center PSL(3,E) at hh
    rw [hze,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  have htiA (a : I) (ha : a ∈ A) : tI*a*tI⁻¹*a ∈ A.pCoreIn 2 := by
    rw [show A = (F.Li L 1).subgroupOf I from rfl,pCoreIn_subgroupOf 2 _ I hAI]
    let a' : F.Li L 1 := ⟨a,ha⟩
    let t' : normalizer (F.Li L 1 : Set G) :=
      ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) t.property.1⟩
    have hi := hti (QuotientGroup.mk' (pCore 2 (F.Li L 1)) a')
    rw [coreAction_mk] at hi
    have hh : (F.Li L 1).normalizerMonoidHom t' a' * a' ∈ pCore 2 (F.Li L 1) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 (F.Li L 1)) (_ * _) = 1
      rw [map_mul,hi,inv_mul_cancel]
    exact mem_map_of_mem (F.Li L 1).subtype hh
  obtain ⟨s,hs,hsk,hsi,hfix⟩ := outside_cubic_centralizing_inverter A C S hp hc hnorm hnot
    hz tI t.property.1 htiA htinner
  have hCA := normalizes_of_trivial_core_action A C S hp hnorm hfix
  have hCA' : C.map I.subtype ≤ normalizer (F.Li L 1 : Set G) := by
    have hh := (map_mono (f := I.subtype) hCA).trans (A.le_normalizer_map I.subtype)
    rwa [map_subgroupOf_eq_of_le hAI] at hh
  refine ⟨hCN,hCA',hfix,⟨s,hs⟩,hsk,?_⟩
  intro y
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) y
  rw [coreAction_mk]
  apply eq_inv_of_mul_eq_one_left
  rw [←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hh := hsi (⟨a,hAI a.property⟩ : I) a.property
  rw [show A = (F.Li L 1).subgroupOf I from rfl,pCoreIn_subgroupOf 2 _ I hAI] at hh
  exact (mem_map_iff_mem (F.Li L 1).subtype_injective).mp hh

/-- Source 14.7.41 point normality in the literal reduced local C L₁ T for the large binary L₃ row. -/
theorem local_above_four_linearThree_reduced_point_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 3 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E))
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G)) :
    ((F.Li L 1).subgroupOf I).Normal := by
  obtain ⟨_,hCA,_,_⟩ := local_above_four_linearThree_component_normalizes_point
    d h hab structural previous faithful earlier I hI C hC hout hE hn e
  apply normal_subgroupOf_of_le_normalizer
  rw [hgen]
  exact sup_le (sup_le hCA (F.Li L 1).le_normalizer)
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural))

/-- The original outside component has three-rank one in the large linear-three row. -/
theorem local_above_four_linearThree_component_threeRank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 3 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : primeRank 3 C = 1 := by
  obtain ⟨hCN,_,hfix,_⟩ := local_above_four_linearThree_component_normalizes_point
    d h hab structural previous faithful earlier I hI C hC hout hE hn e
  let := hCN
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    let : Group.IsPerfect SL(3,E) := Atlas.sl_perfect 3 (by decide)
    have hze : center PSL(3,E) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,E)
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center PSL(3,E) at hh
    rw [hze,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  have hr := threeRank_le_one_of_cubic_core_centralizes A C hc hz hrI hfix
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hr
  have hlo := local_component_threeRank d h hab structural previous faithful earlier I hI C hC
  omega

/-- The split large-field rows force containment of the original point residual in the actual component. -/
theorem local_large_even_linearThree_contains_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 4 ≤ n) (heven : Even n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : F.Li L 1 ≤ C.map I.subtype := by
  by_contra hout
  have hr := local_above_four_linearThree_component_threeRank
    d h hab structural previous faithful earlier I hI C hC hout hE (by omega) e
  have htwo := Matrix.PSL3.SplitThreeRank.even_binary_rank hE heven
  rw [←primeRank_congr 3 e,
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at htwo
  omega

/-- The original large-field API, with its original hypothesis. -/
theorem local_large_linearThree_component_inner_inverter
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 4 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) :
    ∃ hCN : C.Normal, letI := hCN
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        (∀ y : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural)
              t.property.1⟩ y = y⁻¹) ∧
        normalQuotientAction C (pCore 2 C)
          ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩ ∈
            MulAut.innerSubgroup (C ⧸ pCore 2 C) :=
  local_above_four_linearThree_component_inner_inverter d h hab structural previous faithful earlier I hI C hC hout hE (by omega) e

/-- The original large-field API, with its original hypothesis. -/
theorem local_large_linearThree_component_normalizes_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 4 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) :
    ∃ hCN : C.Normal, letI := hCN
      C.map I.subtype ≤ normalizer (F.Li L 1 : Set G) ∧
      (F.Li L 1).subgroupOf I ≤ (normalQuotientAction C (pCore 2 C)).ker ∧
      ∃ s : (T : Subgroup G),
        normalQuotientAction C (pCore 2 C)
          ⟨s,F.sylow_le_of_mem_Hz hI s.property⟩ = 1 ∧
        ∀ y : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨s,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural)
              s.property⟩ y = y⁻¹ :=
  local_above_four_linearThree_component_normalizes_point d h hab structural previous faithful earlier I hI C hC hout hE (by omega) e

/-- The original large-field API, with its original hypothesis. -/
theorem local_large_linearThree_reduced_point_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 4 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E))
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G)) :
    ((F.Li L 1).subgroupOf I).Normal :=
  local_above_four_linearThree_reduced_point_normal d h hab structural previous faithful earlier I hI C hC hout hE (by omega) e hgen

/-- The original large-field API, with its original hypothesis. -/
theorem local_large_linearThree_component_threeRank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 4 ≤ n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : primeRank 3 C = 1 :=
  local_above_four_linearThree_component_threeRank d h hab structural previous faithful earlier I hI C hC hout hE (by omega) e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
