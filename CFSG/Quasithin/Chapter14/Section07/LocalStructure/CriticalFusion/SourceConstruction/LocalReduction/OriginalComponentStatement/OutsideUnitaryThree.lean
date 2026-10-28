module
public import Theory.SpecificGroups.SU3.FixedBorelInner
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.GroupTheory.CubicCoreCentralizerRank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Geometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoNormality

/-!
# The original outside-component binary unitary row

Let C be an actual C-component of an original local I, with L₁ outside C
and C/O₂(C) isomorphic to PSU₃(2ⁿ), n ≥ 2, for the specified Hermitian
form. Transport the actual Sylow and its normalizer to the standard root
and full Borel. The lifted Borel residual maps onto this entire Borel,
so the established B_C = B makes the original inverter fix its quotient.
The unitary calculation then places that inverter in the root inner image
of the actual Sylow action.

The existing Sylow correction gives a centralizing inverter still in T,
kills the L₁-action on C/O₂(C), and proves C normalizes L₁. Consequently
L₁ is normal in the literal reduced local I = C L₁ T. The original local
three-rank bound gives m₃(C) = 1. No complement to the two-core is chosen.

These are the outside-unitary action conclusions of 14.7.41. Module
recognition and the U₃(8) exclusion in 14.7.42–43 remain to be proved.
The structural, faithful and earlier-source premises keep their existing
producers; this does not instantiate universal records from guarded facts.

Source: Aschbacher–Smith 14.7.41–43, printed pp.1061–1062,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
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
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (I : Subgroup G) (C : Subgroup I) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hTI : (T : Subgroup G) ≤ I) (P : Sylow 2 C)
    (hP : (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C)
    (x : I) (hx : (x : G) ∈ T)
    (hdisp : let B₀ := componentSylowNormalizer T I C
      let B := (pResidual 2 B₀).map B₀.subtype
      ∀ b ∈ B, (x : G)*b*(x : G)⁻¹*b⁻¹ ∈ B.pCoreIn 2) :
    normalQuotientAction C (pCore 2 C) x ∈ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ e.surjective
  let π := QuotientGroup.mk' (pCore 2 C)
  let q := e.toMonoidHom.comp π
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  obtain ⟨j,hQ,hN⟩ := psu_borel_model J n (by omega) hE hconj Q
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  have hJ₀ : J₀.form = !![0,0,1;0,1,0;1,0,0] := rfl
  let : Group (ProjectiveSpecialUnitaryMatrixGroup J₀) := inferInstance
  let : DivisionMonoid (ProjectiveSpecialUnitaryMatrixGroup J₀) := Group.toDivisionMonoid
  let e' : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J₀ := e.trans j
  let f : C →* ProjectiveSpecialUnitaryMatrixGroup J₀ := e'.toMonoidHom.comp π
  have hf : Function.Surjective f := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hPf : (P : Subgroup C).map f = projectiveRoot J₀ hJ₀ := by
    change (P : Subgroup C).map (j.toMonoidHom.comp q) = _
    rw [←Subgroup.map_map]
    exact hQ
  have hNf : (normalizer (P : Set C)).map f = projectiveBorel J₀ hJ₀ := by
    change (normalizer (P : Set C)).map (j.toMonoidHom.comp q) = _
    rw [←Subgroup.map_map,P.normalizer_map_surjective q hq]
    exact hN
  let R := (pResidual 2 (normalizer (P : Set C))).map (normalizer (P : Set C)).subtype
  have hRf : R.map f = projectiveBorel J₀ hJ₀ := by
    change ((pResidual 2 (normalizer (P : Set C))).map _).map f = _
    rw [map_embedded_pResidual,hNf]
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J₀.conj 2 n
      (by omega) hE hconj
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
      (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hE)
    have hodd : Odd (Nat.card E - 1) := by
      rw [hE]
      have hpos : (1 : ℕ) ≤ (2^n)^2 := Nat.one_le_pow 2 (2^n) (pow_pos (by decide) n)
      exact Nat.Even.sub_odd hpos
        ((even_two.pow_of_ne_zero (by omega : n ≠ 0)).pow_of_ne_zero (by decide)) odd_one
    rw [projectiveBorel_twoResidual J₀ hJ₀ hE hfixed
      ((by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)) hodd]
    exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)
  have hcore : (R.pCoreIn 2).map f ≤ projectiveRoot J₀ hJ₀ := by
    rw [map_pCoreIn_of_ker_isPGroup f hk,hRf,projectiveBorel_twoCore J₀ n
      (by omega) hE hconj hJ₀]
  let a := normalQuotientAction C (pCore 2 C)
  let β := MulAut.congr e' (a x)
  have heq (c : C) : β (f c) = f (MulAut.conjNormal x c) := by
    change e' (a x (e'.symm (e' (π c)))) = _
    rw [e'.symm_apply_apply,normalQuotientAction_apply_mk]
    rfl
  have hpres : (P : Subgroup C).map (MulAut.conjNormal x).toMonoidHom = P := by
    apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective
      (f := (MulAut.conjNormal x : MulAut C).toMonoidHom)
      (K := (P : Subgroup C)) (MulAut.conjNormal x : MulAut C).injective).symm)
    rintro _ ⟨c,hc,rfl⟩
    rw [hP] at hc ⊢
    change (x : G) * (c : I) * (x : G)⁻¹ ∈ (T : Subgroup G)
    exact T.mul_mem (T.mul_mem hx hc) (T.inv_mem hx)
  have hroot : (projectiveRoot J₀ hJ₀).map β.toMonoidHom = projectiveRoot J₀ hJ₀ := by
    have he : β.toMonoidHom.comp f = f.comp (MulAut.conjNormal x).toMonoidHom :=
      MonoidHom.ext heq
    rw [←hPf,Subgroup.map_map,he,←Subgroup.map_map,hpres]
  let S := T.subtype hTI
  let A := ((S : Subgroup I).map a).map (MulAut.congr e').toMonoidHom
  have hA : IsPGroup 2 A := (S.isPGroup'.map a).map _
  have hRA : (projectiveRoot J₀ hJ₀).map MulAut.conj ≤ A := by
    rintro _ ⟨_,hr,rfl⟩
    rw [←hPf] at hr
    obtain ⟨c,hc,rfl⟩ := hr
    have hcS : (c : I) ∈ S := by
      rw [hP] at hc
      exact hc
    have hh : MulAut.congr e' (MulAut.conj (π c)) ∈ A :=
      mem_map_of_mem (MulAut.congr e').toMonoidHom
        ⟨c,hcS,normalQuotientAction_inner C (pCore 2 C) c⟩
    change MulAut.conj (e' (π c)) ∈ A
    rwa [MulAut.congr_conj] at hh
  have hβ : β ∈ A := mem_map_of_mem (MulAut.congr e').toMonoidHom
    (mem_map_of_mem a hx)
  have hfix : ∀ b ∈ projectiveBorel J₀ hJ₀, β b * b⁻¹ ∈ projectiveRoot J₀ hJ₀ := by
    intro b hb
    rw [←hRf] at hb
    obtain ⟨c,hc,rfl⟩ := hb
    let g := I.subtype.comp C.subtype
    have hg : Function.Injective g := I.subtype_injective.comp C.subtype_injective
    let B₀ := componentSylowNormalizer T I C
    let B := (pResidual 2 B₀).map B₀.subtype
    have hRB : R.map g = B := by
      rw [show R = (pResidual 2 (normalizer (P : Set C))).map _ from rfl,
        map_embedded_pResidual,normalizer_image_eq I C P hP]
    have hbc : g c ∈ B := hRB ▸ mem_map_of_mem g hc
    have hd := hdisp (g c) hbc
    have hRg : (R.pCoreIn 2).map g = B.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 R g hg,hRB]
    have hdR : MulAut.conjNormal x c * c⁻¹ ∈ R.pCoreIn 2 := by
      apply (mem_map_iff_mem hg).mp
      rw [hRg]
      exact hd
    rw [heq,←f.map_mul_inv (MulAut.conjNormal x c) c]
    exact hcore (mem_map_of_mem f hdR)
  have hi := fixed_standard_borel_actor_mem_root_inner J₀ hJ₀ hn hE hconj
    A hA hRA β hβ hroot hfix
  obtain ⟨c,_,hc⟩ := hi
  refine ⟨e'.symm c,?_⟩
  apply (MulAut.congr e').injective
  rw [MulAut.congr_conj,e'.apply_symm_apply]
  exact hc

/-- The original inverter acts inner on the binary unitary-three quotient. -/
theorem local_unitaryThree_component_inner_inverter
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
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
  refine ⟨hNC,t,hti,?_⟩
  apply component_actor_inner_of_fixed_borel J hn hE hconj I C e
    (F.sylow_le_of_mem_Hz hI) P hP tI t.property.1
  dsimp only
  intro b hb
  have hh := (coreAction_eq_one_iff _ _).mp htfix ⟨b,hb⟩
  exact mem_map_of_mem _ hh

/-- The actual component normalizes the point and admits an original-Sylow centralizing inverter. -/
theorem local_unitaryThree_component_normalizes_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
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
  obtain ⟨hCN,t,hti,htinner⟩ := local_unitaryThree_component_inner_inverter
    d h hab structural previous faithful earlier I hI C hC hout J hn hE hconj e
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
    have hze := HermitianForm.EvenProjectiveComparison.center_eq_bot J
      (by omega : 0 < n) hE hconj
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) at hh
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

/-- Source 14.7.41 point normality in the literal reduced local C L₁ T for the binary U₃ row. -/
theorem local_unitaryThree_reduced_point_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G)) :
    ((F.Li L 1).subgroupOf I).Normal := by
  obtain ⟨_,hCA,_,_⟩ := local_unitaryThree_component_normalizes_point
    d h hab structural previous faithful earlier I hI C hC hout J hn hE hconj e
  apply normal_subgroupOf_of_le_normalizer
  rw [hgen]
  exact sup_le (sup_le hCA (F.Li L 1).le_normalizer)
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural))

/-- The original outside component has three-rank one in the binary unitary-three row. -/
theorem local_unitaryThree_component_threeRank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : primeRank 3 C = 1 := by
  obtain ⟨hCN,_,hfix,_⟩ := local_unitaryThree_component_normalizes_point
    d h hab structural previous faithful earlier I hI C hC hout J hn hE hconj e
  let := hCN
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    have hze := HermitianForm.EvenProjectiveComparison.center_eq_bot J
      (by omega : 0 < n) hE hconj
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) at hh
    rw [hze,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  have hr := threeRank_le_one_of_cubic_core_centralizes A C hc hz hrI hfix
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup] at hr
  have hlo := local_component_threeRank d h hab structural previous faithful earlier I hI C hC
  omega


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
