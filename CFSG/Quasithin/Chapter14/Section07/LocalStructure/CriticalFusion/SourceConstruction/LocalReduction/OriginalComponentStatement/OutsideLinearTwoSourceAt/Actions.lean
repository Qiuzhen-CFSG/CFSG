module
public import Theory.SpecificGroups.SL2.LiftedBorelInner
public import Theory.GroupTheory.CubicInverterInnerComponent
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Borel

/-!
# Outside binary rank-one actions at the actual original Sylow

This is the At port of the binary rank-one outside-component action. The
component is explicitly normal, while Structural1222At and Theorem12213At
refer to the same original group and Sylow. Borel fixation and the lifted
inner-action calculation produce the actual component quotient actions; the reduced local then
normalizes the point residual.

Source: Aschbacher–Smith 14.7.41, printed p.1061, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
open Chapter12.Section08 CriticalFusion.Source OutsideProjectiveAt
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
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (I : Subgroup G) (C : Subgroup I) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) (P : Sylow 2 C)
    (hP : (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C)
    (x : I)
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
  apply Matrix.ProjectiveSpecialLinearGroup.quotient_inner_of_borelResidual_fixed hE hn e P
    (MulAut.conjNormal x) hxP
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

/-- In the outside-component binary L₂ row, the point and its original
inverter induce inner automorphisms of the literal component two-core quotient. -/
theorem local_linearTwo_component_inner_actions_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) :
    ((F.Li L 1).subgroupOf I).map (normalQuotientAction C (pCore 2 C)) ≤
        MulAut.innerSubgroup (C ⧸ pCore 2 C) ∧
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        (∀ y : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural)
              t.property.1⟩ y = y⁻¹) ∧
        normalQuotientAction C (pCore 2 C)
          ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩ ∈
            MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hnA : (S : Subgroup I) ≤ normalizer (A : Set I) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li
      (h.sylow_normalizes_at structural) hx) (a : G)
  have hnot : ¬ A ≤ C := by
    intro hh
    apply hout
    have hh' := map_mono (f := I.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAI] at hh'
  have hnorm := cubic_supplement_normalizes_sylow_inf A C S hp hc hnA hnot
  change A ⊔ (S : Subgroup I) ≤
    normalizer (↑((S : Subgroup I) ⊓ C) : Set I) at hnorm
  have hpres (x : I) (hx : x ∈ A ⊔ (S : Subgroup I)) :
      (P : Subgroup C).map (MulAut.conjNormal x).toMonoidHom = P := by
    apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective
      (f := (MulAut.conjNormal x : MulAut C).toMonoidHom)
      (K := (P : Subgroup C)) (MulAut.conjNormal x : MulAut C).injective).symm)
    rintro _ ⟨c,hc,rfl⟩
    rw [hP] at hc ⊢
    exact ((mem_normalizer_iff.mp (hnorm hx) (c : I)).mp ⟨hc,c.property⟩).1
  obtain ⟨_,_,hAB,t,htB,hti,htfix⟩ := component_borel_fixed_actions_at
    d h hab structural previous faithful earlier I hI C hout
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    apply component_actor_inner_of_fixed_borel hE hn I C e P hP a
      (hpres a (mem_sup_left ha))
    dsimp only
    intro b hb
    exact hAB (commutator_mem_commutator ha hb)
  · refine ⟨t,hti,?_⟩
    apply component_actor_inner_of_fixed_borel hE hn I C e P hP
      ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
      (hpres _ (mem_sup_right t.property.1))
    dsimp only
    intro b hb
    have hh := (coreAction_eq_one_iff _ _).mp htfix ⟨b,hb⟩
    exact mem_map_of_mem _ hh


/-- The actual component normalizes the point and admits an original-Sylow centralizing inverter. -/
theorem local_linearTwo_component_normalizes_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) :
    C.map I.subtype ≤ normalizer (F.Li L 1 : Set G) ∧
      (F.Li L 1).subgroupOf I ≤ (normalQuotientAction C (pCore 2 C)).ker ∧
      ∃ s : (T : Subgroup G),
        normalQuotientAction C (pCore 2 C)
          ⟨s,F.sylow_le_of_mem_Hz hI s.property⟩ = 1 ∧
        ∀ y : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨s,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural)
              s.property⟩ y = y⁻¹ := by
  obtain ⟨_,t,hti,htinner⟩ := local_linearTwo_component_inner_actions_at
    d h hab structural previous faithful earlier I hI C hout hE hn e
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hnorm : (S : Subgroup I) ≤ normalizer (A : Set I) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li
      (h.sylow_normalizes_at structural) hx) (a : G)
  have hnot : ¬ A ≤ C := by
    intro hh
    apply hout
    have hh' := map_mono (f := I.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAI] at hh'
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    apply e.injective
    rw [map_one]
    have hez : e z ∈ center PSL(2,E) := by
      apply mem_center_iff.mpr
      intro x
      obtain ⟨y,rfl⟩ := e.surjective x
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz y)
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot,mem_bot] using hez
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  have htiA (a : I) (ha : a ∈ A) : tI*a*tI⁻¹*a ∈ A.pCoreIn 2 := by
    rw [show A = (F.Li L 1).subgroupOf I from rfl,pCoreIn_subgroupOf 2 _ I hAI]
    let a' : F.Li L 1 := ⟨a,ha⟩
    let t' : normalizer (F.Li L 1 : Set G) :=
      ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) t.property.1⟩
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
  refine ⟨hCA',hfix,⟨s,hs⟩,hsk,?_⟩
  intro y
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) y
  rw [coreAction_mk]
  apply eq_inv_of_mul_eq_one_left
  rw [←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hh := hsi (⟨a,hAI a.property⟩ : I) a.property
  rw [show A = (F.Li L 1).subgroupOf I from rfl,pCoreIn_subgroupOf 2 _ I hAI] at hh
  exact (mem_map_iff_mem (F.Li L 1).subtype_injective).mp hh

/-- Source 14.7.41 point normality in the literal reduced local C L₁ T for the binary L₂ row. -/
theorem local_linearTwo_reduced_point_normal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E))
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G)) :
    ((F.Li L 1).subgroupOf I).Normal := by
  obtain ⟨hCA,_,_⟩ := local_linearTwo_component_normalizes_point_at
    d h hab structural previous faithful earlier I hI C hout hE hn e
  apply normal_subgroupOf_of_le_normalizer
  rw [hgen]
  exact sup_le (sup_le hCA (F.Li L 1).le_normalizer)
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural))


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
