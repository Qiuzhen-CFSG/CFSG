module
public import Theory.SpecificGroups.SL2.LiftedBorelInner
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideComponentCentralResidual

/-!
# The binary rank-one outside-component actions in source 14.7.41

Let C be any actual C-component of an original local I, with L₁ outside C,
and suppose C/O₂(C) is binary PSL₂ over a field of order at least four.
Then L₁ and the original point inverter in T∩L act by inner automorphisms
on this literal quotient. The proof constructs relative normality and the
original Sylow intersection, transports its Borel residual through the
component inclusion, and applies the lifted-Borel innerness detector to
B_C = B. Both the two-core and the conjugation action are retained.

This is the rank-one outer-action step, not the full source dichotomy or
its subsequent tensor-module and ambient exclusions. The other Lie-type
rows, L₁-normality and all-component 14.7.47 assembly remain to be proved.
The existing earlier structural, faithful-classification and 14.7.10
inputs retain their producers; no inner-action or Borel-fixation premise
is added to this original-source application.

Source: Aschbacher–Smith 14.7.41, printed p.1061, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_eq_one_iff)
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
theorem local_linearTwo_component_inner_actions
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
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) :
    ∃ hCN : C.Normal, letI := hCN
      ((F.Li L 1).subgroupOf I).map (normalQuotientAction C (pCore 2 C)) ≤
        MulAut.innerSubgroup (C ⧸ pCore 2 C) ∧
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
  refine ⟨hNC,?_⟩
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  have hnA : (S : Subgroup I) ≤ normalizer (A : Set I) := by
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
  obtain ⟨_,_,hAB,t,htB,hti,htfix⟩ := local_component_borel_fixed_actions
    d h hab structural previous faithful earlier I hI C hC hout
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
