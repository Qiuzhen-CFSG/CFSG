module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognition
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Recovering the component image from the full join action

The original component is normal in LT and acts nontrivially on its chosen
module. If LT fills GL(V), simplicity of binary GL in degree at least three
forces the component image to fill it too. The coordinate comparison then
transports fullness to the original chosen subspace, and through both literal
quotients L/O₂(L) and L/C_L(V).

No irreducibility or natural-module marking is assumed. These are the image
comparisons used to select the natural row in Aschbacher–Smith 12.2.20,
printed p.802, from 12.2.2(3), p.795.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem binaryLinear_simple {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hd : 3 ≤ Module.finrank (ZMod 2) W) :
    IsSimpleGroup (BinaryLinear.GL W) := by
  let n := Module.finrank (ZMod 2) W
  let e : W ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin]
      rfl)
  let E : BinaryLinear.GL W ≃* BinaryLinear.OuterCyclic.LinearGroup n :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
          (BinaryLinear.OuterCyclic.Space n)))
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hd
  let : IsSimpleGroup (BinaryLinear.OuterCyclic.LinearGroup n) :=
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  exact E.isSimpleGroup

theorem chosen_component_full_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    letI := D.elementary
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map (chosenJoinLinearAction D hT) = ⊤ := by
  let := D.elementary
  let J := L ⊔ (T : Subgroup G)
  let a := chosenJoinLinearAction D hT
  let K := (L.subgroupOf J).map a
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : K.Normal := Subgroup.Normal.map inferInstance a (MonoidHom.range_eq_top.mp hf)
  have hK : K ≠ ⊥ := by
    intro he
    apply D.centralAction_ne_one
    apply MonoidHom.ext
    intro l
    apply D.actionCentralizer_le_centralAction_ker
    intro v hv
    have ha : a ⟨l, (le_sup_left : L ≤ J) l.property⟩ = 1 := mem_bot.mp (he ▸
      (mem_map_of_mem a
        (show (⟨l, (le_sup_left : L ≤ J) l.property⟩ : J) ∈ L.subgroupOf J from l.property)))
    have hh := congrArg (fun e : BinaryLinear.GL (Additive V) =>
      ((e (Additive.ofMul ⟨v, hv⟩)).toMul : G)) ha
    change (l : G) * v * (l : G)⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let : IsSimpleGroup (BinaryLinear.GL (Additive V)) :=
    binaryLinear_simple (chosen_finrank_ge_three h D)
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal K inferInstance).resolve_left hK

theorem chosen_linearAction_surjective_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    Function.Surjective ((LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) D.space).toMonoidHom.comp D.chosenAction.asGroupHom) := by
  let := D.elementary
  let e : D.space ≃ₗ[ZMod 2] Additive V :=
    (MulEquiv.toAdditiveRight D.spaceEquiv).toLinearEquiv (ZMod.map_smul _)
  intro a
  let b : Additive V ≃ₗ[ZMod 2] Additive V := e.symm.trans (a.trans e)
  have hb : b ∈ (L.subgroupOf (L ⊔ (T : Subgroup G))).map
      (chosenJoinLinearAction D hT) := by
    rw [chosen_component_full_of_join_full h D hT hf]
    exact mem_top _
  obtain ⟨l, hl, he⟩ := hb
  refine ⟨⟨l, hl⟩, ?_⟩
  apply LinearEquiv.ext
  intro v
  apply e.injective
  have he' := congrArg (fun z : BinaryLinear.GL (Additive V) => z (e v)) he
  have hc : e (D.chosenAction ⟨l, hl⟩ v) = chosenJoinLinearAction D hT l (e v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction ⟨l, hl⟩ v)) : G) =
      (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹
    rw [D.spaceEquiv_apply, D.spaceEquiv_apply]
    rfl
  change e (D.chosenAction ⟨l, hl⟩ v) = e (a v)
  rw [hc, he']
  simp [b]

theorem chosen_quotientLinearAction_surjective_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    Function.Surjective ((LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) D.space).toMonoidHom.comp D.quotientAction.asGroupHom) := by
  intro a
  obtain ⟨l, hl⟩ := chosen_linearAction_surjective_of_join_full h D hT hf a
  exact ⟨QuotientGroup.mk' (pCore 2 L) l, hl⟩

theorem chosen_faithfulLinearAction_surjective_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    letI := D.actionCentralizer_normal
    Function.Surjective ((LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) D.space).toMonoidHom.comp D.faithfulAction.asGroupHom) := by
  let := D.actionCentralizer_normal
  intro a
  obtain ⟨l, hl⟩ := chosen_linearAction_surjective_of_join_full h D hT hf a
  exact ⟨QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l, hl⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
