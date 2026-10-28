module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneConstituent
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.CubicSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.SourceConstituent
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Solvability of the original residual Thompson subgroup

The full B.5 classification and the literal Sylow-fixed point exclude all
rank-one rows except a natural SL₂ section. Order comparison excludes the
L₃(2) actor there. The genuine earlier13.3.2 implication then supplies an
alternating-five constituent on the original component; its injection into
the same central section contradicts the cubic fixed-vector calculation.
Thus there is no C-component and the original Thompson subgroup is solvable.

Only the original earlier structural, uniqueness, faithful group and A₅
module implications remain. No decomposition, group model, solvability or
centralizer conclusion is added to the source hypotheses.
Source: Aschbacher–Smith14.7.67(4), printed p.1070;14.3.4 and13.3.2.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer ResidualNormalizer.Components
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

private theorem not_linearTwo_psl3 (k : BinaryField)
    (e : Matrix.SpecialLinearGroup (Fin 2) k.Carrier ≃* Matrix.PSL3Two.PSL) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.card_sl_two,Matrix.PSL3Two.card_PSL] at hc
  let q := Nat.card k.Carrier
  change q * (q^2-1)=168 at hc
  by_cases hq : q ≤ 5
  · interval_cases q <;> norm_num at hc
  · have hq6 : 6 ≤ q := by omega
    have hsq : 36 ≤ q^2 := by nlinarith
    have hh : 6*35 ≤ q*(q^2-1) := Nat.mul_le_mul hq6 (by omega)
    omega

/-- The surviving SL₂ row has the original A₅ quotient, not L₃(2). -/
theorem residual_component_five_of_linearTwo
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (k : BinaryField)
    (e : d.residualGlobalComponent hs B ≃* Matrix.SpecialLinearGroup (Fin 2) k.Carrier) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  let q := (residualComponentOffenderEquiv hB).trans (d.residualOffenderGlobalEquiv earlier hs hB)
  rcases (d.residual_component_group_classification earlier hs hB).1 with h | h
  · exact h
  · obtain ⟨a⟩ := h
    exact (not_linearTwo_psl3 k ((q.trans e).symm.trans a)).elim

/-- Transport an actual alternating constituent to the same global component action. -/
theorem residual_global_no_linearTwo_of_constituent
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B U : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hU : U ≤ E F) (model : Chapter6.Source.IsConjugationModel B U Chapter6.Source.a5Module) :
    let := (d.residualSpan_reduced hs).elementary
    ∀ s : MovedSection (d.residualGlobalAction hs) (d.residualGlobalComponent hs B),
    ∀ k : BinaryField, ¬ Nonempty (ActionEquiv
      (s.action.comp (d.residualGlobalComponent hs B).subtype) (linearNatural k 2)) := by
  let := (d.residualSpan_reduced hs).elementary
  dsimp only
  intro s k he
  obtain ⟨e⟩ := he
  obtain ⟨a,b,hm⟩ := model
  let q := (residualComponentOffenderEquiv hB).trans (d.residualOffenderGlobalEquiv earlier hs hB)
  let f := (a.symm.trans q).toMonoidHom
  have hUY : U ≤ Y L F := hU.trans (d.residualSpan_le_D.trans le_sup_left)
  let i : BinaryPermutation.natural (Fin 5) →+ Additive ((E F).subgroupOf (Y L F)) := {
    toFun := fun v => Additive.ofMul ⟨⟨b.symm (Multiplicative.ofAdd v),
      hUY (b.symm (Multiplicative.ofAdd v)).property⟩,
      hU (b.symm (Multiplicative.ofAdd v)).property⟩
    map_zero' := by
      apply Subtype.ext
      apply Subtype.ext
      change (b.symm 1 : G) = 1
      exact congrArg Subtype.val b.symm.map_one
    map_add' v w := by
      apply Subtype.ext
      apply Subtype.ext
      change (b.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : G) =
        (b.symm (Multiplicative.ofAdd v) : G) * (b.symm (Multiplicative.ofAdd w) : G)
      exact congrArg Subtype.val (map_mul b.symm (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  have hi : Function.Injective i := by
    intro v w hv
    have hb : b.symm (Multiplicative.ofAdd v) = b.symm (Multiplicative.ofAdd w) := by
      apply Subtype.ext
      exact congrArg (fun x : Additive ((E F).subgroupOf (Y L F)) => ((x.toMul : Y L F) : G)) hv
    exact b.symm.injective hb
  apply RankOneConstituent.not_linearTwo_of_alternating_injection s k e f
    (a.symm.trans q).injective i hi
  intro x v
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 B) (a.symm x)
  have hx : a (QuotientGroup.mk' (pCore 2 B) g) = x := by rw [hg]; exact a.apply_symm_apply x
  have hq : f x = d.residualComponentToGlobal earlier hs hB g := by
    change q (a.symm x) = _
    rw [←hg]
    rfl
  rw [hq]
  apply Eq.trans ?_ (d.residualComponentToGlobal_equivariant earlier hs hB g (i v))
  apply Subtype.ext
  apply Subtype.ext
  have h := hm g (b.symm (Multiplicative.ofAdd v))
  rw [hx,MulEquiv.apply_symm_apply] at h
  exact h.trans (d.residualRepresentation_apply hs (inclusion (hB.1.trans J_le_Y) g) (i v)).symm

include d in
/-- The actual Thompson subgroup has no C-component. The only retained
module input is the genuine earlier 13.3.2 alternating-five implication. -/
theorem residual_thompson_no_component_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) : False := by
  let hs := (d.residual_intersections structural uniqueness).2.2.2
  let := (d.residualSpan_reduced hs).elementary
  obtain ⟨c⟩ := d.residual_global_component_classification earlier hs hB
  obtain ⟨k,⟨e⟩⟩ := d.residualGlobalComponent_linearTwo earlier hs hB c
  have hfive := d.residual_component_five_of_linearTwo earlier hs hB k e.groupEquiv
  obtain ⟨U,hU,hUE,hm,hcard⟩ := d.residual_component_alternating_constituent_of_source
    structural uniqueness earlier modules hB hfive
  have hBE : B ≤ normalizer (E F : Set G) :=
    (hB.1.trans J_le_Y).trans d.residual_Y_normalizes_E
  exact d.residual_global_no_linearTwo_of_constituent earlier hs hB
    (hUE.trans (le_normalizer_iff_commutator_le_left.mp hBE)) hm c.sectionData k ⟨e⟩

include d in
/-- Solvability in 14.7.67 is constructed from the original component and
constituent classification, without a decomposition or solvability premise. -/
theorem residual_thompson_solvable_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    Group.IsSolvable (J L F) := by
  by_contra hn
  obtain ⟨B,hB⟩ := exists_isCComponent_of_not_isSolvable hn
  apply d.residual_thompson_no_component_of_source structural uniqueness earlier modules
    (B := B.map (J L F).subtype)
  refine ⟨map_subtype_le B,?_⟩
  have he : (B.map (J L F).subtype).subgroupOf (J L F) = B :=
    comap_map_eq_self_of_injective (J L F).subtype_injective B
  rwa [he]

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
