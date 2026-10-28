module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.ComponentIntersection
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.LinearParabolic
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MiddleRecognition

/-!
# The linear larger-component branch of point-core containment

The actual intersection M₁* ∩ K₁* has Sylow index 63. When the intrinsic
component quotient is PSL₅(2), transport the intersection through the
original core-quotient equivalence and a linear marking. Sylow-overgroup
recognition identifies its image as a two- or three-space stabilizer in
an actual basis. Thus the checked tensor-radical obstruction applies to
the normal elementary eight-group supplied by failure of V ≤ O₂(G₁).

This discharges the linear row without an assumed parabolic isomorphism.
The application to LocalComponents leaves only the M₂₄ and J₄ rows;
those exclusions and construction of the remaining component alternatives
stay with qt-d-1251-local. Final exterior assembly is qt-d-1251-source.

Source: Aschbacher--Smith, the embedding discussion in 12.5.3, printed
p.818, and the proof of 12.5.8(1), printed p.820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private def linearFiveEquiv {A : Type*} [Group A] (h : ClassicalGroup.IsPSL A 5 2) :
    A ≃* BinaryLinear.OuterCyclic.LinearGroup 5 := Classical.choice (by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))⟩)

/-- The original intersection is an actual middle flag stabilizer under a component
marking; the equality specifies the embedding in the linear model. -/
theorem pointComponentParabolic_linear_flag {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    ∃ (e : s.pointCoreImage K ≃* BinaryLinear.OuterCyclic.LinearGroup 5)
      (b : BinaryLinear.FiveFlagGeometry.FiveBasis),
      (s.pointComponentParabolic K).map e.toMonoidHom =
        BinaryLinear.FiveFlagGeometry.flagStabilizer b {1} ∨
      (s.pointComponentParabolic K).map e.toMonoidHom =
        BinaryLinear.FiveFlagGeometry.flagStabilizer b {2} := by
  let e := (s.pointComponentCoreEquivImage hK hn).symm.trans (linearFiveEquiv hm)
  obtain ⟨S,hS,hi⟩ := s.pointComponentParabolic_sylow_index hK hn hLK hY
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A := (s.pointComponentParabolic K).map e.toMonoidHom
  have hRA : (R : Subgroup _) ≤ A := map_mono hS
  have hidx : (R : Subgroup _).relIndex A = 63 := by
    change ((S : Subgroup (s.pointCoreImage K)).map e.toMonoidHom).relIndex
      ((s.pointComponentParabolic K).map e.toMonoidHom) = 63
    rw [relIndex_map_map_of_injective _ _ e.injective]
    exact hi
  obtain ⟨b,hb⟩ := BinaryLinear.FiveFlagGeometry.middle_flag_of_sylow_index R A hRA hidx
  exact ⟨e,b,hb⟩

/-- The parabolic comparison is constructed from the source containment data. -/
theorem pointComponentParabolic_linear_equiv {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    Nonempty (s.pointComponentParabolic K ≃* Representation.SL5ExteriorSquare.parabolic 2) := by
  obtain ⟨e,b,he | he⟩ := s.pointComponentParabolic_linear_flag hK hn hLK hY hm
  all_goals
    exact ⟨((e.subgroupMap _).trans (MulEquiv.subgroupCongr he)).trans
      (BinaryLinear.FiveFlagGeometry.middle_flag_equiv b _
        (by first | exact Or.inl rfl | exact Or.inr rfl)).some⟩

/-- The linear larger-component branch of source 12.5.8(1), with no assumed
parabolic comparison or seed-core containment. -/
theorem seed_le_point_core_of_linear_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  obtain ⟨B,hnB,hpB,hcB⟩ := s.pointComponentParabolic_seed_normal_eight h hLK hf
  let e := (s.pointComponentParabolic_linear_equiv hK hn hLK hY hm).some
  let := hnB
  let := hpB
  let N := B.map e.toMonoidHom
  let : N.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  apply BinaryLinear.FiveParabolicRadical.matrix_no_normal_eight N ((IsElementaryAbelian.isPGroup 2 B).map e.toMonoidHom)
  exact (card_map_of_injective e.injective).trans hcB

/-- The linear row is discharged on the original chosen component. -/
theorem seed_le_point_core_of_linear_row
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (hm : ClassicalGroup.IsPSL (c.K 1 ⧸ pCore 2 (c.K 1)) 5 2) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  exact hf (s.seed_le_point_core_of_linear_component h
    (c.component 1 (Or.inl rfl)).1 (c.normal 1 (Or.inl rfl))
    (c.contains 1 (Or.inl rfl)) (s.point_core_failure_large c hf).2 hm)

/-- Only the two sporadic models remain under failure of point-core containment. -/
theorem point_core_failure_sporadic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (hf : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* Janko4.Model) :=
  (s.point_core_failure_large c hf).1.resolve_left
    (fun hm => hf (s.seed_le_point_core_of_linear_row h c hm))
end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
