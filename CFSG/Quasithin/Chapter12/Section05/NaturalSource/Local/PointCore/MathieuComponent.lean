module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.LinearComponent
public import Theory.Mathieu.M24.LocalGeometry.EightNormalizers

/-!
# The actual Mathieu point-component exclusion

The literal intersection M₁* ∩ K₁* contains a Sylow subgroup of K₁* of
relative index 63. Failure of point-core containment gives a normal elementary
eight in this same intersection. Transport through the actual component core
quotient places both in native M₂₄. The checked normal-eight catalogue and
its octad/trio geometry exclude this configuration, with no assumed ambient
parabolic comparison. Together with the linear and radical rows, only J₄
remains under failure of point-core containment.

The remaining J₄ row and construction of LocalComponents belong to
qt-d-1251-local; qt-d-1251-source owns the final exterior exclusion.
Source: Aschbacher--Smith, 12.5.3 and 12.5.8(1), printed pp.818, 820.
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

/-- The Mathieu larger-component row, using the original embedded parabolic. -/
theorem seed_le_point_core_of_mathieu_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  obtain ⟨S,hS,hi⟩ := s.pointComponentParabolic_sylow_index hK hn hLK hY
  obtain ⟨B,hnB,hpB,hcB⟩ := s.pointComponentParabolic_seed_normal_eight h hLK hf
  let e := (s.pointComponentCoreEquivImage hK hn).symm.trans hm.some
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A := (s.pointComponentParabolic K).map e.toMonoidHom
  have hRA : (R : Subgroup _) ≤ A := map_mono hS
  have hidx : (R : Subgroup _).relIndex A = 63 := by
    change ((S : Subgroup (s.pointCoreImage K)).map e.toMonoidHom).relIndex
      ((s.pointComponentParabolic K).map e.toMonoidHom) = 63
    rw [relIndex_map_map_of_injective _ _ e.injective]
    exact hi
  let ea : s.pointComponentParabolic K ≃* A := e.subgroupMap (s.pointComponentParabolic K)
  let E : Subgroup A := B.map ea.toMonoidHom
  let := hnB
  let := hpB
  have hnE : E.Normal := Subgroup.Normal.map hnB ea.toMonoidHom ea.surjective
  exact @Sporadic.Mathieu.M24LocalGeometry.EightNormalizers.no_normal_eight_of_sylow_index R A hRA hidx E hnE
    (IsElementaryAbelian.map _) ((card_map_of_injective ea.injective).trans hcB)

/-- The Mathieu row is discharged on the original chosen point component. -/
theorem seed_le_point_core_of_mathieu_row
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (hm : Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* Sporadic.Mathieu.M24)) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  exact hf (s.seed_le_point_core_of_mathieu_component h
    (c.component 1 (Or.inl rfl)).1 (c.normal 1 (Or.inl rfl))
    (c.contains 1 (Or.inl rfl)) (s.point_core_failure_large c hf).2 hm)

/-- J₄ is the sole remaining model under failure of point-core containment. -/
theorem point_core_failure_janko4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s)
    (hf : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    Nonempty ((c.K 1 ⧸ pCore 2 (c.K 1)) ≃* Janko4.Model) :=
  (s.point_core_failure_sporadic h c hf).resolve_left
    (fun hm => hf (s.seed_le_point_core_of_mathieu_row h c hm))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
