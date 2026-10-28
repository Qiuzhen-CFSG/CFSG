module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalPlane
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitEdge
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer

/-!
# The critical plane has edge index four

The reversed critical pair transports the distance-two image calculation to
`Q alpha` and gives relative index two for `Z c` over its intersection with
`Q alpha`. The maximal-plane identity identifies that intersection with the
critical plane. The native edge layer has index eight, so the subgroup index
multiplication formula gives the required index four over the common edge
layer. The final wrappers retain the literal characteristic replacement.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii) and (3.6), printed
pp.867 and 871.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

theorem critical_reverse_image_order_two
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl)) :
    (Q R (alpha R)).relIndex (Z R c) = 2 := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := critical_reverse R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl (by change 0 < s.geometry.b R; omega) c hc0 hc
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R hc0
  have hcol : color R (act R g⁻¹ (mVertex R g)) = false := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have hnew := (criticalPair_act_iff R g⁻¹ (mVertex R g) (alpha R)
    (s.geometry.exists_critical (mVertex R g) hc0)
    (s.geometry.exists_critical (act R g⁻¹ (mVertex R g)) hcol)).mpr hrev
  have hcrit : CriticalPair R (alpha R) (mVertex R g⁻¹)
      (s.geometry.exists_critical (alpha R) rfl) := by
    simpa only [alpha,act_mVertex,mul_inv_cancel,one_mul] using hnew
  have htwo := s.critical_image_order_two_of_core_large h t hfull hb hlarge hcrit
  have he := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (Q R (mVertex R g⁻¹)) (Z R (alpha R)) (MulAut.conj g⁻¹).injective
  rw [←Q_act,←Z_act] at he
  simpa only [alpha,act_mVertex,inv_mul_cancel,one_mul] using he.trans htwo

theorem criticalPlane_edge_relIndex_four
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    (Z R b).relIndex (criticalPlane R c b) = 4 := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := s.critical_reverse_image_order_two h t hfull hb hlarge hc
  have hedge := s.edge_Z_index_eight_at h t hfull hc0 hcb
  have hplane := s.criticalPlane_eq_opposite_inf_Q h t hfull hb hlarge hc hab hcb
  have hzb : Z R b ≤ criticalPlane R c b :=
    s.edge_Z_le_criticalPlane hc hab hcb
  have hzc : criticalPlane R c b ≤ Z R c :=
    criticalPlane_le_opposite c b
  have hmid : (criticalPlane R c b).relIndex (Z R c) = 2 := by
    rw [hplane, inf_relIndex_left]
    exact hrev
  have hmul := relIndex_mul_relIndex (Z R b) (criticalPlane R c b) (Z R c)
    hzb hzc
  rw [hmid, hedge] at hmul
  omega

theorem criticalPlane_edge_strict
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    Z R b < criticalPlane R c b := by
  have hindex := s.criticalPlane_edge_relIndex_four h t hfull hb hlarge hc hab hcb
  have hle : Z R b ≤ criticalPlane R c b := s.edge_Z_le_criticalPlane hc hab hcb
  exact lt_of_le_of_ne hle (by
    intro heq
    rw [heq] at hindex
    norm_num at hindex)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The actual characteristic replacement has critical plane index four over its
common-edge Z-layer. -/
theorem reducedSource_criticalPlane_edge_relIndex_four (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    (hlarge : ¬ core r.radical (alpha r.radical) ≤
      (frattini (Q r.radical (alpha r.radical))).map
        (Q r.radical (alpha r.radical)).subtype ⊔ X r.radical (alpha r.radical))
    {c b : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hab : Adjacent r.radical (alpha r.radical) b)
    (hcb : Adjacent r.radical c b) :
    (Z r.radical b).relIndex (criticalPlane r.radical c b) = 4 :=
  Source.criticalPlane_edge_relIndex_four ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hlarge hc hab hcb

/-- The actual characteristic replacement has a strict critical plane over its
common-edge Z-layer. -/
theorem reducedSource_criticalPlane_edge_strict (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    (hlarge : ¬ core r.radical (alpha r.radical) ≤
      (frattini (Q r.radical (alpha r.radical))).map
        (Q r.radical (alpha r.radical)).subtype ⊔ X r.radical (alpha r.radical))
    {c b : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hab : Adjacent r.radical (alpha r.radical) b)
    (hcb : Adjacent r.radical c b) :
    Z r.radical b < criticalPlane r.radical c b :=
  Source.criticalPlane_edge_strict ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hlarge hc hab hcb

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
