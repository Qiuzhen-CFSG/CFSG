module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Similarity
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceInvolutions
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits

/-!
# The two Mathieu involution classes in the original normalizer span

The constructed isomorphism of the span with native M₂₄ transfers its
certified two-class involution coverage. The original 21-point rectangle
fusion locus separates z from the chosen rank-two rectangle element, so
these exact representatives give both classes regardless of the chosen
recognition map. The shared Sylow subgroup supplies ambient coverage, and
the same separation proves that the span controls all its involution fusion.

This supplies the two class-intersection identities used in Aschbacher,
*Sporadic Groups* (1994), 40.6 and 41.1, pp.219–220. The internal rectangle
import unfolds only the existing marked second representative. No ambient
generation or second-centralizer hypothesis is used here.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer Sporadic.Mathieu

private theorem two_classes_of_mathieu_equiv {H : Type*} [Group H] (e : H ≃* M24)
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : ¬ IsConj a b)
    (x : H) (hx : orderOf x = 2) : IsConj a x ∨ IsConj b x := by
  have back {u v : H} (h : IsConj (e u) (e v)) : IsConj u v := by
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h
  have ha' := M24InvolutionCentralizers.involution_classes (e a) ((e.orderOf_eq a).trans ha)
  have hb' := M24InvolutionCentralizers.involution_classes (e b) ((e.orderOf_eq b).trans hb)
  have hx' := M24InvolutionCentralizers.involution_classes (e x) ((e.orderOf_eq x).trans hx)
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact (hab (back (ha'.symm.trans hb'))).elim
  · exact hx'.imp (fun h => back (ha'.symm.trans h)) (fun h => back (hb'.symm.trans h))
  · exact hx'.symm.imp (fun h => back (ha'.symm.trans h)) (fun h => back (hb'.symm.trans h))
  · exact (hab (back (ha'.symm.trans hb'))).elim

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)
include D

/-- The 21-element fusion locus separates the original marked representatives. -/
theorem secondPoint_not_fused : ¬ IsConj z (planeSecondPoint F) := by
  change ¬ IsConj z (PlaneTensor.element F 34)
  rw [plane_fusion_iff_pure F D.orientation.1]
  decide

/-- Source 40.6 inside the actual generated subgroup, with the original two representatives. -/
theorem normalizerSpan_two_involution_classes
    (x : normalizerSpan F) (hx : orderOf x = 2) :
    IsConj (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) x ∨
      IsConj (planeSecondPoint (normalizerSpanMarking F)) x := by
  obtain ⟨e⟩ := normalizerSpan_equiv F D
  exact two_classes_of_mathieu_equiv e (normalizerSpanMarking F).point_orderOf
    (planeSecondPoint_order _) (secondPoint_not_fused _ (normalizerSpanLocalData F D)) x hx

/-- The common ambient Sylow gives precisely the same two involution classes in G. -/
theorem two_involution_classes
    (x : G) (hx : orderOf x = 2) : IsConj z x ∨ IsConj (planeSecondPoint F) x := by
  obtain ⟨y, hy⟩ := involution_conjugate_into_normalizerSpan F x hx
  have hyo : orderOf y = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hy
    have h := (MulAut.conj g).orderOf_eq x
    change orderOf (g*x*g⁻¹) = orderOf x at h
    rw [hg,Subgroup.orderOf_coe,hx] at h
    exact h
  rcases normalizerSpan_two_involution_classes F D y hyo with hz | ht
  · have hh := ((normalizerSpan F).subtype.map_isConj hz).trans hy.symm
    change IsConj ((overgroupPoint (normalizerSpan F)
      (point_centralizer_le_normalizerSpan F) : normalizerSpan F) : G) x at hh
    exact Or.inl (by simpa only [overgroupPoint_val] using hh)
  · have hh := (normalizerSpan F).subtype.map_isConj ht
    change IsConj ((planeSecondPoint (normalizerSpanMarking F) : normalizerSpan F) : G)
      (y : G) at hh
    rw [normalizerSpan_secondPoint_val] at hh
    exact Or.inr (hh.trans hy.symm)

/-- The literal generated subgroup controls ambient fusion of all its involutions. -/
theorem normalizerSpan_involution_fusion
    (a b : normalizerSpan F) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : IsConj (a : G) (b : G)) : IsConj a b := by
  have hz := secondPoint_not_fused F D
  have cast_point : ((normalizerSpan F).subtype
      (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F))) = z := overgroupPoint_val _ _
  have cast_second : ((normalizerSpan F).subtype
      (planeSecondPoint (normalizerSpanMarking F))) = planeSecondPoint F :=
    normalizerSpan_element_val F 34
  rcases normalizerSpan_two_involution_classes F D a ha with hza | hta <;>
    rcases normalizerSpan_two_involution_classes F D b hb with hzb | htb
  · exact hza.symm.trans hzb
  · have hh := ((normalizerSpan F).subtype.map_isConj hza).trans
      (hab.trans ((normalizerSpan F).subtype.map_isConj htb).symm)
    rw [cast_point, cast_second] at hh
    exact (hz hh).elim
  · have hh := ((normalizerSpan F).subtype.map_isConj hzb).trans
      (hab.symm.trans ((normalizerSpan F).subtype.map_isConj hta).symm)
    rw [cast_point, cast_second] at hh
    exact (hz hh).elim
  · exact hta.symm.trans htb

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
