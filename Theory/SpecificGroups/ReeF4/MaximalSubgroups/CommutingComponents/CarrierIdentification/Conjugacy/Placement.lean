module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Conjugacy.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Conjugacy.Placement.Reduction
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Reducing maximal-subgroup placement to the two product geometries

The complete relative component family generates a subgroup normalized by M.
Apply local recognition to its full ambient normalizer. In the Suzuki case,
the required containment follows. In the linear case, a strict proper overgroup
of the linear-pair normalizer would also strictly contain the conjugate of M,
contradicting maximality.

This proves the finite-group assembly but leaves both geometric inputs open.
In particular, it does not assert `suzukiPairPlacement` without premises.
The final unconditional assembly belongs here after those inputs are proved.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E, §2.2 and Proposition 2.3,
including the symplectic overgroup immediately following that proposition.
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

/-- The component family and maximality discharge every finite-group premise
once local semisimple recognition and the proper linear overgroup are proved. -/
theorem suzukiPairPlacement_of_semisimpleRecognition_of_linearOvergroup
    (hrecognition : SemisimpleNormalizerRecognition)
    (hlinear : LinearPairProperOvergroup) : SuzukiPairPlacement := by
  intro m hm M hM _hsolv hR L K hL hK hne _hc
  obtain ⟨g, hg | hg⟩ := hrecognition m hm (componentFamily M)
    (componentFamily_isCommutingSimpleFamily hR hL hK hne)
  · exact ⟨g, (Subgroup.map_mono (le_normalizer_componentFamily M)).trans hg⟩
  · have hMN := (Subgroup.map_mono (le_normalizer_componentFamily M)).trans hg
    have hmax : IsCoatom (M.map (MulAut.conj g).toMonoidHom) :=
      ((MulAut.conj g).mapSubgroup.isCoatom_iff M).mpr hM
    obtain ⟨H, hNH, hH⟩ := hlinear m hm
    exact (hH (hmax.2 H (lt_of_le_of_lt hMN hNH))).elim

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
