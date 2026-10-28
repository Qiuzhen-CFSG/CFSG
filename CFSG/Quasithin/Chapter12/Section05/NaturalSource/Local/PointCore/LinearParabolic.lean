module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.ParabolicImage
public import Theory.SpecificGroups.BinaryLinear.FiveParabolicRadical

/-!
# The linear parabolic obstruction in the original point-core quotient

If the literal M₁* is isomorphic to the two-space parabolic in SL₅(2),
the original V lies in O₂(G₁). Otherwise its image supplies a normal
elementary subgroup of order eight, contradicting the parabolic's
irreducible order-sixty-four radical.

The input is an actual subgroup isomorphism, not merely a model for K₁*.
Constructing it from the original larger-component embedding remains
with qt-d-1251-local. The Mathieu and Janko exclusions also remain open.
Final exterior assembly belongs to qt-d-1251-source.

Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The tensor-radical obstruction in the linear parabolic row, applied to the
literal point-core quotient. Recognizing this image inside a larger component
is still required by the local source assembly. -/
theorem seed_le_point_core_of_linear_parabolic_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : s.pointCoreImage (s.marking.Mi 1) ≃*
      Representation.SL5ExteriorSquare.parabolic 2) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  obtain ⟨hn, hp, hc⟩ := s.pointCoreImage_seed_normal_eight h hf
  let B := (s.pointCoreImage V).subgroupOf (s.pointCoreImage (s.marking.Mi 1))
  let : B.Normal := hn
  let : IsElementaryAbelian 2 B := hp
  let N := B.map e.toMonoidHom
  let : N.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hh := BinaryLinear.FiveParabolicRadical.matrix_no_normal_eight N
    ((IsElementaryAbelian.isPGroup 2 B).map e.toMonoidHom)
  apply hh
  exact (card_map_of_injective e.injective).trans hc

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
