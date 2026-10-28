module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.RadiusCentrality
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointFixed

/-!
# Radius bounds for the actual symplectic replacement

The original natural-six source and its characteristic replacement supply the
literal graph geometry. At distance greater than four, the shared radius
abelianity theorem gives MS93 (5.2)(ii)--(iii). At distance four, only centrality
of the radius commutator remains an input; the derived and endpoint bounds
follow without any further module or path hypotheses.

The final applications retain the original SourceData, replacement radical
and quotient conventions. No splitting of the full elementary layer is used.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed pp.914--915.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- Centrality is the sole radius premise needed for the remaining two bounds. -/
theorem radius_bounds_of_central (hb : 2 < s.geometry.b R)
    {a : Vertex R} (ha : color R a = false)
    (hc : ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)))
    (a' c : Vertex R) :
    ⁅V R a,V R a⁆ ≤ X R a ∧
    ⁅⁅X R a' ⊓ Q R a,V R a ⊓ Q R c⁆,V R a ⊓ Q R c⁆ = ⊥ :=
  ⟨SectionFive.radius_derived_le_X R s.geometry hb ha hc,
    SectionFive.critical_radius_triple_commutator R hc⟩

/-- At distance greater than four the actual source supplies centrality too. -/
theorem radius_bounds_of_four_lt (hb : 4 < s.geometry.b R)
    {a : Vertex R} (ha : color R a = false) (a' c : Vertex R) :
    ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) ∧
    ⁅V R a,V R a⁆ ≤ X R a ∧
    ⁅⁅X R a' ⊓ Q R a,V R a ⊓ Q R c⁆,V R a ⊓ Q R c⁆ = ⊥ := by
  have hc := SectionFive.radius_commutator_central_of_four_lt R s.geometry hb ha
  exact ⟨hc,SectionFive.radius_derived_le_X R s.geometry (by omega) ha hc,
    SectionFive.critical_radius_triple_commutator R hc⟩

end Source
namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T)

/-- Literal reduced-source deduction, leaving exactly the distance-four
centrality assertion as a premise. -/
theorem reducedSource_radius_bounds (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : 2 < ((originalSource d h).reduce c).geometry.b c.radical)
    (hc : ⁅V c.radical (alpha c.radical),Q c.radical (alpha c.radical)⁆ ≤
      centralizer (V c.radical (alpha c.radical) : Set (FreeAmalgam c.radical)))
    (a' e : Vertex c.radical) :
    ⁅V c.radical (alpha c.radical),V c.radical (alpha c.radical)⁆ ≤
      X c.radical (alpha c.radical) ∧
    ⁅⁅X c.radical a' ⊓ Q c.radical (alpha c.radical),
        V c.radical (alpha c.radical) ⊓ Q c.radical e⁆,
      V c.radical (alpha c.radical) ⊓ Q c.radical e⁆ = ⊥ :=
  Source.radius_bounds_of_central ((originalSource d h).reduce c) hb rfl hc a' e

/-- The original characteristic replacement discharges all radius premises
when its critical distance is greater than four. -/
theorem reducedSource_radius_bounds_of_four_lt (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : 4 < ((originalSource d h).reduce c).geometry.b c.radical)
    (a' e : Vertex c.radical) :
    ⁅V c.radical (alpha c.radical),Q c.radical (alpha c.radical)⁆ ≤
      centralizer (V c.radical (alpha c.radical) : Set (FreeAmalgam c.radical)) ∧
    ⁅V c.radical (alpha c.radical),V c.radical (alpha c.radical)⁆ ≤
      X c.radical (alpha c.radical) ∧
    ⁅⁅X c.radical a' ⊓ Q c.radical (alpha c.radical),
        V c.radical (alpha c.radical) ⊓ Q c.radical e⁆,
      V c.radical (alpha c.radical) ⊓ Q c.radical e⁆ = ⊥ :=
  Source.radius_bounds_of_four_lt ((originalSource d h).reduce c) hb rfl a' e

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
