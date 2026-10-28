module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSporadic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointAlternative

/-!
# Original local conclusions after the five sporadic point exclusions

The point-model sieve excludes M11, M12, J2, HS and Ru using the original
seven-section and marked two-block parabolic. Among the remaining covered
sporadic rows, M24 and J4 give the full large alternative, including Y ≤ K₁.
The three-space exclusion then constructs all four components and proves
V ≤ O₂(G₁). The actual point-control and generation-one consumers use this
construction with the earlier structural and ambient normalizer premises.

The original M22, M23 and He point rows remain explicit exclusions here;
qt-d-1251-local owns their removal, the other remaining point models, both
general normalizer containments and the quasisimple escape. The earlier
Structural1222At producer is qt-d-1222-source. Final exterior assembly,
including discharge of all source premises, belongs to qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3--4, 12.5.8(1), 12.5.11, pp.817--821.
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
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (name : ClassificationModels.SporadicName) (hj : name ≠ .j3)
    (h22 : name ≠ .m22) (h23 : name ≠ .m23) (hHe : name ≠ .he)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier))

include h hK hLK hN name hj h22 h23 hHe hm

/-- The covered sporadic point rows construct all original local components. -/
@[expose] def localComponentsOfSporadicPointSieve : LocalComponents s :=
  s.localComponentsOfPointAlternative h K hK hLK hN
    (s.local_point_component_alternative_of_sporadic_sieve h hK hLK hN name hj h22 h23 hHe hm)

/-- Point-core containment, with the actual component refinement constructed. -/
theorem seed_le_point_core_of_sporadic_point_sieve : V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_core_of_point_alternative h hK hLK hN
    (s.local_point_component_alternative_of_sporadic_sieve h hK hLK hN name hj h22 h23 hHe hm)

/-- The point-control consumer retains only the earlier structural input and
both pending ambient normalizer containments. -/
theorem pointControl_of_sporadic_point_sieve
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    PointControl s.marking :=
  s.pointControl_of_point_alternative h structural hK hLK hN
    (s.local_point_component_alternative_of_sporadic_sieve h hK hLK hN name hj h22 h23 hHe hm)
    hG₃ hG₆

/-- The generation-one consumer uses the same original component and quotient maps. -/
theorem generation_ne_one_of_sporadic_point_sieve
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  s.generation_ne_one_of_point_alternative h structural hK hLK hN
    (s.local_point_component_alternative_of_sporadic_sieve h hK hLK hN name hj h22 h23 hHe hm)
    hG₃ hG₆ hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
