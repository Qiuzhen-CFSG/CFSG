module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.NonSmall
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.SpanGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch

/-!
# The full two-span construction over Z_alpha

Choose an actual critical segment. The genuine small-branch producer and
square obstruction exclude its small intersection. SpanRecognition gives
its marked dual quotient and midpoint-kernel containment. The span is
noncentral in the radius group by the starred intersection identity, so
an actual noncommuting neighbor rho can be selected. Critical shifting,
the small-branch exclusion and the same recognition give the second span.

The two abelian spans intersect in Z_alpha and generate the starred group
by their literal indices. Their common-marked quotient maps assemble to a
surjective two-dual map with kernel exactly Z_alpha. Surjectivity on each
moving span also proves VStar = Z_alpha sup core_alpha. This construction
needs no exact-U core factor. The independent SpanRecognition contract
remains explicit for the source-theorem assembly owner to discharge.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(5) and the final
paragraph, printed pp.911--912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
private theorem midpoint_span_not_central (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    ⁅V R (alpha R), orbitSpan s.middle⁆ ≠ ⊥ := by
  intro h
  have hc := RankOne.midpoint_nu common radius hb s
  have hV := orbitSpan_le_radius s.middle hc.1.le
  have hB : orbitSpan s.middle ≤ B R (alpha R) (geometry.Z_normal (alpha R)) := by
    rw [radius.B_eq_center (alpha R) rfl]
    intro x hx
    refine ⟨⟨x, hV hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp h y.property x hx).symm
  apply RankOne.midpoint_span_not_le_Z common radius hb s
  rw [← radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)]
  exact le_inf (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R) hc) hB

/-- Two actual critical midpoints, their common-marked quotients, and the
literal intersection and generation of their abelian full spans. -/
structure FullSpanPair where
  first : CriticalSegment geometry
  second : CriticalSegment geometry
  first_nu : nu R geometry (alpha R) first.middle
  second_nu : nu R geometry (alpha R) second.middle
  second_adjacent : Adjacent R (beta R) second.middle
  noncommuting : ⁅Z R second.middle, orbitSpan first.middle⁆ ≠ ⊥
  first_abelian : IsMulCommutative (orbitSpan first.middle)
  second_abelian : IsMulCommutative (orbitSpan second.middle)
  first_quotient : RankOne.SpanQuotient source common first.middle
  second_quotient : RankOne.SpanQuotient source common second.middle
  intersection : orbitSpan first.middle ⊓ orbitSpan second.middle = Z R (alpha R)
  generation : VStar R geometry (alpha R) (beta R) =
    orbitSpan first.middle ⊔ orbitSpan second.middle

/-- Select the second source midpoint and reapply the same recognition after
excluding its small branch with the actual single-quotient producer. -/
theorem exists_fullSpanPair (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (hrec : RankOne.SpanRecognition source common) :
    Nonempty (FullSpanPair source common) := by
  obtain ⟨s⟩ := exists_criticalSegment geometry hb
  have hs := s.not_smallIntersection source geometry common radius hb
  obtain ⟨hsQ, ⟨q⟩, hindex⟩ := hrec s hs
  have hc := RankOne.midpoint_nu common radius hb s
  have hab : IsMulCommutative (orbitSpan s.middle) :=
    orbitSpan_commutative_of_le_kernel (geometry := geometry) s.middle s.middle_color hsQ
  obtain ⟨rho, hrho, hadj, hne⟩ := exists_noncentral_neighbor source common radius
    (beta R) (base_adjacent R) (orbitSpan s.middle)
    (orbitSpan_le_radius s.middle hc.1.le) (orbitSpan_normalized s.middle)
    (midpoint_span_not_central source common radius hb s)
  obtain ⟨t, ht⟩ := criticalSegment_through_of_noncommuting source common hb s.middle rho
    ((cosetGraph R).dist_comm.trans s.first_distance)
    ((cosetGraph R).dist_comm.trans hrho.1) hne
  have htns : ¬ t.SmallIntersection := by
    have hn := shifted_nonSmall_of_singleQuotients source common radius hb
      (singleQuotient_of_smallIntersection source geometry common radius hb)
      s.middle rho ((cosetGraph R).dist_comm.trans s.first_distance)
      ((cosetGraph R).dist_comm.trans hrho.1) hne
    simpa only [CriticalSegment.SmallIntersection, ht] using hn
  subst rho
  obtain ⟨htQ, ⟨r⟩, _⟩ := hrec t htns
  have htab : IsMulCommutative (orbitSpan t.middle) :=
    orbitSpan_commutative_of_le_kernel (geometry := geometry) t.middle t.middle_color htQ
  have hinter := q.intersect s.first_distance t.first_distance htab hne
  have hgen := q.star_generation radius r hc hrho htab hne hindex
  exact ⟨⟨s, t, hc, hrho, hadj, hne, hab, htab, q, r, hinter, hgen⟩⟩

/-- The source two-span construction gives the actual two-dual quotient by Z,
and the starred subgroup is generated by Z and the actual commutator core.
The only recognition input is the independent full-span contract. -/
theorem fullSpans (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (hrec : RankOne.SpanRecognition source common) :
    Nonempty (StarDoubleQuotient source common) ∧
      VStar R geometry (alpha R) (beta R) = Z R (alpha R) ⊔ core R (alpha R) := by
  obtain ⟨p⟩ := exists_fullSpanPair source common radius hb hrec
  refine ⟨starDoubleQuotient_of_spans radius p.first.middle p.second.middle
    p.first.first_distance p.second.first_distance p.first_quotient p.second_quotient
    p.generation p.intersection, ?_⟩
  apply le_antisymm
  · rw [p.generation, p.first_quotient.span_eq_Z_sup_moving p.first.first_distance,
      p.second_quotient.span_eq_Z_sup_moving p.second.first_distance]
    exact sup_le (sup_le le_sup_left ((RankOne.movingSpan_le_core geometry common.large_distance
      p.first.middle p.first.first_distance).trans le_sup_right))
      (sup_le le_sup_left ((RankOne.movingSpan_le_core geometry common.large_distance
        p.second.middle p.second.first_distance).trans le_sup_right))
  · exact sup_le
      (Flags.Z_le_star geometry radius.toEarlyFacts common.large_distance _ _ rfl (base_adjacent R))
      (SmallBranch.core_le_star source geometry common radius _ _ rfl (base_adjacent R))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
