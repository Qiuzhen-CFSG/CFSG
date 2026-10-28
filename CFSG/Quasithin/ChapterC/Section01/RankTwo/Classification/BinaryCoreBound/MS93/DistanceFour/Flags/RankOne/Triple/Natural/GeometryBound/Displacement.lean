module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Incidence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.Local
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.EndpointJoin
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius

/-!
# Both strict displacement inequalities on p.905

Assume the residual fixed quotient has index greater than four. The critical
commutator has order two in the binary specialization, excluding the source's
order-four alternative. The endpoint geometry constructs an actual index-three
endpoint--kernel join. If the first layer lies in the midpoint kernel, its
endpoint fixed index is at most two; the numerical rank-one bound contradicts
the excessive residual fixed index. For an escaping first layer, the midpoint
centralizer calculation bounds the same fixed index by its displacement index,
so that displacement must also exceed two. No natural factor is assumed.

The reverse argument constructs a transported escaping edge and its actual
index-three parabolic join from these forward inequalities. Its fixed-index
calculation proves the strict reverse radius inequality. The final theorem
assembles `FlagP905Displacement` with every endpoint and forward premise
discharged. The subsequent incidence-centrality argument and final fixed-index
bound belong to the source-theorem assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the two displacement paragraphs in (4.6.8), claim (1), printed p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- Conditional assembly of the two first-layer cases. The two extra
premises specify actual endpoint geometry, not a natural section or the
desired displacement inequality. They must be discharged in source assembly. -/
theorem FlagCriticalData.two_lt_firstLayer_displacement_of_endpoint_join
    (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (hexcess : 4 < (flagFixedPreimage source i).relIndex (V R (beta R))) (g : M)
    (hjoin : (Q R p.middle).relIndex (firstFlagLayer (R := R) g) ≤ 2 →
      Z R p.endpoint ≤ localFlagActor source i g ∧
        (Z R p.endpoint ⊔ localFlagKernel source i g).relIndex
          (localFlagActor source i g) = 3)
    (hcontained : firstFlagLayer (R := R) g ≤ Q R p.middle →
      (commutatorPreimage (firstFlagLayer (R := R) g) (Z R p.endpoint)
        (Z R (alpha R))).relIndex (firstFlagLayer (R := R) g) ≤ 2) :
    2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g) := by
  by_contra! hsmall
  obtain ⟨hEP, hi⟩ := hjoin hsmall
  have hKP : localFlagKernel source i g ≤ localFlagActor source i g :=
    map_mono (flagKernel_le source i)
  have hlarge := two_lt_local_fixedIndex_of_index_three source geometry
    common.large_distance i hkernel hexcess g
    (Z R p.endpoint ⊔ localFlagKernel source i g) (sup_le hEP hKP) hi
  by_cases htrapped : firstFlagLayer (R := R) g ≤ Q R p.middle
  · have hAN : Z R p.endpoint ≤ normalizer (Z R (alpha R)) := hEP.trans
      ((localFlagActor_le_stabilizer source i g).trans (Z_normalized R _))
    rw [localFlagFixedPreimage_join_kernel source geometry common early i hkernel g _ hAN]
      at hlarge
    exact (not_lt_of_ge (hcontained htrapped)) hlarge
  · have hn : localFlagActor source i g ≤ normalizer (firstFlagLayer (R := R) g) :=
      (map_mono (flagParabolic_normalizes_edgeRadius source geometry common.large_distance
        i hkernel)).trans (le_normalizer_map (MulAut.conj (embedM R g)).toMonoidHom)
    exact (not_lt_of_ge ((p.firstLayer_fixedIndex_le_displacement common early hkernel g
      htrapped (hEP.trans hn)).trans hsmall)) hlarge

/-- Strict first-layer displacement at every crossed incident flag. Both
geometric premises of the conditional assembly are proved by the endpoint
calculation, including the case where the layer lies in the midpoint kernel. -/
theorem FlagCriticalData.two_lt_firstLayer_displacement
    (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (hexcess : 4 < (flagFixedPreimage source i).relIndex (V R (beta R)))
    (d : M) (_hd : flagIncident source i 1 d)
    (hcross : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R))
    (g : M) (hinc : flagIncident source i g d)
    (hne : localFlagZ source i g ≠ localFlagZ source i 1) :
    2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g) :=
  p.two_lt_firstLayer_displacement_of_endpoint_join common early hkernel hexcess g
    (fun _ => p.endpoint_join common hb early hkernel d hcross g hinc hne)
    (p.contained_firstLayer_fixedIndex_le_two common hb early g)

/-- The displacement portion of MS93 (4.6.8), claim (1), p.905. The exact
contrary triple and excessive fixed index imply both strict displacement
inequalities, without any natural-section or later radius hypothesis. -/
theorem flagP905Displacement_of_fixedIndex_gt_four
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hexcess : 4 < (flagFixedPreimage source i).relIndex (V R (beta R))) :
    FlagP905Displacement source geometry i := by
  have hforward := fun p : FlagCriticalData source geometry i =>
    p.two_lt_firstLayer_displacement common hb early hkernel hexcess
  intro p
  exact ⟨p.two_lt_middle_radius_index_of_forward common hb early hkernel hbad hexcess hforward,
    hforward p⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
