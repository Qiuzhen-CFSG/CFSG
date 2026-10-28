module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Incidence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils

/-!
# Critical endpoint replacement and the p.905 symmetry assembly

The reverse displacement bound selects a radius-two generator escaping any
incident core intersection whose image modulo Q_alpha has order at most two.
Its escape forces distance four from alpha, giving a replacement critical
endpoint with the same bad midpoint. Actual core coverage then supplies a
second crossed incident flag with a different core intersection.

The assembly uses these endpoints and the strict displacements
against two conjugate first layers. Both commutators equal the full midpoint
edge commutator by `Symmetry.Algebra`; hence the finite pencil separation puts
it in the local center. `Symmetry.Pencils` constructs the finite incidence
facts from the source projection and its actual marked natural module.
`flagP905_symmetry` therefore proves centrality with only the two strict
displacement bounds left explicit. Their producer and the final index
contradiction stay with the parent incidence assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), claim (1), bottom half of printed p.905.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The reverse strict displacement selects a replacement critical endpoint
outside any subgroup whose image modulo Q_alpha has order at most two.
The midpoint and its noncentral triple remain the original ones. -/
theorem FlagCriticalData.exists_replacement_outside
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4)
    (J : Subgroup (FreeAmalgam R)) (hQJ : Q R (alpha R) ≤ J)
    (hJQ : J ≤ Q R (beta R)) (hsmall : (Q R (alpha R)).relIndex J ≤ 2)
    (hreverse : 2 < (Q R (alpha R)).relIndex (V R p.middle)) :
    ∃ p' : FlagCriticalData source geometry i,
      p'.middle = p.middle ∧ ¬ Z R p'.endpoint ≤ J := by
  have hescape : ¬ V R p.middle ≤ J := by
    intro h
    let : Finite (stabilizer R (beta R)) := finite_stabilizer R (beta R)
    let : Finite J := Finite.of_injective
      (inclusion (hJQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
    have hn : (Q R (alpha R)).relIndex J ≠ 0 :=
      ((Q R (alpha R)).subgroupOf J).index_ne_zero_of_finite
    have hi := relIndex_le_of_le_right h hn
    omega
  have hex : ∃ e : Vertex R, (cosetGraph R).dist e p.middle ≤ 2 ∧ ¬ Z R e ≤ J := by
    classical
    by_contra! hn
    apply hescape
    exact iSup_le fun e => iSup_le fun he => hn e he
  obtain ⟨e, he, heJ⟩ := hex
  have hmid : Z R p.middle ≤ Q R (alpha R) := by
    have hm := p.middle_le_firstLayer
    rw [firstFlagLayer, localConjugate_one] at hm
    exact hm.trans (edgeRadius_le_Q_alpha geometry common.large_distance)
  have h0 : (cosetGraph R).dist e p.middle ≠ 0 := by
    intro h
    have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp h
    exact heJ (heq ▸ hmid.trans hQJ)
  have h1 : (cosetGraph R).dist e p.middle ≠ 1 := by
    intro h
    have ha := adjacent_symm R ((cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp h))
    exact heJ ((edge_Z_le p.middle e p.middle_color ha).trans (hmid.trans hQJ))
  have he2 : (cosetGraph R).dist e p.middle = 2 := by omega
  have hecol : color R e = false :=
    (color_eq_of_dist_even R e p.middle (by rw [he2]; decide)).trans p.middle_color
  have henot : ¬ Z R e ≤ Q R (alpha R) := fun h => heJ (h.trans hQJ)
  have hlt : ¬ (cosetGraph R).dist e (alpha R) < 4 := by
    intro h
    apply henot
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e hecol)
    rw [geometry.distance_constant e hecol]
    change (cosetGraph R).dist e (alpha R) < geometry.b R
    omega
  have htri := (cosetGraph_connected R).dist_triangle
    (u := e) (v := p.middle) (w := alpha R)
  have hmid2 : (cosetGraph R).dist p.middle (alpha R) = 2 := by
    rw [SimpleGraph.dist_comm]
    exact p.first_distance
  have he4 : (cosetGraph R).dist e (alpha R) = 4 := by omega
  have hc : CriticalPair R e (alpha R) (geometry.exists_critical e hecol) := by
    refine ⟨?_, henot⟩
    rw [geometry.distance_constant e hecol]
    exact he4.trans hb.symm
  let p' : FlagCriticalData source geometry i := {
    middle := p.middle
    endpoint := e
    critical := common.critical_reverse e hecol (alpha R) rfl hc
    middle_neighbor := p.middle_neighbor
    first_distance := p.first_distance
    second_distance := (SimpleGraph.dist_comm ..).trans he2
    middle_triple := p.middle_triple }
  exact ⟨p', rfl, heJ⟩

/-- Reverse displacement and core coverage select two distinct incident
pencils crossed by critical endpoints with the same bad midpoint. -/
theorem FlagCriticalData.exists_separated_crossed_endpoints
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (hkernel : flagKernel source i = Q R (beta R))
    (hsmall : ∀ d : M, flagIncident source i 1 d →
      (Q R (alpha R)).relIndex
        (flagKernel source i ⊓ localFlagKernel source (!i) d) ≤ 2)
    (hreverse : 2 < (Q R (alpha R)).relIndex (V R p.middle)) :
    ∃ (p' : FlagCriticalData source geometry i) (d d' : M),
      p'.middle = p.middle ∧ flagIncident source i 1 d ∧ flagIncident source i 1 d' ∧
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) ∧
      ¬ Z R p'.endpoint ⊓ localFlagKernel source (!i) d' ≤ Q R (alpha R) ∧
      flagKernel source i ⊓ localFlagKernel source (!i) d ≠
        flagKernel source i ⊓ localFlagKernel source (!i) d' := by
  classical
  obtain ⟨d, hd, hcross⟩ := Incident.exists_delta2 source geometry common hb i hkernel p
  let J := flagKernel source i ⊓ localFlagKernel source (!i) d
  have hQJ : Q R (alpha R) ≤ J := by
    apply le_inf
    · simpa only [localFlagKernel, localConjugate_one] using
        Q_alpha_le_localFlagKernel source i 1
    · exact Q_alpha_le_localFlagKernel source (!i) d
  have hJQ : J ≤ Q R (beta R) := inf_le_left.trans_eq hkernel
  obtain ⟨p', hp', hpJ⟩ := p.exists_replacement_outside common hb J hQJ hJQ
    (hsmall d hd) hreverse
  obtain ⟨x, hx, hxJ⟩ := SetLike.not_le_iff_exists.mp hpJ
  have hxcore : x ∈ flagKernel source i :=
    hkernel ▸ p'.endpoint_le_edgeKernel hb hx
  obtain ⟨d', hd', hxd'⟩ := Incident.flagKernel_covered source i x hxcore
  refine ⟨p', d, d', hp', hd, hd', hcross, ?_, ?_⟩
  · intro h
    exact hxJ (hQJ (h ⟨hx, hxd'⟩))
  · intro he
    apply hxJ
    change x ∈ flagKernel source i ⊓ localFlagKernel source (!i) d
    rw [he]
    exact ⟨hxcore, hxd'⟩

/-- The symmetry argument with finite pencil facts explicit. Both critical
endpoints and both full-edge commutator identifications are constructed here;
`flagP905_symmetry` supplies the pencil facts from the source data. -/
theorem flagP905_symmetry_of_pencilFacts (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hpencils : FlagP905PencilFacts source i)
    (hdisplacement : FlagP905Displacement source geometry i)
    (p : FlagCriticalData source geometry i) :
    ⁅Z R p.middle, Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  obtain ⟨p', d, d', hp', hd, hd', hcross, hcross', hne⟩ :=
    p.exists_separated_crossed_endpoints common hb hkernel hpencils.intersection_index
      (hdisplacement p).1
  obtain ⟨g, g', hgd, hgd', hg, hg', hcentral⟩ := hpencils.separate d d' hd hd' hne
  have hdisp := (hdisplacement p).2 d hd hcross g hgd hg
  have hdisp' := (hdisplacement p').2 d' hd' hcross' g' hgd' hg'
  rw [hp'] at hdisp'
  exact (le_inf
    (le_inf (p.edge_commutator_le_localFlagZ common early hkernel g' hdisp')
      (p.edge_commutator_le_localFlagZ common early hkernel g hdisp))
    (edge_commutator_le_edgeZ_of_early early p.middle (beta R) p.middle_color
      (adjacent_symm R p.middle_neighbor))).trans hcentral

/-- The final incidence and symmetry implication in MS93 (4.6.8), claim (1),
printed p.905. The finite pencil facts are proved from the source data; only
the two displacement bounds remain as the explicit input of this implication.
The contrary triple is retained in the source interface, while the selected
critical data already contains its required midpoint specialization. -/
theorem flagP905_symmetry (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (_hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hdisplacement : FlagP905Displacement source geometry i)
    (p : FlagCriticalData source geometry i) :
    ⁅Z R p.middle, Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype :=
  flagP905_symmetry_of_pencilFacts source geometry common hb early i hkernel
    (flagP905PencilFacts source geometry common i hkernel) hdisplacement p

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
