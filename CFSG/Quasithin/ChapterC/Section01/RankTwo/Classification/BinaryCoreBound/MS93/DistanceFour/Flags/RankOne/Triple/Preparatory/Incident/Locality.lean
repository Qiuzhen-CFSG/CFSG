module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs

/-!
# Local normalization for the incident flag calculation

Left translation of the actual parabolic cosets preserves incidence.
Transporting every fixed preimage proves that the full untilded actor
normalizes the second flag layer. The first parabolic core lies in every
incident opposite actor, so the critical endpoint also normalizes that layer.

Consequently the literal subgroup Y = [U_delta intersect Q_middle,Z_endpoint]
lies in U_delta intersect Z_middle. Its second containment uses the earlier
commutator bound at the midpoint. The displacement equivalence fixes the
orientation of the relative index in the binary specialization; it does
not assert that the second layer escapes Q_middle.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the local flag definitions on printed p.905 and the Y calculation
in the proof of (4.6.8), claim (4), on p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Left translating both cosets preserves incidence. -/
theorem flagIncident_left (source : LocalSource L R) (i : Bool) (a g h : M) :
    flagIncident source i (a * g) (a * h) ↔ flagIncident source i g h := by
  constructor
  · rintro ⟨m, hm, hn⟩
    refine ⟨a⁻¹ * m, ?_, ?_⟩
    · simpa only [mul_inv_rev, mul_assoc] using hm
    · simpa only [mul_inv_rev, mul_assoc] using hn
  · rintro ⟨m, hm, hn⟩
    refine ⟨a * m, ?_, ?_⟩
    · simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hm
    · simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hn

/-- All local coordinate changes preserve the source quotient denominator. -/
theorem localConjugate_Z (a : M) :
    localConjugate (Z R (alpha R)) a = Z R (alpha R) := by
  have ha : embedM R a ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨a, rfl⟩
  exact mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) ha)

/-- Simultaneous conjugation sends every incident fixed preimage to the
corresponding fixed preimage, hence sends its span into the translated span. -/
theorem secondFlagLayer_conjugate_le (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a h : M) :
    localConjugate (secondFlagLayer source i h) a ≤ secondFlagLayer source i (a * h) := by
  let f := (MulAut.conj (embedM R a)).toMonoidHom
  change (⨆ g : M, ⨆ (_ : flagIncident source i g h),
    commutatorPreimage (firstFlagLayer (R := R) g)
      (localFlagKernel source (!i) h) (Z R (alpha R))).map f ≤ _
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro g
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro hg
  apply le_iSup_of_le (a * g)
  apply le_iSup_of_le ((flagIncident_left source i a g h).mpr hg)
  apply le_commutatorPreimage
  · exact (map_mono (commutatorPreimage_le _ _ _)).trans_eq
      (localConjugate_mul (V R (beta R)) a g).symm
  · have hb := map_mono (f := f)
      (commutator_commutatorPreimage_le (firstFlagLayer (R := R) g)
        (localFlagKernel source (!i) h) (Z R (alpha R))
        ((firstFlagLayer_le_radius g).trans
          ((geometry.V_local _ rfl hlarge).trans (Z_normalized R _))))
    rw [map_commutator] at hb
    have hK : (localFlagKernel source (!i) h).map f =
        localFlagKernel source (!i) (a * h) :=
      (localConjugate_mul (flagKernel source (!i)) a h).symm
    have hZ : (Z R (alpha R)).map f = Z R (alpha R) := localConjugate_Z a
    rwa [hK, hZ] at hb

/-- The span of incident fixed preimages still centralizes the local core
modulo Z_alpha, in the genuine relative quotient. -/
theorem secondFlagLayer_commutator_le_Z (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool) (h : M) :
    ⁅secondFlagLayer source i h, localFlagKernel source (!i) h⁆ ≤ Z R (alpha R) := by
  have hVZ := (geometry.V_local (alpha R) rfl hlarge).trans (Z_normalized R _)
  have hs : secondFlagLayer source i h ≤
      commutatorPreimage (V R (alpha R)) (localFlagKernel source (!i) h) (Z R (alpha R)) := by
    apply iSup_le
    intro g
    apply iSup_le
    intro _
    apply le_commutatorPreimage
    · exact (commutatorPreimage_le _ _ _).trans (firstFlagLayer_le_radius g)
    · exact commutator_commutatorPreimage_le _ _ _ ((firstFlagLayer_le_radius g).trans hVZ)
  exact (commutator_mono hs le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hVZ)

/-- The second layer is normalized by the full untilded actor at its flag. -/
theorem secondFlagLayer_normalized (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (h : M) :
    localFlagActor source (!i) h ≤ normalizer (secondFlagLayer source i h) := by
  apply le_normalizer_iff.mpr
  rintro x ⟨y, ⟨p, hp, rfl⟩, rfl⟩ u hu
  have hc := secondFlagLayer_conjugate_le source geometry hlarge i (h * p * h⁻¹) h
  have he : h * p * h⁻¹ * h = h * p := by group
  rw [he, secondFlagLayer_right_mul source i h p hp] at hc
  have hh := hc (mem_map_of_mem (MulAut.conj (embedM R (h * p * h⁻¹))).toMonoidHom hu)
  change embedM R (h * p * h⁻¹) * u * (embedM R (h * p * h⁻¹))⁻¹ ∈
    secondFlagLayer source i h at hh
  change (embedM R h * embedM R p * (embedM R h)⁻¹) * u *
    (embedM R h * embedM R p * (embedM R h)⁻¹)⁻¹ ∈ secondFlagLayer source i h
  simpa only [map_mul, map_inv] using hh

/-- Each first core lies in the opposite parabolic for the same flag. -/
theorem flagKernel_le_oppositeActor [Finite M] (source : LocalSource L R) (i : Bool) :
    flagKernel source i ≤ flagParabolic source (!i) := by
  rw [← pairing_selectedCore source i]
  apply map_mono
  exact (inf_le_left : RankOnePairing.selectedCore (pairingExtension source) i ≤
    RankOnePairing.commonSylow (pairingExtension source)).trans
      ((RankOnePairing.commonSylow_le_localParabolic (pairingExtension source) (!i)).trans_eq
        (pairing_parabolic source (!i)))

/-- The first core is contained in every full actor incident to the first flag. -/
theorem flagKernel_le_incidentActor [Finite M] (source : LocalSource L R) (i : Bool)
    (h : M) (hinc : flagIncident source i 1 h) :
    flagKernel source i ≤ localFlagActor source (!i) h := by
  obtain ⟨m, hm, hhm⟩ := (flagIncident_one_iff source i h).mp hinc
  have he : localFlagActor source (!i) m = localFlagActor source (!i) h := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source (!i) h (h⁻¹ * m) hhm
  have hc : localConjugate (flagKernel source i) m = flagKernel source i :=
    mem_normalizer_iff_map_conj_eq.mp
      (flagKernel_normalized source i (mem_map_of_mem (embedM R) hm))
  exact hc.symm.le.trans ((map_mono (flagKernel_le_oppositeActor source i)).trans_eq he)

/-- The critical endpoint is in the full actor at every incident opposite flag. -/
theorem endpoint_le_incidentActor [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 4) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) (h : M) (hinc : flagIncident source i 1 h) :
    Z R p.endpoint ≤ localFlagActor source (!i) h :=
  (p.endpoint_le_edgeKernel hb).trans
    (hkernel ▸ flagKernel_le_incidentActor source i h hinc)

/-- The endpoint normalizes the actual second layer, using the full local actor. -/
theorem endpoint_normalizes_secondLayer [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 4) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) (h : M) (hinc : flagIncident source i 1 h) :
    Z R p.endpoint ≤ normalizer (secondFlagLayer source i h) :=
  (endpoint_le_incidentActor source geometry hb i hkernel p h hinc).trans
    (secondFlagLayer_normalized source geometry (by omega) i h)

/-- The literal source Y lies in U_delta intersect Z_middle. The first
containment uses endpoint normalization; the second uses the distance-two
Z-generator and the earlier commutator bound at the midpoint. -/
theorem endpoint_commutator_le [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) (h : M) (hinc : flagIncident source i 1 h) :
    ⁅secondFlagLayer source i h ⊓ Q R p.middle, Z R p.endpoint⁆ ≤
      secondFlagLayer source i h ⊓ Z R p.middle := by
  have hEV : Z R p.endpoint ≤ V R p.middle := by
    apply le_iSup_of_le p.endpoint
    apply le_iSup_of_le (show (cosetGraph R).dist p.endpoint p.middle ≤ 2 by
      rw [SimpleGraph.dist_comm]; exact p.second_distance.le)
    exact le_rfl
  apply le_inf
  · exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (endpoint_normalizes_secondLayer source geometry hb i hkernel p h hinc))
  · rw [commutator_comm]
    exact (commutator_mono hEV inf_le_right).trans
      (early.commutator_le_Z p.middle p.middle_color)

/-- Finiteness comes from the finite original vertex stabilizer, despite
working in the infinite free amalgam. -/
theorem secondFlagLayer_finite [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool) (h : M) :
    Finite (secondFlagLayer source i h) := by
  let := finite_stabilizer R (alpha R)
  exact Finite.of_injective (inclusion ((secondFlagLayer_le_radius source i h).trans
    (geometry.V_local _ rfl hlarge))) (inclusion_injective _)

/-- In the binary case the displacement bound has exactly the source orientation:
it is equivalent to the second layer escaping the midpoint kernel. -/
theorem displacement_iff [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool) (h : M)
    (c : Vertex R) :
    2 ≤ (Q R c).relIndex (secondFlagLayer source i h) ↔
      ¬ secondFlagLayer source i h ≤ Q R c := by
  let := secondFlagLayer_finite source geometry hlarge i h
  have hpos : (Q R c).relIndex (secondFlagLayer source i h) ≠ 0 :=
    ((Q R c).subgroupOf (secondFlagLayer source i h)).index_ne_zero_of_finite
  rw [← relIndex_eq_one]
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
