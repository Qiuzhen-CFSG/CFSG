module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage

/-!
# Forward saturation and an actual distinct incident flag

If every first-color fixed subgroup in an opposite pencil were the same,
both marked parabolics would normalize Z_beta. Their generation and local
neighbor transitivity would force Z_alpha = Z_beta, contradicting index two.
Thus the forward displacement hypothesis applies to an actual distinct fixed
subgroup. Its index greater than two fills Q_beta/Q_middle, of order four.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (1), printed
p.905, immediately before the reverse displacement argument.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem fixed_conjugate (source : LocalSource L R) (i : Bool) (g : M) :
    localFlagZ source i g = localConjugate (localFlagZ source i 1) g := by
  let e := MulAut.conj (embedM R g)
  have hz : (Z R (alpha R)).map e.toMonoidHom = Z R (alpha R) := by
    apply mem_normalizer_iff_map_conj_eq.mp
    apply Z_normalized R _
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  have hc : (centralizer (flagKernel source i : Set (FreeAmalgam R))).map e.toMonoidHom =
      centralizer ((flagKernel source i).map e.toMonoidHom : Set (FreeAmalgam R)) := by
    apply le_antisymm (map_centralizer_le_centralizer_image _ _)
    intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
  simp only [localFlagZ, localFlagKernel, localConjugate_one]
  change Z R (alpha R) ⊓ centralizer ((flagKernel source i).map e.toMonoidHom :
    Set (FreeAmalgam R)) = (Z R (alpha R) ⊓ centralizer (flagKernel source i :
      Set (FreeAmalgam R))).map e.toMonoidHom
  rw [map_inf _ _ e.toMonoidHom e.injective, hz, hc]

private theorem base_fixed_normalized (source : LocalSource L R) (i : Bool) :
    flagParabolic source i ≤ normalizer (localFlagZ source i 1) := by
  rintro _ ⟨g, hg, rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  change localConjugate (localFlagZ source i 1) g = _
  rw [← fixed_conjugate]
  simpa only [one_mul] using localFlagZ_right_mul source i 1 g hg

variable [Finite M]

private theorem exists_opposite_moving (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    ∃ g ∈ parabolic source.projection source.flag (!i),
      localFlagZ source i g ≠ localFlagZ source i 1 := by
  classical
  by_contra! hn
  have hopp : flagParabolic source (!i) ≤ normalizer (localFlagZ source i 1) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (fixed_conjugate source i g).symm.trans (hn g hg)
  have hgen : flagParabolic source i ⊔ flagParabolic source (!i) = stabilizer R (alpha R) := by
    rw [flagParabolic, flagParabolic, ← Subgroup.map_sup]
    have hp := parabolic_generation source.projection source.projection_surjective source.flag
    have hp' : parabolic source.projection source.flag i ⊔
        parabolic source.projection source.flag (!i) = ⊤ := by
      cases i
      · exact hp
      · exact (sup_comm _ _).trans hp
    rw [hp', ← MonoidHom.range_eq_map, alpha, stabilizer_m_base]
    rfl
  have hnorm := sup_le (base_fixed_normalized source i) hopp
  rw [hgen] at hnorm
  have hfixed : localFlagZ source i 1 = Z R (beta R) := by
    simp only [localFlagZ, localFlagKernel, localConjugate_one, hkernel]
    exact (Early.edge_Z_eq_fixed common _ _ rfl (base_adjacent R)).symm
  rw [hfixed] at hnorm
  have hZA : Z R (alpha R) ≤ Z R (beta R) := by
    rw [Z, if_pos (show color R (alpha R) = false from rfl)]
    apply iSup_le
    intro b
    apply iSup_le
    intro hb
    obtain ⟨g, hg, he⟩ := stabilizer_transitive_neighbors R (alpha R) (base_adjacent R) hb
    rw [← he, edgeOmega_act]
    change (Z R (beta R)).map (MulAut.conj g⁻¹).toMonoidHom ≤ Z R (beta R)
    exact (mem_normalizer_iff_map_conj_eq.mp (hnorm ((stabilizer R _).inv_mem hg))).le
  have hi := early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
  rw [relIndex_eq_one.mpr hZA] at hi
  omega

/-- Every actual incident pencil contains a first-color fixed subgroup different from the base one. -/
theorem exists_incident_distinct_fixed (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) :
    ∃ g : M, flagIncident source i g d ∧ localFlagZ source i g ≠ localFlagZ source i 1 := by
  obtain ⟨a, ha, hane⟩ := exists_opposite_moving source geometry common early i hkernel
  obtain ⟨m, hm, hdm⟩ := hd
  simp only [inv_one, one_mul] at hm
  refine ⟨m*a, ⟨m*a, ?_, ?_⟩, ?_⟩
  · simp only [inv_mul_cancel]; exact one_mem _
  · simpa only [← mul_assoc] using (parabolic source.projection source.flag (!i)).mul_mem hdm ha
  · intro he
    apply hane
    have hmfix : localFlagZ source i m = localFlagZ source i 1 := by
      simpa only [one_mul] using localFlagZ_right_mul source i 1 m hm
    rw [fixed_conjugate source i (m*a), localConjugate_mul,
      ← fixed_conjugate source i a] at he
    rw [← hmfix, fixed_conjugate source i m] at he
    exact map_injective (MulAut.conj (embedM R m)).injective he

/-- One strict first-layer displacement fills the four-element midpoint quotient. -/
theorem FlagCriticalData.radius_sup_middle_kernel_of_layer
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (g : M)
    (hdisp : 2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    V R (alpha R) ⊔ Q R p.middle = Q R (beta R) := by
  let T := Q R (beta R)
  let Q₀ := (Q R p.middle).subgroupOf T
  let E := (V R (alpha R)).subgroupOf T
  have hQT : Q R p.middle ≤ T := Q_le_adjacent_h R rfl (adjacent_symm R p.middle_neighbor)
  have hET : V R (alpha R) ≤ T :=
    (V_le_Q geometry common.large_distance _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R))
  let : Q₀.Normal := normal_subgroupOf_of_le_normalizer
    ((show T ≤ stabilizer R p.middle from fun _ hx => hx.2 _ p.middle_neighbor).trans
      (Q_normalized R _))
  let := finite_stabilizer R (alpha R)
  let : Finite (V R (alpha R)) := Finite.of_injective
    (inclusion (geometry.V_local _ rfl common.large_distance)) (inclusion_injective _)
  have hgt : 2 < Q₀.relIndex E := by
    rw [relIndex_subgroupOf hET]
    exact hdisp.trans_le (relIndex_le_of_le_right (firstFlagLayer_le_radius g) index_ne_zero_of_finite)
  have hQi : Q₀.index = 4 := early.edge_Q_index _ _ p.middle_color
    (adjacent_symm R p.middle_neighbor)
  have hd : Q₀.relIndex E ∣ 4 := hQi ▸ Q₀.relIndex_dvd_index_of_normal E
  have hf := Nat.mem_divisors.mpr ⟨hd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  have hi : Q₀.relIndex E = 4 := by omega
  have hm := relIndex_mul_index (show Q₀ ≤ E ⊔ Q₀ from le_sup_right)
  rw [relIndex_sup_right, hi, hQi] at hm
  have htop : E ⊔ Q₀ = ⊤ := index_eq_one.mp (by omega)
  have hh := congrArg (Subgroup.map T.subtype) htop
  dsimp only [E, Q₀] at hh
  rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hET,
    map_subgroupOf_eq_of_le hQT, ← MonoidHom.range_eq_map, range_subtype] at hh

/-- The forward hypotheses provide the full image of V_alpha at the midpoint. -/
theorem FlagCriticalData.radius_sup_middle_kernel_of_forward
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (hforward : ∀ d : M, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ∀ g : M, flagIncident source i g d →
      localFlagZ source i g ≠ localFlagZ source i 1 →
      2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    V R (alpha R) ⊔ Q R p.middle = Q R (beta R) := by
  obtain ⟨d, hd, hcross⟩ := Incident.exists_delta2 source geometry common hb i hkernel p
  obtain ⟨g, hg, hne⟩ := exists_incident_distinct_fixed source geometry common early i hkernel d hd
  exact p.radius_sup_middle_kernel_of_layer common early g (hforward d hd hcross g hg hne)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
