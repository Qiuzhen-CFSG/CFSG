module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Locality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.FixedSpaces.Pencil
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction


/-!
# Incident fixed spaces and the source delta0 selection

The actual cores at two distinct incident neighbors generate the full first
parabolic. Their common fixed space therefore fixes the full actor modulo
Z_alpha; restricting to G_alpha gives the literal relative quotient statement.
The model calculation and its lift retain the original marked projection.

In the binary specialization the earlier edge index makes the midpoint image
modulo Z_alpha at most a line. At most one of the three second layers contains
the midpoint, since two would contradict its bad triple. At most one core
contains the critical endpoint, since pairwise core intersections are Q_alpha.
A remaining neighbor gives the corrected four-part source selection. This
stronger binary argument needs no extra premise about the supplied natural
section. The existing conditional lemmas and legacy records remain unchanged.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), printed p.906, between claims (3) and (4) of (4.6.8). In particular,
the line beginning “Hence we can choose” reads
[Z_(alpha+2) intersect U_delta0, L_delta1] <= Z_alpha.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem commutator_join_le {G : Type*} [Group G]
    (A D E P N : Subgroup G) (hD : D ≤ P) (hE : E ≤ P)
    (hPN : P ≤ normalizer N) (hd : ⁅A, D⁆ ≤ N) (he : ⁅A, E⁆ ≤ N) :
    ⁅A, D ⊔ E⁆ ≤ N := by
  have h : D ⊔ E ≤ commutatorPreimage P A N := by
    apply sup_le
    · exact le_commutatorPreimage hD (by rwa [commutator_comm])
    · exact le_commutatorPreimage hE (by rwa [commutator_comm])
  rw [commutator_comm]
  exact (commutator_mono h le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hPN)

/-- The literal intersection enlarged by Z_alpha is fixed modulo Z_alpha
by both cores, therefore by the subgroup they generate. Incidence and
distinctness are only needed for identifying that generated subgroup. -/
theorem intersection_commutator_le_joinedCores (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (d e : M) :
    ⁅(H ⊓ secondFlagLayer source i d ⊓ secondFlagLayer source i e) ⊔ Z R (alpha R),
      localFlagKernel source (!i) d ⊔ localFlagKernel source (!i) e⁆ ≤ Z R (alpha R) := by
  apply commutator_join_le _ _ _ (stabilizer R (alpha R)) _
    (localFlagKernel_le_stabilizer source (!i) d)
    (localFlagKernel_le_stabilizer source (!i) e) (Z_normalized R _)
  · exact (commutator_mono (sup_le (inf_le_left.trans inf_le_right)
      (Z_le_secondFlagLayer source i d)) le_rfl).trans
      (secondFlagLayer_commutator_le_Z source geometry hlarge i d)
  · exact (commutator_mono (sup_le inf_le_right
      (Z_le_secondFlagLayer source i e)) le_rfl).trans
      (secondFlagLayer_commutator_le_Z source geometry hlarge i e)

private theorem quotient_fixed_of_commutator {G : Type*} [Group G]
    (P N D A : Subgroup G) [(N.subgroupOf P).Normal]
    (hDP : D ≤ P) (hAP : A ≤ P) (hPN : P ≤ normalizer N)
    (hcomm : ⁅D, A⁆ ≤ N) :
    (D.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P)) ≤
      centralizer ((A.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P)) :
        Set (P ⧸ N.subgroupOf P)) := by
  have h := le_commutatorPreimage hDP hcomm
  have hs : D.subgroupOf P ≤ (commutatorPreimage P A N).subgroupOf P :=
    fun _ hx => h hx
  rw [commutatorPreimage_subgroupOf P A N P le_rfl hAP hPN,
    commutatorPreimage_eq_inf_comap_centralizer] at hs
  exact map_le_iff_le_comap.mpr (hs.trans inf_le_right)

/-- The quotient of the enlarged intersection in G_alpha/Z_alpha lies in
the common fixed space of the images of both actual local cores. -/
theorem intersection_quotient_fixed (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (d e : M) :
    letI := geometry.Z_normal (alpha R)
    let P := stabilizer R (alpha R)
    let N := (Z R (alpha R)).subgroupOf P
    let D := (H ⊓ secondFlagLayer source i d ⊓ secondFlagLayer source i e) ⊔ Z R (alpha R)
    (D.subgroupOf P).map (QuotientGroup.mk' N) ≤
      centralizer (((localFlagKernel source (!i) d ⊔ localFlagKernel source (!i) e).subgroupOf P).map
        (QuotientGroup.mk' N) : Set (P ⧸ N)) := by
  let := geometry.Z_normal (alpha R)
  apply quotient_fixed_of_commutator
  · exact (sup_le (inf_le_left.trans inf_le_right) (Z_le_secondFlagLayer source i d)).trans
      ((secondFlagLayer_le_radius source i d).trans (geometry.V_local _ rfl hlarge))
  · exact sup_le (localFlagKernel_le_stabilizer source (!i) d)
      (localFlagKernel_le_stabilizer source (!i) e)
  · exact Z_normalized R _
  · exact intersection_commutator_le_joinedCores source geometry hlarge i H d e

/-- The residual consequence once the actual incident cores generate a
subgroup containing the first residual. The generation premise remains a
separate mathematical obligation; it is not inferred from naturality alone. -/
theorem intersection_residual_le_of_generation (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (d e : M)
    (hgen : flagResidual source i ≤
      localFlagKernel source (!i) d ⊔ localFlagKernel source (!i) e) :
    ⁅H ⊓ secondFlagLayer source i d ⊓ secondFlagLayer source i e,
      flagResidual source i⁆ ≤ Z R (alpha R) :=
  (commutator_mono le_sup_left hgen).trans
    (intersection_commutator_le_joinedCores source geometry hlarge i H d e)

/-- The source's bound with the first full actor and target Z_alpha implies
its immediate middle noncontainment conclusion, using the critical bad triple.
This is a conditional implication, not a construction of the selected neighbor. -/
theorem middle_not_le_secondLayer_of_first_actor_bound (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (p : FlagCriticalData source geometry i) (d : M)
    (hcomm : ⁅Z R p.middle ⊓ secondFlagLayer source i d, flagParabolic source i⁆ ≤
      Z R (alpha R)) :
    ¬ Z R p.middle ≤ secondFlagLayer source i d := by
  intro h
  apply p.middle_triple
  have hc : ⁅Z R p.middle, flagResidual source i⁆ ≤ Z R (alpha R) := by
    rw [inf_eq_left.mpr h] at hcomm
    exact (commutator_mono le_rfl (flagResidual_le source i)).trans hcomm
  exact ((commutator_mono hc (V_le_Q geometry hlarge _ rfl)).trans_eq
    (geometry.centralizes _ rfl)).trans bot_le

/-- Distinct incident neighbors fix the intersection modulo Z_alpha under the
full first actor. The concrete binary core-generation theorem is stronger than
its residual consequence. -/
theorem intersection_first_actor_le [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (d e : M)
    (hd : flagIncident source i 1 d) (he : flagIncident source i 1 e)
    (hne : localFlagZ source (!i) d ≠ localFlagZ source (!i) e) :
    ⁅H ⊓ secondFlagLayer source i d ⊓ secondFlagLayer source i e,
      flagParabolic source i⁆ ≤ Z R (alpha R) := by
  have h := intersection_commutator_le_joinedCores source geometry hlarge i H d e
  rw [distinct_incident_cores_generate source i d e hd he hne] at h
  exact (commutator_mono le_sup_left le_rfl).trans h

/-- The literal quotient of the enlarged intersection is fixed by the full
first parabolic, retaining relative normality and the original denominator. -/
theorem intersection_quotient_fixed_first_actor [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (d e : M)
    (hd : flagIncident source i 1 d) (he : flagIncident source i 1 e)
    (hne : localFlagZ source (!i) d ≠ localFlagZ source (!i) e) :
    letI := geometry.Z_normal (alpha R)
    let P := stabilizer R (alpha R)
    let N := (Z R (alpha R)).subgroupOf P
    let D := (H ⊓ secondFlagLayer source i d ⊓ secondFlagLayer source i e) ⊔ Z R (alpha R)
    (D.subgroupOf P).map (QuotientGroup.mk' N) ≤
      centralizer (((flagParabolic source i).subgroupOf P).map
        (QuotientGroup.mk' N) : Set (P ⧸ N)) := by
  have h := intersection_quotient_fixed source geometry hlarge i H d e
  dsimp only at h ⊢
  rwa [distinct_incident_cores_generate source i d e hd he hne] at h

/-- The source's residual fixed-space conclusion, with actual generation
proved from the marked incident cores and no generation witness assumed. -/
theorem intersection_residual_le [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (H : Subgroup (FreeAmalgam R)) (d e : M)
    (hd : flagIncident source i 1 d) (he : flagIncident source i 1 e)
    (hne : localFlagZ source (!i) d ≠ localFlagZ source (!i) e) :
    ⁅H ⊓ secondFlagLayer source i d ⊓ secondFlagLayer source i e,
      flagResidual source i⁆ ≤ Z R (alpha R) := by
  apply intersection_residual_le_of_generation source geometry hlarge i H d e
  rw [distinct_incident_cores_generate source i d e hd he hne]
  exact flagResidual_le source i

private theorem intersection_le_of_index_two {G : Type*} [Group G]
    (H N D : Subgroup G) (hNH : N ≤ H) (hND : N ≤ D)
    (hi : N.relIndex H = 2) (hnot : ¬ H ≤ D) : H ⊓ D ≤ N := by
  have hm := relIndex_mul_relIndex N (H ⊓ D) H (le_inf hNH hND) inf_le_left
  rw [hi] at hm
  have hn : (H ⊓ D).relIndex H ≠ 1 :=
    fun he => hnot ((relIndex_eq_one.mp he).trans inf_le_right)
  have hd : (H ⊓ D).relIndex H ∣ 2 := ⟨N.relIndex (H ⊓ D), by nlinarith [hm]⟩
  have he := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  rw [he] at hm
  exact relIndex_eq_one.mp (by omega : N.relIndex (H ⊓ D) = 1)

/-- The binary edge index makes the midpoint intersection lie in Z_alpha
whenever the midpoint is not contained in that second layer. -/
theorem middle_intersection_le_Z_of_not_le (source : LocalSource L R)
    (geometry : Geometry R) (early : EarlyFacts R geometry) (i : Bool)
    (p : FlagCriticalData source geometry i) (d : M)
    (hnot : ¬ Z R p.middle ≤ secondFlagLayer source i d) :
    Z R p.middle ⊓ secondFlagLayer source i d ≤ Z R (alpha R) := by
  have hZ := Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)
  exact (intersection_le_of_index_two _ (Z R (beta R)) _
    (Early.edge_Z_le p.middle (beta R) p.middle_color (adjacent_symm R p.middle_neighbor))
    (hZ.trans (Z_le_secondFlagLayer source i d))
    (early.edge_Z_index p.middle (beta R) p.middle_color
      (adjacent_symm R p.middle_neighbor)) hnot).trans hZ

private theorem avoid_two (A B : Fin 3 → Prop)
    (hA : ∀ j k, j ≠ k → A j → A k → False)
    (hB : ∀ j k, j ≠ k → B j → B k → False) :
    ∃ j, ¬ A j ∧ ¬ B j := by
  classical
  by_cases ha : A 0
  · have ha1 : ¬ A 1 := hA 0 1 (by decide) ha
    have ha2 : ¬ A 2 := hA 0 2 (by decide) ha
    by_cases hb : B 1
    · exact ⟨2, ha2, hB 1 2 (by decide) hb⟩
    · exact ⟨1, ha1, hb⟩
  · by_cases hb : B 0
    · have hb1 : ¬ B 1 := hB 0 1 (by decide) hb
      have hb2 : ¬ B 2 := hB 0 2 (by decide) hb
      by_cases ha1 : A 1
      · exact ⟨2, hA 1 2 (by decide) ha1, hb2⟩
      · exact ⟨1, ha1, hb1⟩
    · exact ⟨0, ha, hb⟩

/-- The corrected four-part source selection on p.906. The binary edge index
and full-actor generation give a stronger selection route, so the supplied
natural section need not be strengthened or re-marked. -/
theorem exists_source_delta0 [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry) (i : Bool)
    (_hkernel : flagKernel source i = Q R (beta R))
    (_natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i) :
    ∃ d : M, flagIncident source i 1 d ∧
      ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d ∧
      ⁅Z R p.middle ⊓ secondFlagLayer source i d, flagParabolic source i⁆ ≤
        Z R (alpha R) ∧
      ¬ Z R p.middle ≤ secondFlagLayer source i d := by
  have hlarge : 2 < geometry.b R := by omega
  obtain ⟨d,hd,hjoin,hmeet,_⟩ := exists_incident_core_pencil source i
  have hA (j k : Fin 3) (hjk : j ≠ k)
      (hj : Z R p.endpoint ≤ localFlagKernel source (!i) (d j))
      (hk : Z R p.endpoint ≤ localFlagKernel source (!i) (d k)) : False := by
    apply p.endpoint_not_le_Q common
    exact (le_inf hj hk).trans_eq (hmeet j k hjk)
  have hB (j k : Fin 3) (hjk : j ≠ k)
      (hj : Z R p.middle ≤ secondFlagLayer source i (d j))
      (hk : Z R p.middle ≤ secondFlagLayer source i (d k)) : False := by
    have hc := intersection_commutator_le_joinedCores source geometry hlarge i
      (Z R p.middle) (d j) (d k)
    rw [inf_eq_left.mpr hj, inf_eq_left.mpr hk, hjoin j k hjk] at hc
    apply middle_not_le_secondLayer_of_first_actor_bound source geometry hlarge i p (d j) ?_ hj
    exact (commutator_mono (inf_le_left.trans le_sup_left) le_rfl).trans hc
  obtain ⟨j,hj,hmid⟩ := avoid_two _ _ hA hB
  have hcomm : ⁅Z R p.middle ⊓ secondFlagLayer source i (d j), flagParabolic source i⁆ ≤
      Z R (alpha R) :=
    (commutator_mono (middle_intersection_le_Z_of_not_le source geometry early i p (d j) hmid)
      le_rfl).trans (le_normalizer_iff_commutator_le_left.mp
        ((flagParabolic_le source i).trans (Z_normalized R _)))
  exact ⟨d j, hd j, hj, hcomm,
    middle_not_le_secondLayer_of_first_actor_bound source geometry hlarge i p (d j) hcomm⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
