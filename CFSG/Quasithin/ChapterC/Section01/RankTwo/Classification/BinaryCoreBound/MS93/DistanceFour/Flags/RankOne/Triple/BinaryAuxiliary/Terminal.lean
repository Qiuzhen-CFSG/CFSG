module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Fixed

/-!
# The terminal binary displacement argument in MS93 (4.6.8)

Two successive escapes, X from Q_middle and Y from X Q_middle, force Y
to fill the order-four quotient Q_beta/Q_middle. Its commutator with Z_middle
is therefore the entire edge commutator. The three-neighbor calculation puts
it in Z_delta. Two incident neighbors avoiding the critical endpoint generate
the first full parabolic, whose fixed subgroup in Z_alpha is central.

The final assembly below is explicitly conditional on the two auxiliary
escapes. It constructs the selected core, natural section and corrected
preparatory configuration itself; it does not yet prove those escapes or
assert the unconditional source theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed pp.907--908.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Forget only the later incident choices, preserving the same actual path. -/
def SourceFlagPreparatoryData.toCriticalData {source : LocalSource L R}
    {geometry : Geometry R} {i : Bool} (p : SourceFlagPreparatoryData source geometry i) :
    FlagCriticalData source geometry i where
  middle := p.middle
  endpoint := p.endpoint
  critical := p.critical
  middle_neighbor := p.middle_neighbor
  first_distance := p.first_distance
  second_distance := p.second_distance
  middle_triple := p.middle_triple

namespace BinaryAuxiliary

private theorem index_gt_two_of_two_escapes {G : Type*} [Group G]
    (K A H : Subgroup G) [Finite H] (hAH : A ≤ H)
    (hAK : ¬ A ≤ K) (hH : ¬ H ≤ A ⊔ K) : 2 < K.relIndex H := by
  have hp : K.relIndex H ≠ 0 := (K.subgroupOf H).index_ne_zero_of_finite
  have h1 : K.relIndex H ≠ 1 := fun h => hAK (hAH.trans (relIndex_eq_one.mp h))
  by_contra hn
  have h2 : K.relIndex H = 2 := by omega
  obtain ⟨a, _, haK, hcosets⟩ := relIndex_eq_two_iff_exists_notMem_and.mp h2
  obtain ⟨x, hx, hxK⟩ := SetLike.not_le_iff_exists.mp hAK
  have hxa : x * a ∈ K := (hcosets x (hAH hx)).resolve_right hxK
  have ha : a ∈ A ⊔ K := by
    have hh := (A ⊔ K).mul_mem ((A ⊔ K).inv_mem (mem_sup_left hx)) (mem_sup_right hxa)
    simpa only [inv_mul_cancel_left] using hh
  apply hH
  intro y hy
  rcases hcosets y hy with hyK | hyK
  · have hh := (A ⊔ K).mul_mem (mem_sup_right hyK) ((A ⊔ K).inv_mem ha)
    simpa only [mul_inv_cancel_right] using hh
  · exact mem_sup_right hyK

variable [Finite M]

/-- The two source escapes force strict displacement; no assumed index or
reverse-containment implication replaces either escape. -/
theorem Y_displacement_of_escapes (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) (c : Vertex R)
    (hX : ¬ X source i d ≤ Q R c)
    (hY : ¬ Y source i d ≤ X source i d ⊔ Q R c) :
    2 < (Q R c).relIndex (Y source i d) := by
  let := finite_stabilizer R (alpha R)
  let : Finite (Y source i d) := Finite.of_injective
    (inclusion ((Y_le_radius source i d).trans (geometry.V_local _ rfl hlarge)))
    (inclusion_injective _)
  exact index_gt_two_of_two_escapes _ _ _
    ((X_le_D source geometry hlarge i d).trans (D_le_Y source i d)) hX hY

/-- Filling the edge quotient puts its full midpoint commutator in Z_delta,
using the proved derived bound for the actual auxiliary span. -/
theorem edge_commutator_le_localZ_of_displacement (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) (d : M)
    (hd : flagIncident source i 1 d)
    (hindex : 2 < (Q R p.middle).relIndex (Y source i d)) :
    ⁅Z R p.middle, Q R (beta R)⁆ ≤ localFlagZ source (!i) d := by
  have hY : Y source i d ≤ Q R (beta R) :=
    (Y_le_radius source i d).trans ((V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R)))
  have he : ⁅Z R p.middle, Y source i d⁆ = ⁅Z R p.middle, Q R (beta R)⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (p.sup_middle_kernel_of_displacement early _ hY hindex))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.middle p.middle_color)))
      (hY.trans ((show Q R (beta R) ≤ stabilizer R p.middle from
        fun _ hx => hx.2 _ p.middle_neighbor).trans (Z_normalized R p.middle)))
  rw [← he]
  exact (commutator_mono (p.middle_le_firstLayer.trans (first_le_Y source i 1 d hd)) le_rfl).trans
    (Y_commutator_le_localZ source geometry common early i hkernel d)

private theorem two_avoiding (P : Fin 3 → Prop)
    (h : ∀ j k, j ≠ k → ¬ (P j ∧ P k)) :
    ∃ j k, j ≠ k ∧ ¬ P j ∧ ¬ P k := by
  classical
  by_cases h0 : P 0
  · exact ⟨1, 2, by decide, fun h1 => h 0 1 (by decide) ⟨h0, h1⟩,
      fun h2 => h 0 2 (by decide) ⟨h0, h2⟩⟩
  · by_cases h1 : P 1
    · exact ⟨0, 2, by decide, h0, fun h2 => h 1 2 (by decide) ⟨h1, h2⟩⟩
    · exact ⟨0, 1, by decide, h0, h1⟩

/-- The last source paragraph: two avoiding neighbors force the midpoint
edge commutator to be central in the whole vertex stabilizer. -/
theorem middle_edge_central_of_Y_displacement (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i)
    (hdisplacement : ∀ d : M, flagIncident source i 1 d →
      ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d →
      2 < (Q R p.middle).relIndex (Y source i d)) :
    ⁅Z R p.middle, Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  obtain ⟨d, hd, hjoin, hmeet, _⟩ := Incident.exists_incident_core_pencil source i
  have hav : ∀ j k, j ≠ k → ¬ (Z R p.endpoint ≤ localFlagKernel source (!i) (d j) ∧
      Z R p.endpoint ≤ localFlagKernel source (!i) (d k)) := by
    rintro j k hjk ⟨hj, hk⟩
    exact p.endpoint_not_le_Q common ((le_inf hj hk).trans_eq (hmeet j k hjk))
  obtain ⟨j, k, hjk, hj, hk⟩ := two_avoiding _ hav
  have hjfix := edge_commutator_le_localZ_of_displacement source geometry common early i hkernel p
    (d j) (hd j) (hdisplacement (d j) (hd j) hj)
  have hkfix := edge_commutator_le_localZ_of_displacement source geometry common early i hkernel p
    (d k) (hd k) (hdisplacement (d k) (hd k) hk)
  apply le_trans _ (full_actor_fixed_Z_le_center source geometry common early i hkernel)
  intro x hx
  have hxj := hjfix hx
  have hxk := hkfix hx
  refine ⟨hxj.1, ?_⟩
  have central (K : Subgroup (FreeAmalgam R))
      (h : x ∈ centralizer (K : Set (FreeAmalgam R))) :
      K ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
    intro y hy z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (h y hy).symm
  have hall := sup_le (central _ hxj.2) (central _ hxk.2)
  rw [hjoin j k hjk] at hall
  intro y hy
  exact (hall hy x (Set.mem_singleton x)).symm

end BinaryAuxiliary

/-- Conditional final assembly from the two genuine auxiliary escapes on p.908.
The source theorem remains unfinished until that premise is constructed. -/
theorem flagControl_of_binary_auxiliary_escapes [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (haux : ∀ i : Bool, flagKernel source i = Q R (beta R) →
      FlagNaturalSection source i → ∀ p : SourceFlagPreparatoryData source geometry i,
      ∀ d : M, flagIncident source i 1 d →
        ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d →
        (¬ BinaryAuxiliary.X source i d ≤ Q R p.middle) ∧
        (¬ BinaryAuxiliary.Y source i d ≤ BinaryAuxiliary.X source i d ⊔ Q R p.middle)) :
    FlagControl source := by
  obtain ⟨i, hkernel⟩ := select_flag_kernel source geometry common early
  refine ⟨i, hkernel, ?_⟩
  by_contra hbad
  obtain ⟨natural⟩ := flagNaturalSection source geometry common hb early i hkernel hbad
  obtain ⟨p⟩ := sourceFlagPreparatoryData source geometry common hb early i hkernel hbad natural
  apply p.toCriticalData.middle_edge_commutator_not_le_center common
  apply BinaryAuxiliary.middle_edge_central_of_Y_displacement source geometry common early i hkernel p.toCriticalData
  intro d hd hnot
  obtain ⟨hX, hY⟩ := haux i hkernel natural p d hd hnot
  exact BinaryAuxiliary.Y_displacement_of_escapes source geometry common.large_distance i d p.middle hX hY

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
