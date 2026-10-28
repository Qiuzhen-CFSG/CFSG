module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry

/-!
# Reverse midpoint comparison when the second layer crosses the original core

An index-two core intersection lets any crossing subgroup represent the
nontrivial coset. Its commutators therefore generate all edge-core
commutators modulo Z_alpha. The selected original layer meets Z_middle in
exactly Z_beta; this supplies the required comparison with the original
Z_middle denominator. No moving-factor or later X calculation is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907,
the commutator-index comparison in the first paragraph.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing Incident.Pairing.Transport.Natural.Kernel

private theorem commutator_le_sup_of_index_two {G : Type*} [Group G]
    (E H K F A : Subgroup G) (hFH : F ≤ H) (hi : K.relIndex H = 2)
    (hnot : ¬ F ≤ K) (hEK : ⁅E,H ⊓ K⁆ ≤ A) (hHA : H ≤ normalizer A) :
    ⁅E,H⁆ ≤ A ⊔ ⁅E,F⁆ := by
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp hnot
  apply commutator_le.mpr
  intro e he h hh
  by_cases hhK : h ∈ K
  · exact mem_sup_left (hEK (commutator_mem_commutator he ⟨hh,hhK⟩))
  · have hfactor : u⁻¹ * h ∈ K := by
      have hm := (K.subgroupOf H).mul_mem_iff_of_index_two hi
        (a := ⟨u⁻¹,H.inv_mem (hFH hu)⟩) (b := ⟨h,hh⟩)
      exact hm.mpr (by simp only [mem_subgroupOf, inv_mem_iff, hun, hhK])
    have hc := hEK (commutator_mem_commutator he
      (show u⁻¹ * h ∈ H ⊓ K from ⟨H.mul_mem (H.inv_mem (hFH hu)) hh,hfactor⟩))
    have hn := (mem_normalizer_iff.mp (hHA (hFH hu)) _).mp hc
    have hp := (A ⊔ ⁅E,F⁆).mul_mem
      (mem_sup_right (commutator_mem_commutator he hu)) (mem_sup_left hn)
    have hid := commutatorElement_mul_right_eq_mul_conj e u (u⁻¹ * h)
    simp only [mul_inv_cancel_left] at hid
    rw [hid]
    simpa only [mul_assoc] using hp

private theorem index_comparison_of_sup {G : Type*} [Group G]
    (E A T C D : Subgroup G) [Finite E]
    (hAE : A ≤ E) (hDE : D ≤ E)
    (hEN : E ≤ normalizer A) (hTA : T ⊓ E ≤ A) (hC : C ≤ A ⊔ D) :
    A.relIndex C ≤ T.relIndex D := by
  let : Finite (A ⊔ D : Subgroup G) := Finite.of_injective
    (inclusion (sup_le hAE hDE)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDE) (inclusion_injective _)
  let : (A.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hEN
  have hsup : A.relIndex (A ⊔ D) = A.relIndex D := by
    have hh := relIndex_sup_left (D.subgroupOf E) (A.subgroupOf E)
    rwa [← subgroupOf_sup hAE hDE, relIndex_subgroupOf (sup_le hAE hDE),
      relIndex_subgroupOf hDE] at hh
  calc
    A.relIndex C ≤ A.relIndex (A ⊔ D) := relIndex_le_of_le_right hC index_ne_zero_of_finite
    _ = A.relIndex D := hsup
    _ ≤ (T ⊓ D).relIndex D := relIndex_le_of_le_left
      ((inf_le_inf_left T hDE).trans hTA) index_ne_zero_of_finite
    _ = T.relIndex D := inf_relIndex_right _ _

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem incident_core_index (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (flagKernel source i).relIndex (localFlagKernel source (!i) d) = 2 := by
  obtain ⟨π, hπ, hk⟩ := exists_barProjection source i
  obtain ⟨t, _, htn, himage⟩ := exists_incident_reflection source i d hd π hπ hk
  rw [← relIndex_subgroupOf (incidentKernel_le_flagParabolic source i d hd), ← hk,
    relIndex_ker]
  apply Nat.card_eq_two_iff.mpr
  refine ⟨⟨1, (himage 1).mpr (Or.inl rfl)⟩, ⟨t, (himage t).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro he
    exact htn (congrArg Subtype.val he).symm
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (himage x).mp x.property with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)

/-- The first core has two cosets modulo an incident opposite core. -/
theorem incident_reverse_core_index (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (localFlagKernel source (!i) d).relIndex (flagKernel source i) = 2 := by
  have hinc : flagIncident source (!i) 1 d⁻¹ := by
    obtain ⟨m, hm, hdm⟩ := hd
    refine ⟨d⁻¹*m, ?_, ?_⟩
    · simpa only [inv_one, one_mul] using hdm
    · simpa only [inv_inv, mul_inv_cancel_left, Bool.not_not, inv_one, one_mul] using hm
  have hh := incident_core_index source (!i) d⁻¹ hinc
  simp only [Bool.not_not] at hh
  have he := relIndex_map_map_of_injective (f := (MulAut.conj (embedM R d)).toMonoidHom)
    (flagKernel source (!i))
    (localFlagKernel source i d⁻¹) (MulAut.conj (embedM R d)).injective
  change (localFlagKernel source (!i) d).relIndex
    (localConjugate (localConjugate (flagKernel source i) d⁻¹) d) = _ at he
  rw [← localConjugate_mul, mul_inv_cancel, localConjugate_one] at he
  exact he.trans hh

omit [Finite M] in
/-- The selected midpoint intersection is the original edge Z-layer. -/
theorem middle_intersection_eq_edge_Z (source : LocalSource L R) (geometry : Geometry R)
    (early : EarlyFacts R geometry) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) :
    Z R p.middle ⊓ secondFlagLayer source i p.delta0 = Z R (beta R) := by
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  have hBA := Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)
  have hBT := Early.edge_Z_le p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  have hBE := hBA.trans (Z_le_secondFlagLayer source i p.delta0)
  have hi := early.edge_Z_index p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  have hm := relIndex_mul_relIndex (Z R (beta R))
    (Z R p.middle ⊓ secondFlagLayer source i p.delta0) (Z R p.middle)
    (le_inf hBT hBE) inf_le_left
  rw [hi] at hm
  have hn : (Z R p.middle ⊓ secondFlagLayer source i p.delta0).relIndex (Z R p.middle) ≠ 1 :=
    fun h => p.middle_not_le ((relIndex_eq_one.mp h).trans inf_le_right)
  have hd : (Z R p.middle ⊓ secondFlagLayer source i p.delta0).relIndex (Z R p.middle) ∣ 2 :=
    ⟨_, by simpa only [mul_comm] using hm.symm⟩
  have he := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  rw [he] at hm
  exact le_antisymm (relIndex_eq_one.mp (by omega)) (le_inf hBT hBE)

/-- The transported auxiliary span lies in the common edge core. -/
theorem transported_Y_le_edge_core (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M) :
    (Y source i e).map t.conjugation.toMonoidHom ≤ Q R (beta R) := by
  rw [← t.map_Q_beta]
  exact map_mono ((Y_le_radius source i e).trans
    ((V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R))))

/-- The reverse comparison when the transported second layer escapes the
original opposite core. The two source denominators are retained. -/
theorem reverse_comparison_of_second_core_escape (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hcross : ¬ (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤
    (Z R p.middle).relIndex
      ⁅secondFlagLayer source i p.delta0,
        (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ := by
  let E := secondFlagLayer source i p.delta0
  let F := (secondFlagLayer source i e).map t.conjugation.toMonoidHom
  let W := (Y source i e).map t.conjugation.toMonoidHom
  have hWH : W ≤ Q R (beta R) :=
    transported_Y_le_edge_core source geometry common.large_distance i p t e
  have hFH : F ≤ Q R (beta R) := (map_mono (second_le_Y source i e)).trans hWH
  have hHE : Q R (beta R) ≤ normalizer E :=
    (hkernel ▸ Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor).trans
      (Incident.secondFlagLayer_normalized source geometry common.large_distance i p.delta0)
  have hDE : ⁅E,F⁆ ≤ E := le_normalizer_iff_commutator_le_left.mp (hFH.trans hHE)
  let := Incident.secondFlagLayer_finite source geometry common.large_distance i p.delta0
  have hHA : Q R (beta R) ≤ normalizer (Z R (alpha R)) :=
    (show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Z_normalized R _)
  apply index_comparison_of_sup E (Z R (alpha R)) (Z R p.middle) ⁅E,W⁆ ⁅E,F⁆
    (Z_le_secondFlagLayer source i p.delta0) hDE
    ((secondFlagLayer_le_radius source i p.delta0).trans
      ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _)))
  · rw [middle_intersection_eq_edge_Z source geometry early i p]
    exact Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)
  · apply (commutator_mono le_rfl hWH).trans
    apply commutator_le_sup_of_index_two E (Q R (beta R))
      (localFlagKernel source (!i) p.delta0) F (Z R (alpha R)) hFH
    · rw [← hkernel]
      exact incident_reverse_core_index source i p.delta0 p.delta0_neighbor
    · exact hcross
    · exact (commutator_mono le_rfl inf_le_right).trans
        (Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i p.delta0)
    · exact hHA

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
