module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Preparation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Comparison

/-!
# The original center in the midpoint moving summand

The reverse geometric index comparison and a nontrivial marked moving action
force the original center into the midpoint moving summand. Otherwise the
binary edge index makes its intersection with the commutator lie in Z_beta;
the exact three-denominator cancellation then makes the moving action trivial.

The reverse comparison is an explicit premise at the supplied flag, not an
existential choice or a consequence of an unmarked natural-module label.
This is a conditional step toward central-layer containment.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907, the first commutator-index comparison.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem intersection_le_of_index_two {G : Type*} [Group G]
    (A B S : Subgroup G) (hBA : B ≤ A) (hBS : B ≤ S)
    (hi : B.relIndex A = 2) (hnot : ¬ A ≤ S) : A ⊓ S ≤ B := by
  have hm := relIndex_mul_relIndex B (A ⊓ S) A (le_inf hBA hBS) inf_le_left
  rw [hi] at hm
  have hn : (A ⊓ S).relIndex A ≠ 1 :=
    fun he => hnot ((relIndex_eq_one.mp he).trans inf_le_right)
  have hd : (A ⊓ S).relIndex A ∣ 2 := ⟨B.relIndex (A ⊓ S), by nlinarith [hm]⟩
  have he := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  rw [he] at hm
  exact relIndex_eq_one.mp (by omega : B.relIndex (A ⊓ S) = 1)

private theorem center_le_of_reverse_index {G : Type*} [Group G]
    (C D A B T U S : Subgroup G) [Finite C]
    (hBA : B ≤ A) (hBT : B ≤ T) (hTU : T ≤ U) (hUS : U ≤ S) (hCS : C ≤ S)
    (hD : D ≤ U ⊓ C) (hi : B.relIndex A = 2)
    (hreverse : A.relIndex C ≤ T.relIndex D) (hnot : ¬ C ≤ U) : A ≤ S := by
  by_contra h
  have hAS := intersection_le_of_index_two A B S hBA (hBT.trans (hTU.trans hUS)) hi h
  have hAC : A ⊓ C ≤ B := (inf_le_inf_left A hCS).trans hAS
  have hbound := Moving.displacement_index_bound C D A B T U 1 hBA hBT hTU hD hreverse
    (le_of_eq (relIndex_eq_one.mpr hAC))
  have hpos : 0 < U.relIndex C := by
    change 0 < Nat.card (C ⧸ U.subgroupOf C)
    exact Nat.card_pos
  exact hnot (relIndex_eq_one.mp (by omega))

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The source reverse comparison at the supplied flag puts the original
center in its transported moving summand. All denominators retain their
original markings. This theorem does not construct the reverse comparison. -/
theorem middle_center_le_moving_of_reverse_index
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0)
    (e : M) (he : flagIncident source i 1 e)
    (hcross : ¬ X source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hreverse : (Z R (alpha R)).relIndex
        ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤
      (Z R p.middle).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆) :
    Z R (alpha R) ≤
      (⁅Y source i e,localFlagActor source (!i) e⁆ ⊔ secondFlagLayer source i e).map
        t.conjugation.toMonoidHom := by
  let f := t.conjugation.toMonoidHom
  let E := secondFlagLayer source i p.delta0
  let Y₀ := (Y source i e).map f
  let U₀ := (secondFlagLayer source i e).map f
  let P := (localFlagActor source (!i) e).map f
  let S := (⁅Y source i e,localFlagActor source (!i) e⁆ ⊔
    secondFlagLayer source i e).map f
  let C := ⁅E,Y₀⁆
  have hEP : E ≤ P :=
    ((secondFlagLayer_le_radius source i p.delta0).trans
      ((V_le_Q geometry common.large_distance _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R)))).trans
      ((t.map_first_kernel source i hkernel).symm.le.trans
        (map_mono (Incident.flagKernel_le_incidentActor source i e he)))
  have hCY : C ≤ Y₀ := le_normalizer_iff_commutator_le_right.mp
    (hEP.trans ((map_mono (Y_normalized source i e)).trans (le_normalizer_map _)))
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (Y source i e) := Finite.of_injective
    (inclusion ((Y_le_radius source i e).trans (geometry.V_local _ rfl common.large_distance)))
      (inclusion_injective _)
  let : Finite Y₀ := Finite.of_equiv (Y source i e)
    (t.conjugation.subgroupMap (Y source i e)).toEquiv
  let : Finite C := Finite.of_injective (inclusion hCY) (inclusion_injective _)
  have hTU : Z R p.middle ≤ U₀ := by
    rw [← t.map_Z_alpha]
    exact map_mono (Z_le_secondFlagLayer source i e)
  have hUS : U₀ ≤ S := map_mono le_sup_right
  have hCS : C ≤ S := by
    dsimp [C, S, Y₀]
    rw [Subgroup.map_sup, map_commutator]
    rw [commutator_comm E]
    exact (commutator_mono (show Y₀ ≤ Y₀ from le_rfl) hEP).trans le_sup_left
  have hD : ⁅E,U₀⁆ ≤ U₀ ⊓ C := le_inf
    (le_normalizer_iff_commutator_le_right.mp
      (hEP.trans ((map_mono
        (Incident.secondFlagLayer_normalized source geometry common.large_distance i e)).trans
          (le_normalizer_map _))))
    (commutator_mono le_rfl (map_mono (second_le_Y source i e)))
  have hnot : ¬ C ≤ U₀ := by
    intro h
    obtain ⟨me⟩ : Nonempty (MovingFactor source i e) := by
      simpa only [inv_mul_cancel_right] using
        movingFactor_conjugate source geometry common.large_distance i
          (e*p.delta0⁻¹) p.delta0 moving
    let nm := markedFactorMap t.conjugation me
    have hSY : S ≤ Y₀ := map_mono
      (sup_le (le_normalizer_iff_commutator_le_left.mp (Y_normalized source i e))
        (second_le_Y source i e))
    apply hcross
    exact (X_le_second source geometry common.large_distance i p.delta0).trans
      ((markedFactor_commutator_iff nm E hEP).mp
        ((commutator_mono hSY le_rfl).trans (commutator_comm E Y₀ ▸ h)))
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases hc : color R p.middle <;> simp_all
  exact center_le_of_reverse_index C ⁅E,U₀⁆ (Z R (alpha R)) (Z R (beta R))
    (Z R p.middle) U₀ S
    (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
    (edge_Z_le p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor))
    hTU hUS hCS hD (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R))
    hreverse hnot

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
