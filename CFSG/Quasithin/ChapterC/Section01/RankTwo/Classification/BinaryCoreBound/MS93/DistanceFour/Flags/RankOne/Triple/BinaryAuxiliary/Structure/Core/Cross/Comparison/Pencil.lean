module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions

/-!
# Central-layer action from the midpoint pencil

The original X escapes Q_middle, so it escapes at least two of the three
incident transported cores. If Z_alpha lies in the corresponding second
layers, it is fixed modulo Z_middle by both cores. Their actual join is
the full transported first parabolic. This yields the center-action field
of the midpoint comparison, with the central containments still explicit.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907, “Since this holds for all lambda0”.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

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

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Containment in the second layers at the escaping flags implies the full
first-actor bound: at least two of the three actual cores are escaped, and
those two cores generate the transported first parabolic. -/
theorem middle_center_action_of_containments
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (x : XFactor source i p.delta0)
    (hcenter : ∀ e : M, flagIncident source i 1 e →
      ¬ X source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom →
      Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom) :
    ⁅Z R (alpha R), (flagParabolic source i).map t.conjugation.toMonoidHom⁆ ≤
      Z R p.middle := by
  have hlarge : 2 < geometry.b R := by omega
  let f := t.conjugation.toMonoidHom
  obtain ⟨e,hi,hjoin,hmeet,_⟩ := Incident.exists_incident_core_pencil source i
  obtain ⟨j,k,hjk,hj,hk⟩ := two_avoiding
    (fun j => X source i p.delta0 ≤ (localFlagKernel source (!i) (e j)).map f)
    (by
      intro j k hjk hh
      apply X_selected_not_le_middle_core source geometry hb early i hkernel p x
      have h := le_inf hh.1 hh.2
      rwa [← map_inf _ _ _ t.conjugation.injective,hmeet j k hjk,t.map_Q_alpha] at h)
  have hgen : (localFlagKernel source (!i) (e j)).map f ⊔
      (localFlagKernel source (!i) (e k)).map f = (flagParabolic source i).map f := by
    rw [← Subgroup.map_sup, hjoin j k hjk]
  have hcomm (m : Fin 3)
      (hm : ¬ X source i p.delta0 ≤ (localFlagKernel source (!i) (e m)).map f) :
      ⁅Z R (alpha R), (localFlagKernel source (!i) (e m)).map f⁆ ≤ Z R p.middle := by
    have hc := map_mono (f := f)
      (Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i (e m))
    rw [map_commutator,t.map_Z_alpha] at hc
    exact (commutator_mono (hcenter (e m) (hi m) hm) le_rfl).trans hc
  let P := (flagParabolic source i).map f
  have hnorm : P ≤ normalizer (Z R p.middle) := by
    rw [← t.map_Z_alpha]
    exact (map_mono ((flagParabolic_le source i).trans (Z_normalized R _))).trans
      (le_normalizer_map f)
  have hP : P ≤ commutatorPreimage P (Z R (alpha R)) (Z R p.middle) := by
    apply le_trans hgen.symm.le
    apply sup_le
    · exact le_commutatorPreimage (le_sup_left.trans_eq hgen)
        (by simpa only [commutator_comm] using hcomm j hj)
    · exact le_commutatorPreimage (le_sup_right.trans_eq hgen)
        (by simpa only [commutator_comm] using hcomm k hk)
  rw [commutator_comm]
  exact (commutator_mono hP le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hnorm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
