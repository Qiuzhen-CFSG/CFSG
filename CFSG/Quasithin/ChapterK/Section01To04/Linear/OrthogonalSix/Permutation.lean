module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Ratios
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Offenders on the six-dimensional A₈ and S₈ permutation sections

The checked degree-eight enumeration implies that strong offenders contain
odd permutations. Restriction to A₈ therefore has no strong offenders, and
its surviving best offenders have rank three. An explicit even-part offender
gives ratio one and, by simplicity, generation of A₈. Transpositions in a best
offender generate S₈ normally.

Source: Aschbacher–Smith, K.3.2.2 and B.4.2(10), printed pp.455 and 86,
using the complete B.3.2 calculations.
-/

public section

open BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix

private theorem conjugate_not_le_alternating {A B : Subgroup (Equiv.Perm (Fin 8))}
    (h : IsConjugateTo A B) {x : Equiv.Perm (Fin 8)} (hx : x ∈ B)
    (hodd : Equiv.Perm.sign x ≠ 1) : ¬ A ≤ alternatingGroup (Fin 8) := by
  rintro hle
  obtain ⟨g, rfl⟩ := h
  have he := Equiv.Perm.mem_alternatingGroup.mp
    (hle (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx))
  apply hodd
  simpa [MulAut.conj_apply, mul_comm, mul_left_comm, mul_assoc] using he

/-- No strong offender on the natural module is contained in the alternating group. -/
theorem no_strong_of_le_alternating {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : A ≤ alternatingGroup (Fin 8)) :
    ¬ IsStrongOffender (naturalRepresentation (Fin 8)) A := by
  intro hs
  exact conjugate_not_le_alternating ((Eight.isStrongOffender_natural_iff A).mp hs)
    (pairSwap_mem (n := 8) (m := 4) 0 (by decide)) (by decide) hA

/-- Every best offender lying in A₈ has rank three. -/
theorem best_rank_of_le_alternating {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : A ≤ alternatingGroup (Fin 8))
    (hbest : IsBestOffender (naturalRepresentation (Fin 8)) A) : rank A = 3 := by
  rcases (Eight.isBestOffender_natural_iff A).mp hbest with h | h
  · rcases h with ⟨m, hm, _, hc⟩ | hc | hc | ⟨B, hB, _, hc⟩
    · exact False.elim (conjugate_not_le_alternating hc
        (pairSwap_mem (n := 8) (m := m) 0 hm) (by decide) hA)
    · have hx : pairSwap 8 2 ∈ exceptional 8 (by decide) :=
        Subgroup.subset_closure (Or.inr ⟨2, by decide, rfl⟩)
      exact False.elim (conjugate_not_le_alternating hc hx (by decide) hA)
    · exact hc.rank_eq.trans Eight.rank_evenPart
    · exact hc.rank_eq.trans (Eight.rank_hyperplane hB)
  · exact regularEight_rank_three h

private theorem best_map_subtype {H : Subgroup (Equiv.Perm (Fin 8))}
    {A : Subgroup H} (hA : IsBestOffender ((naturalRepresentation (Fin 8)).comp H.subtype) A) :
    IsBestOffender (naturalRepresentation (Fin 8)) (A.map H.subtype) := by
  have hoff := hA.isOffender _ |>.map_equivariant _ (naturalRepresentation (Fin 8)) H.subtype H.subtype_injective
    (LinearEquiv.refl _ _) (fun _ _ => rfl)
  refine ⟨hoff.1, ?_⟩
  intro B hB
  have hBH : B ≤ H := hB.trans (by rintro _ ⟨a, _, rfl⟩; exact a.property)
  have hm := Subgroup.map_subgroupOf_eq_of_le hBH
  have hle : B.subgroupOf H ≤ A := by
    intro a ha
    obtain ⟨a', ha', he⟩ := hB ha
    exact H.subtype_injective he ▸ ha'
  have hw := hA.2 (B.subgroupOf H) hle
  rwa [weight_comp_map _ H.subtype H.subtype_injective,
    weight_comp_map _ H.subtype H.subtype_injective, hm] at hw

/-- The actual restricted A₈ module has no strong offenders. -/
theorem alternating_not_strong :
    ¬ IsStrongFFModule (alternatingNaturalRepresentation (Fin 8)) := by
  rintro ⟨A, hA⟩
  have hoff := (show IsOffender (alternatingNaturalRepresentation (Fin 8)) A from
    ⟨hA.1, hA.2.le⟩).map_equivariant _ (naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8)).subtype
      Subtype.val_injective (LinearEquiv.refl _ _) (fun _ _ => rfl)
  apply no_strong_of_le_alternating (A := A.map (alternatingGroup (Fin 8)).subtype)
    (by rintro _ ⟨a, _, rfl⟩; exact a.property)
  refine ⟨hoff.1, ?_⟩
  rw [← fixedCodim_map_equivariant (alternatingNaturalRepresentation (Fin 8))
    (naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8)).subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl), rank_map_injective _ Subtype.val_injective]
  exact hA.2

theorem alternating_best_rank {A : Subgroup (alternatingGroup (Fin 8))}
    (hA : IsBestOffender (alternatingNaturalRepresentation (Fin 8)) A) : rank A = 3 := by
  rw [← rank_map_injective (alternatingGroup (Fin 8)).subtype Subtype.val_injective]
  exact best_rank_of_le_alternating (by rintro _ ⟨a, _, rfl⟩; exact a.property)
    (best_map_subtype hA)

private theorem evenPart_best :
    IsBestOffender (alternatingNaturalRepresentation (Fin 8))
      ((evenPart 8).subgroupOf (alternatingGroup (Fin 8))) :=
  Eight.isBestOffender_natural_evenPart.subgroupOf _ inf_le_right

theorem alternating_quadraticRatio :
    quadraticRatio (alternatingNaturalRepresentation (Fin 8)) = 1 :=
  quadraticRatio_eq_one_of_no_strong _ ⟨_, evenPart_best.isOffender _⟩
    (fun A hA => alternating_not_strong ⟨A, hA⟩)

theorem alternating_offenderSubgroup :
    offenderSubgroup (alternatingNaturalRepresentation (Fin 8)) = ⊤ := by
  let J := offenderSubgroup (alternatingNaturalRepresentation (Fin 8))
  let : J.Normal := offenderSubgroup_normal _
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp :
    5 ≤ Nat.card (Fin 8)) (N := J) with h | h
  · exfalso
    apply evenPart_best.1.1
    apply eq_bot_iff.mpr
    rw [← h]
    exact le_iSup_of_le _ (le_iSup_of_le ⟨evenPart_best, le_top⟩ le_rfl)
  · exact h

/-- Best offenders generate the full symmetric actor as well. -/
theorem symmetric_offenderSubgroup :
    offenderSubgroup (naturalRepresentation (Fin 8)) = ⊤ := by
  let J := offenderSubgroup (naturalRepresentation (Fin 8))
  have hJ : J.Normal := offenderSubgroup_normal _
  have hD : D 8 ≤ J := le_iSup_of_le _ (le_iSup_of_le
    ⟨Eight.isBestOffender_natural_of_caseAFamily
      (caseAFamily_disjointTranspositions (by decide) (by decide)), le_top⟩ le_rfl)
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le _).mpr
  rintro s ⟨i, j, hij, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (0 : Fin 8) ≠ 1) hij)
  have hx := hJ.conj_mem (pairSwap 8 0) (hD (pairSwap_mem 0 (by decide))) g
  change g * Equiv.swap 0 1 * g⁻¹ ∈ J at hx
  change Equiv.swap i j ∈ J
  exact hg ▸ hx

end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
