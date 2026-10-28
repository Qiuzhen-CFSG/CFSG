module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.Actions

/-!
# Genuine covering rows for the corrected source action

The triple-A₇ component has an impossible order. In the triple-S₆ row,
the actor extension clause and order comparisons force the offender and
Thompson image to be the actual derived subgroup. Transport preserves
the original central covering and ambient sign-action witnesses.

The proofs adapt the existing terminal `ComponentRows` comparison to the
full `ProjectiveLine.QuasisimpleSourceConclusion`. The two-dimensional
F₄ offender clause remains on the original action; no legacy clause is
constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; F.6.18, pp.309–310; K.1.3, p.453; final proof of
15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace SourceComponentRows.Covers

private theorem cover_quasisimple {D : Type*} [Group D] {n : ℕ}
    (h : FSource.TripleAlternating D n) (hn : 5 ≤ n) : IsQuasisimple D := by
  let _ : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  obtain ⟨e⟩ := h.quotient
  exact { toIsPerfect := h.perfect, simple := e.isSimpleGroup }

private theorem cover_card {D : Type*} [Group D] {n : ℕ} [Nontrivial (Fin n)]
    (h : FSource.TripleAlternating D n) : Nat.card D = (n.factorial / 2) * 3 := by
  obtain ⟨ec⟩ := h.center
  obtain ⟨eq⟩ := h.quotient
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center D),
    Nat.card_congr ec.toEquiv, Nat.card_congr eq.toEquiv, nat_card_alternatingGroup]
  simp

private theorem symmetric_cover_card {D : Type*} [Group D] {n : ℕ}
    (h : FSource.TripleSymmetric D n) : Nat.card D = n.factorial * 3 := by
  let _ := h.normal
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup h.kernel,
    Nat.card_congr h.quotientEquiv.toEquiv, Nat.card_congr h.kernelEquiv.toEquiv,
    Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm, Fintype.card_fin]
  simp

private theorem symmetric_derived_index {D : Type*} [Group D] {n : ℕ}
    (h : FSource.TripleSymmetric D n) (hn : n = 6 ∨ n = 7) :
    (commutator D).index = 2 := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc := cover_card h.derived
  have hd := symmetric_cover_card h
  have hm := (commutator D).card_mul_index
  rw [hc, hd] at hm
  rcases hn with rfl | rfl <;> norm_num [Nat.factorial] at hm <;> omega

private theorem symmetric_derived_quotient {D : Type*} [Group D] [Finite D] {n : ℕ}
    (h : FSource.TripleSymmetric D n) (hn : n = 6 ∨ n = 7) :
    IsPGroup 2 (D ⧸ commutator D) := by
  apply IsPGroup.iff_card.mpr
  exact ⟨1, by simpa only [pow_one, ← index_eq_card] using symmetric_derived_index h hn⟩

private theorem symmetric_fitting {D : Type*} [Group D] [Finite D] {n : ℕ}
    (h : FSource.TripleSymmetric D n) (hn : n = 6 ∨ n = 7)
    (hcore : pCore 2 D = ⊥) : generalizedFitting D = commutator D := by
  let _ : IsQuasisimple (commutator D) := cover_quasisimple h.derived (by omega)
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (symmetric_derived_quotient h hn) hcore

private theorem fitting_top {D : Type*} [Group D] [Finite D]
    (h : IsQuasisimple D) : generalizedFitting D = ⊤ := by
  let _ := h
  let _ : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  exact top_unique (component_le_generalizedFitting D ⊤
    ⟨(inferInstance : (⊤ : Subgroup D).Normal).isSubnormal, inferInstance⟩)

end SourceComponentRows.Covers

namespace SourceInput
open SourceComponentRows.Covers ComponentRows.TripleRows
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

private theorem source_offender_component_card
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    Nat.card (generalizedFitting d.offenderGroup) =
      Nat.card (generalizedFitting (coreQuotient H)) := by
  let e := (MulEquiv.subgroupCongr (d.offender_fitting_eq hL)).trans
    (subgroupOfEquivOfLe ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender))
  exact Nat.card_congr e.toEquiv

/-- The covered half of F.6.18(7) is absent from the source FF component list.
The argument applies unchanged after interchanging the two local labels. -/
theorem source_component_row_tripleSeven_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    (h : FSource.TripleAlternating (coreQuotient H) 7) : False := by
  have hf := fitting_top (cover_quasisimple h (by decide))
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 7560 := by
    rw [d.source_offender_component_card hL, hf, Subgroup.card_top, cover_card h]
    norm_num [Nat.factorial]
  exact model_card_ne_7560 (c.fittingModel _) hc

/-- The covered half of F.6.18(9) has the forbidden triple-A₇ component.
No equality of the ambient and offender actors is assumed. -/
theorem source_component_row_tripleSymmetricSeven_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    (h : FSource.TripleSymmetric (coreQuotient H) 7) : False := by
  have hf := symmetric_fitting h (Or.inr rfl)
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 7560 := by
    rw [d.source_offender_component_card hL, hf, cover_card h.derived]
    norm_num [Nat.factorial]
  exact model_card_ne_7560 (c.fittingModel _) hc

/-- In the triple-S₆ row, the actual Thompson image is the ambient derived
group. This is proved through the source offender actor, not assumed. -/
theorem source_thompson_image_eq_tripleSymmetricSix_derived
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    (h : FSource.TripleSymmetric (coreQuotient H) 6) :
    (thompsonGroup H).map coreProjection = commutator (coreQuotient H) := by
  have hf := symmetric_fitting h (Or.inl rfl)
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
  have hle := (d.fitting_le_thompson hL).trans d.thompson_image_le_offender
  have hc : Nat.card (generalizedFitting (coreQuotient H)) = 1080 := by
    rw [hf, cover_card h.derived]
    norm_num [Nat.factorial]
  rcases d.source_offender_actor_of_quasisimple_source hL c with ⟨hi, hX⟩ | ⟨n, hlo, hhi, ⟨e⟩⟩ | ⟨e⟩
  · let _ := hi
    rw [hX]
    apply le_antisymm
    · rw [← d.offenderGroup.commutator_eq_self]
      exact commutator_mono le_top le_top
    · rwa [← hf]
  · exact (not_symmetric_actor (Or.inl hc) (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle) hlo hhi e).elim
  · obtain ⟨e⟩ := e
    exact (not_g2_actor (Or.inl hc) (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle) e).elim

/-- F.6.18(8)'s genuine symmetric cover yields the genuine triple-A₆
Thompson image, the original ambient covering witness, and the two-quotient. -/
theorem source_component_row_tripleSymmetricSix
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup))
    (h : FSource.TripleSymmetric (coreQuotient H) 6) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  have hf := symmetric_fitting h (Or.inl rfl)
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
  refine ⟨.tripleSix (ComponentRows.tripleAlternating_of_equiv
    (MulEquiv.subgroupCongr (d.source_thompson_image_eq_tripleSymmetricSix_derived hL c h)) h.derived),
    .tripleSymmetricSix h, ?_⟩
  exact (symmetric_derived_quotient h (Or.inl rfl)).of_surjective
    (QuotientGroup.quotientMulEquivOfEq hf.symm).toMonoidHom
    (QuotientGroup.quotientMulEquivOfEq hf.symm).surjective

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
