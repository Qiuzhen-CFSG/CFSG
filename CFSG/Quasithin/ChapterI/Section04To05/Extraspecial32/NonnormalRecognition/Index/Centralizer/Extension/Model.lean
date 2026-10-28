module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Extension.Setup
public import Theory.SpecificGroups.Alternating.FixedPointCentralizer
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Marking.Model
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.IsPerfect

/-!
# The literal nine-point residual and its eight-point supplement

For t9 = (01)(23), the even permutations on its five fixed points form a
normal A₅ in C_A₉(t9). The centralizer has order 480, so the quotient has
order eight. Perfectness of A₅ identifies this subgroup with the actual
two-residual, not just an abstract subgroup of the same order.

The literal eight-point centralizer has order 96. Its image and the residual
therefore generate the order-480 centralizer, and their intersection has order
12. Residual functoriality identifies the pullback with the eight-point
residual under the explicit hypothesis that the latter has order 12.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
The local order hypothesis is discharged by the separate eight-point model;
the extension assembly consumes all four fields of `ModelGeometry`.
-/

@[expose] public section

open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.Extension

/-- The subgroup supported on the five fixed points of the marked involution. -/
abbrev modelFixed := alternatingGroup.FixedPointCentralizer.fixed t9

private theorem fixedPoints_card :
    Fintype.card (alternatingGroup.FixedPointCentralizer.points t9) = 5 := by decide

/-- The actual supported subgroup, identified with A₅. -/
noncomputable def modelFixedEquiv : modelFixed ≃* alternatingGroup (Fin 5) :=
  (alternatingGroup.FixedPointCentralizer.equiv t9).trans
    (Fintype.equivFinOfCardEq (by exact fixedPoints_card)).altCongrHom

theorem modelFixed_card : Nat.card modelFixed = 60 := by
  rw [Nat.card_congr modelFixedEquiv.toEquiv, Nat.card_eq_fintype_card,
    card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem centralizer_card : Nat.card (Centralizer t9) = 480 :=
  alternatingGroup.EightNineInvolutionCounts.card_centralizer_t9

private theorem a5_twoPerfect : IsPPerfect 2 (alternatingGroup (Fin 5)) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  intro H hH hq
  let : H.Normal := hH
  by_contra hne
  let : Nontrivial (alternatingGroup (Fin 5) ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (alternatingGroup (Fin 5) ⧸ H) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
  let : Group.IsNilpotent (alternatingGroup (Fin 5) ⧸ H) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5) ⧸ H) inferInstance

/-- A perfect normal subgroup with two-group quotient is the two-residual. -/
theorem modelResidual_eq_fixed : modelResidual = modelFixed := by
  apply pResidual_eq_of_isPPerfect
  · exact a5_twoPerfect.of_surjective modelFixedEquiv.symm.toMonoidHom
      modelFixedEquiv.symm.surjective
  · apply IsPGroup.of_card (n := 3)
    have h := modelFixed.card_mul_index
    rw [modelFixed_card, centralizer_card] at h
    change modelFixed.index = 2 ^ 3
    omega

/-- The residual consists exactly of permutations fixing the first four points. -/
theorem mem_modelResidual (g : Centralizer t9) :
    g ∈ modelResidual ↔ ∀ i : Fin 9, i.val < 4 → (g.val : Perm (Fin 9)) i = i := by
  rw [modelResidual_eq_fixed, alternatingGroup.FixedPointCentralizer.mem_fixed]
  have hs : ∀ i : Fin 9, i ∈ (t9 : Perm (Fin 9)).support ↔ i.val < 4 := by decide
  simp only [hs]

/-- The A₅ model for the literal two-residual of C_A₉((01)(23)). -/
noncomputable def modelResidualEquiv : modelResidual ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr modelResidual_eq_fixed).trans modelFixedEquiv

theorem modelResidual_card : Nat.card modelResidual = 60 := by
  rw [modelResidual_eq_fixed, modelFixed_card]

private theorem localRange_card : Nat.card modelLocalEmbedding.range = 96 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective modelLocalEmbedding_injective).toEquiv]
  exact Marking.t8_centralizer_card

/-- The actual residual and the literal eight-point image generate the centralizer. -/
theorem modelResidual_sup_local : modelResidual ⊔ modelLocalEmbedding.range = ⊤ := by
  apply eq_top_of_le_card
  have h₁ := card_dvd_of_le (show modelResidual ≤
    modelResidual ⊔ modelLocalEmbedding.range from le_sup_left)
  have h₂ := card_dvd_of_le (show modelLocalEmbedding.range ≤
    modelResidual ⊔ modelLocalEmbedding.range from le_sup_right)
  rw [modelResidual_card] at h₁
  rw [localRange_card] at h₂
  have h := Nat.lcm_dvd h₁ h₂
  norm_num at h
  rw [centralizer_card]
  exact Nat.le_of_dvd (Nat.card_pos) h

private theorem intersection_card :
    Nat.card (modelResidual ⊓ modelLocalEmbedding.range : Subgroup (Centralizer t9)) = 12 := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes modelResidual
    modelLocalEmbedding.range (by rw [modelResidual.normalizer_eq_top]; exact le_top)
  rw [modelResidual_card, localRange_card, modelResidual_sup_local, card_top,
    centralizer_card] at h
  omega

private theorem comap_card : Nat.card (modelResidual.comap modelLocalEmbedding) = 12 := by
  have h := Nat.card_congr ((modelResidual.comap modelLocalEmbedding).equivMapOfInjective
    modelLocalEmbedding modelLocalEmbedding_injective).toEquiv
  rw [map_comap_eq, inf_comm] at h
  exact h.trans intersection_card

/-- The pullback uses the prescribed inclusion fixing point 8. -/
theorem modelLocal_intersection (h12 : Nat.card modelLocalResidual = 12) :
    modelResidual.comap modelLocalEmbedding = modelLocalResidual := by
  symm
  apply eq_of_le_of_card_ge
  · exact (map_le_iff_le_comap).mp (map_pResidual_le 2 modelLocalEmbedding)
  · rw [comap_card, h12]

/-- Concrete model input for the marked centralizer extension; only the independently
produced eight-point residual order remains explicit. -/
theorem modelGeometry_nonempty (h12 : Nat.card modelLocalResidual = 12) :
    Nonempty ModelGeometry :=
  ⟨{ residual_equiv := modelResidualEquiv
     local_card := h12
     local_intersection := modelLocal_intersection h12
     generation := modelResidual_sup_local }⟩
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.Extension
end
