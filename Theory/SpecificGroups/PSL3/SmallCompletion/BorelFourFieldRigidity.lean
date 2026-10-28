module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourFactorization
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.Diagram

/-!
# Whole-Borel rigidity on the original full parabolics over any field of four

Entrywise field transport keeps both actual parabolics, their original Borel,
and the ordered radical embeddings. The proved restriction factorization
therefore applies on the canonical field without replacing any marked group.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL2FourNatural Theory.GroupTheory.RankTwoAmalgam
variable (K : Type*) [Field K] [Finite K]

/-- The full-parabolic native amalgam with its literal whole Borel inclusions. -/
@[expose] def fullBorelAmalgam :
    Theory.GroupTheory.RankTwoAmalgam (pointParabolic K) (borel K) (lineParabolic K) :=
  ⟨inclusion (map_mono (show borelSL K≤pointParabolicSL K from inf_le_left)),
    inclusion (map_mono (show borelSL K≤lineParabolicSL K from inf_le_right))⟩

private def fieldAmalgamIso (e : F ≃+* K) :
    Iso fieldFourBorelAmalgam (fullBorelAmalgam K) where
  left := (MulEquiv.subgroupCongr field_four_parabolics.1.symm).trans
    (((Atlas.fieldEquivPSL 3 e).subgroupMap (pointParabolic F)).trans
      (MulEquiv.subgroupCongr (FieldTransport.field_map_pointParabolic e)))
  middle := ((Atlas.fieldEquivPSL 3 e).subgroupMap (borel F)).trans
    (MulEquiv.subgroupCongr (FieldTransport.field_map_borel e))
  right := (MulEquiv.subgroupCongr field_four_parabolics.2.symm).trans
    (((Atlas.fieldEquivPSL 3 e).subgroupMap (lineParabolic F)).trans
      (MulEquiv.subgroupCongr (FieldTransport.field_map_lineParabolic e)))
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

private theorem field_unipotent (e : F ≃+* K) (u : U F) :
    (fieldAmalgamIso K e).middle (borelUnipotent F u)=
      borelUnipotent K ⟨e u.x,e u.y,e u.c⟩ := by
  apply Subtype.ext
  change Atlas.fieldEquivPSL 3 e (projection F (specialLinear F u))=
    projection K (specialLinear K _)
  rw [show projection F (specialLinear F u)=QuotientGroup.mk' _ (specialLinear F u) from rfl,
    Atlas.fieldEquivPSL_mk]
  apply congrArg (projection K)
  apply Subtype.ext
  change (matrix F u).map e=matrix K _
  funext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- The original full-parabolic amalgam over every field of four has genuine
whole-Borel factorization for every ordered-radical-preserving twist. -/
theorem full_borel_twist_factors (hK : Nat.card K=4) (a : MulAut (borel K))
    (h₁ : ∀ u∈V₁ K,a (borelUnipotent K u)∈(V₁ K).map (borelUnipotent K))
    (h₂ : ∀ u∈V₂ K,a (borelUnipotent K u)∈(V₂ K).map (borelUnipotent K)) :
    FactorsThrough (fullBorelAmalgam K) a := by
  let : Fintype K := Fintype.ofFinite K
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq
    (by rw [card_field,←Nat.card_eq_fintype_card,hK])
  let E := fieldAmalgamIso K e
  let d := (MulAut.congr E.middle.symm) a
  have hd (u : U F) : E.middle (d (borelUnipotent F u))=
      a (borelUnipotent K ⟨e u.x,e u.y,e u.c⟩) := by
    change E.middle (E.middle.symm (a (E.middle (borelUnipotent F u))))=_
    rw [MulEquiv.apply_symm_apply,field_unipotent]
  have huinv (v : U K) : E.middle (borelUnipotent F ⟨e.symm v.x,e.symm v.y,e.symm v.c⟩)=
      borelUnipotent K v := by
    rw [field_unipotent]
    simp
  have hd₁ (u : U F) (hu : u∈V₁ F) : d (borelUnipotent F u)∈(V₁ F).map (borelUnipotent F) := by
    obtain ⟨v,hv,hv'⟩ := h₁ ⟨e u.x,e u.y,e u.c⟩ (by simpa using hu)
    refine ⟨⟨e.symm v.x,e.symm v.y,e.symm v.c⟩,?_,?_⟩
    · simpa using hv
    · apply E.middle.injective
      rw [huinv,hd]
      exact hv'
  have hd₂ (u : U F) (hu : u∈V₂ F) : d (borelUnipotent F u)∈(V₂ F).map (borelUnipotent F) := by
    obtain ⟨v,hv,hv'⟩ := h₂ ⟨e u.x,e u.y,e u.c⟩ (by simpa using hu)
    refine ⟨⟨e.symm v.x,e.symm v.y,e.symm v.c⟩,?_,?_⟩
    · simpa using hv
    · apply E.middle.injective
      rw [huinv,hd]
      exact hv'
  have hf := (E.factorsThrough_iff d).mp (ordered_borel_twist_factors d hd₁ hd₂)
  have he : (MulAut.congr E.middle) d=a := by
    apply MulEquiv.ext
    intro b
    change E.middle (E.middle.symm (a (E.middle (E.middle.symm b))))=a b
    rw [MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply]
  rwa [he] at hf

end Matrix.PSL3.SmallCompletion
