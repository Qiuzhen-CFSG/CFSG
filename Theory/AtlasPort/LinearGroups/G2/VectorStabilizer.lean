module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/VectorStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.SingularReduction
public import Theory.AtlasPort.LinearGroups.G2.PartnerCoordinates
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer

/-! The first-vector stabilizer is parametrized by a singular partner and an opposite-pair stabilizer, giving its order from affine five-space and SL₂. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {K : Type*} [Field K]

/-- The actual vector stabilizer, with no order assumptions. -/
def fixingFirstVector : Subgroup (Model K) where
  carrier := {g | g.val (basisVector 0) = basisVector 0}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by change g.val (h.val _) = _; rw [hh,hg]
  inv_mem' {g} hg := by
    change g.val.symm (basisVector 0) = basisVector 0
    apply g.val.injective
    rw [g.val.apply_symm_apply,hg]

theorem first_basis_norm_add (y : Carrier K) :
    norm (basisVector 0 + y) = norm y + y 7 := by
  simp [norm,basisVector]; ring

theorem fixingFirstVector_partner_last (g : fixingFirstVector (K := K)) :
    g.val.val (basisVector 7) 7 = 1 := by
  have hn : norm (g.val.val (basisVector 7)) = 0 := by
    simpa [norm,basisVector] using automorphism_norm g.val (basisVector 7)
  have hs : norm (basisVector 0 + g.val.val (basisVector 7)) = 1 := by
    have h := automorphism_norm g.val (basisVector 0 + basisVector 7)
    rw [map_add,g.property] at h
    simpa [norm,basisVector] using h
  rw [first_basis_norm_add,hn,zero_add] at hs
  exact hs

def partnerOf (g : fixingFirstVector (K := K)) : SingularPartners K :=
  ⟨g.val.val (basisVector 7),by
    refine ⟨?_,?_,fixingFirstVector_partner_last g⟩
    · simpa [trace,basisVector] using automorphism_trace g.val (basisVector 7)
    · simpa [norm,basisVector] using automorphism_norm g.val (basisVector 7)⟩

theorem chartReducer_fixes_first (y : Carrier K) :
    (chartReducer y).val (basisVector 0) = basisVector 0 := by
  ext i; fin_cases i <;>
    simp [chartReducer,rootA,rootB,rootC,rootD,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,rootDLinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootFApply,basisVector]

def partnerSection (y : SingularPartners K) : fixingFirstVector (K := K) :=
  ⟨chartReducer y.val,chartReducer_fixes_first y.val⟩

theorem partnerSection_action (y : SingularPartners K) :
    (partnerSection y).val.val y.val = basisVector 7 := by
  have h := chartReducer_eq y.val y.property.1 y.property.2.1
    (by rw [y.property.2.2]; exact one_ne_zero)
  simpa [partnerSection,y.property.2.2] using h

def normalizedPair (g : fixingFirstVector (K := K)) : PairStabilizer.fixingPair (F := K) :=
  ⟨(partnerSection (partnerOf g)).val*g.val,by
    constructor
    · change (partnerSection (partnerOf g)).val.val (g.val.val _) = _
      rw [g.property,(partnerSection (partnerOf g)).property]
    · exact partnerSection_action (partnerOf g)⟩

def assemblePartner (y : SingularPartners K) (h : PairStabilizer.fixingPair (F := K)) :
    fixingFirstVector (K := K) :=
  ⟨(partnerSection y).val⁻¹*h.val,by
    change (partnerSection y).val.val.symm (h.val.val (basisVector 0)) = _
    rw [h.property.1]
    change (partnerSection y).val.val.symm (basisVector 0) = basisVector 0
    apply (partnerSection y).val.val.injective
    rw [(partnerSection y).val.val.apply_symm_apply,(partnerSection y).property]⟩

theorem partnerOf_assemble (y : SingularPartners K)
    (h : PairStabilizer.fixingPair (F := K)) : partnerOf (assemblePartner y h) = y := by
  apply Subtype.ext
  change (partnerSection y).val.val.symm (h.val.val (basisVector 7)) = y.val
  rw [h.property.2]
  change (partnerSection y).val.val.symm (basisVector 7) = y.val
  rw [← partnerSection_action y,(partnerSection y).val.val.symm_apply_apply]

/-- The actual vector stabilizer is the partner chart times the actual ordered-pair stabilizer. -/
def fixingFirstVectorEquivPartners : fixingFirstVector (K := K) ≃
    SingularPartners K × PairStabilizer.fixingPair (F := K) where
  toFun g := (partnerOf g,normalizedPair g)
  invFun p := assemblePartner p.1 p.2
  left_inv g := by
    apply Subtype.ext
    change (partnerSection (partnerOf g)).val⁻¹ *
      ((partnerSection (partnerOf g)).val*g.val) = g.val
    exact inv_mul_cancel_left _ _
  right_inv p := by
    apply Prod.ext
    · exact partnerOf_assemble _ _
    · change normalizedPair (assemblePartner p.1 p.2) = p.2
      apply Subtype.ext
      change (partnerSection (partnerOf (assemblePartner p.1 p.2))).val *
        ((partnerSection p.1).val⁻¹*p.2.val) = p.2.val
      rw [partnerOf_assemble]
      exact mul_inv_cancel_left _ _

theorem card_fixingFirstVector [Finite K] :
    Nat.card (fixingFirstVector (K := K)) =
      Nat.card K ^ 5 * Nat.card (PairStabilizer.fixingPair (F := K)) := by
  rw [Nat.card_congr fixingFirstVectorEquivPartners,Nat.card_prod,card_singularPartners]
theorem card_fixingFirstVector_SL2 [Finite K] :
    Nat.card (fixingFirstVector (K := K)) =
      Nat.card K ^ 5 * Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [card_fixingFirstVector,Nat.card_congr PairStabilizer.fixingPairEquivSL2.toEquiv]
end Atlas.G2
