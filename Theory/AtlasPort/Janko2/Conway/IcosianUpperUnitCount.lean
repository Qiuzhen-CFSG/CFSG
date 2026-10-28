/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianUpperUnitCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCScalarNecessity

/-!
# IcosianUpperUnitCount

Upper-triangular determinant-one matrices over the four-element field are explicitly
parametrized. Lifting through scalar reduction counts the local unit parameters.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianUpperUnitCount.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes
open scoped Matrix

abbrev IcosianUpperSL2 := {a : IcosianSpecialLinear // a 1 0=0}

def icosianUpperSL2Parameter (p : GoldenFourˣ × GoldenFour) : IcosianUpperSL2 :=
  ⟨icosianGlueMatrix p.1 p.2,rfl⟩

theorem icosianUpperSL2Parameter_injective : Function.Injective icosianUpperSL2Parameter := by
  rintro ⟨s,c⟩ ⟨t,d⟩ h
  have hs : s=t := Units.ext (congrArg (fun z : IcosianUpperSL2 => z.val 1 1) h)
  have hc : c=d := congrArg (fun z : IcosianUpperSL2 => z.val 0 1) h
  exact Prod.ext hs hc

theorem icosianUpperSL2Parameter_surjective : Function.Surjective icosianUpperSL2Parameter := by
  intro a
  have hd : a.val 0 0*a.val 1 1=1 := by
    have h := a.val.property
    rw [Matrix.det_fin_two,a.property,mul_zero,sub_zero] at h
    exact h
  have hn : a.val 1 1≠0 := by intro h; rw [h,mul_zero] at hd; exact zero_ne_one hd
  let s : GoldenFourˣ := Units.mk0 (a.val 1 1) hn
  have hi : a.val 0 0=(s : GoldenFour)⁻¹ := by
    change a.val 0 0=(a.val 1 1)⁻¹
    calc
      a.val 0 0=a.val 0 0*(a.val 1 1*(a.val 1 1)⁻¹) := by rw [mul_inv_cancel₀ hn,mul_one]
      _=(a.val 0 0*a.val 1 1)*(a.val 1 1)⁻¹ := by ring
      _=(a.val 1 1)⁻¹ := by rw [hd,one_mul]
  refine ⟨(s,a.val 0 1),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [icosianUpperSL2Parameter,icosianGlueMatrix,hi,a.property,s]

def icosianUpperSL2Equiv : (GoldenFourˣ × GoldenFour) ≃ IcosianUpperSL2 :=
  Equiv.ofBijective icosianUpperSL2Parameter
    ⟨icosianUpperSL2Parameter_injective,icosianUpperSL2Parameter_surjective⟩

theorem icosianUpperSL2_card : Nat.card IcosianUpperSL2=12 := by
  rw [← Nat.card_congr icosianUpperSL2Equiv,Nat.card_prod]
  simp [Nat.card_eq_fintype_card,Fintype.card_units,goldenFour_card]

abbrev IcosianUpperUnit := {u : icosianNormOneGroup // (icosianNormOneReduction u) 1 0=0}

attribute [local irreducible] icosianNormOneReductionCoordinates

def icosianUpperUnitEquiv : IcosianUpperUnit ≃ IcosianUpperSL2 × icosianNormOneReduction.ker :=
  (icosianNormOneReductionCoordinates.subtypeEquiv (fun u => by
    change (icosianNormOneReduction u) 1 0=0 ↔
      (icosianNormOneReductionCoordinates u).1 1 0=0
    rw [icosianNormOneReductionCoordinates_fst])).trans
      Equiv.prodSubtypeFstEquivSubtypeProd

theorem icosianUpperUnit_card : Nat.card IcosianUpperUnit=24 := by
  rw [Nat.card_congr icosianUpperUnitEquiv,Nat.card_prod,icosianUpperSL2_card,
    icosianNormOneReduction_kernel_card]

def icosianUpperDiagonal (a : IcosianUpperSL2) : IcosianSpecialLinear :=
  ⟨!![a.val 0 0,0;0,a.val 1 1],by
    have h := a.val.property
    rw [Matrix.det_fin_two,a.property,mul_zero,sub_zero] at h
    simpa [Matrix.det_fin_two] using h⟩

abbrev IcosianRepeatedUnitParameters :=
  (a : IcosianUpperUnit) × {b : icosianNormOneGroup //
    icosianNormOneReduction b=icosianUpperDiagonal ⟨icosianNormOneReduction a.val,a.property⟩}

theorem icosianRepeatedUnitParameters_card : Nat.card IcosianRepeatedUnitParameters=48 := by
  let : Fintype IcosianUpperUnit := Fintype.ofFinite _
  rw [Nat.card_sigma]
  simp_rw [icosianNormOneReduction_fiber_card]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,icosianUpperUnit_card]
  rfl

end Atlas.Conway
