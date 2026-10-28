module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/PointStrataCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.PointOrbits

/-! Coordinate charts count the four singular-point strata and hence the subdegrees. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion
variable (K : Type*) [Field K]

abbrev PolarSingularVectors := {x : SingularOctonions K // x.val 7 = 0}

def polarSingularEquiv : PolarSingularVectors K ≃ K × (Σ u : Fin 2 → K, Atlas.Orthogonal.BRemaining u) where
  toFun x := (x.val.val 0,⟨![x.val.val 1,x.val.val 2],
    ⟨(![-x.val.val 6,-x.val.val 5],x.val.val 3),by
      have ht : x.val.val 4 = -x.val.val 3 := eq_neg_of_add_eq_zero_right x.val.prop.1
      have hn := x.val.prop.2
      simp [SplitOctonion.norm,x.prop,ht] at hn
      simp [Atlas.DotProduct.functional,Fin.sum_univ_two]
      linear_combination -hn⟩⟩)
  invFun p := ⟨⟨![p.1,p.2.1 0,p.2.1 1,p.2.2.val.2,-p.2.2.val.2,
    -p.2.2.val.1 1,-p.2.2.val.1 0,0],by
      constructor
      · simp [trace]
      · have hn := p.2.2.prop
        simp [Atlas.DotProduct.functional,Fin.sum_univ_two] at hn
        simp [SplitOctonion.norm]
        linear_combination -hn⟩,by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have ht : x.val.val 4 = -x.val.val 3 := eq_neg_of_add_eq_zero_right x.val.prop.1
    funext i
    fin_cases i <;> simp [ht,x.prop]
  right_inv p := by
    apply Prod.ext (by rfl)
    apply Sigma.ext (by ext i; fin_cases i <;> rfl)
    apply heq_of_eq
    apply Subtype.ext
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · rfl

theorem card_polarSingularVectors [Finite K] : Nat.card (PolarSingularVectors K) = Nat.card K ^ 5 := by
  classical
  let := Fintype.ofFinite K
  rw [Nat.card_congr (polarSingularEquiv K),Nat.card_prod,Nat.card_sigma]
  simp_rw [Atlas.Orthogonal.card_remainingB]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    Nat.card_fun,Nat.card_fin,Nat.cast_id,← pow_add]
  ring

abbrev NonzeroPolarSingularVectors := {x : PolarSingularVectors K // x.val.val ≠ 0}

theorem card_nonzeroPolarSingularVectors [Finite K] :
    Nat.card (NonzeroPolarSingularVectors K) = Nat.card K ^ 5 - 1 := by
  classical
  let := Fintype.ofFinite K
  let : Unique {x : PolarSingularVectors K // x.val.val = 0} :=
    { default := ⟨⟨⟨0,by simp [trace,SplitOctonion.norm]⟩,rfl⟩,rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext (Subtype.ext x.prop)) }
  have hz : Fintype.card {x : PolarSingularVectors K // x.val.val = 0} = 1 := Fintype.card_unique
  change Nat.card {x : PolarSingularVectors K // ¬ x.val.val = 0} = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hz,
    ← Nat.card_eq_fintype_card,card_polarSingularVectors]

abbrev PolarSingularPoints := {p : SingularPoints K // p.val.rep 7 = 0}

theorem polar_smul_iff (a : Kˣ) (x : Carrier K) :
    ((trace (a • x) = 0 ∧ SplitOctonion.norm (a • x) = 0) ∧ (a • x) 7 = 0) ↔
      ((trace x = 0 ∧ SplitOctonion.norm x = 0) ∧ x 7 = 0) := by
  rw [singular_smul_iff K]
  simp [Units.smul_def,a.ne_zero]

def polarNonzeroConeEquiv : Atlas.LinearAlgebra.NonzeroCone
    (fun x : Carrier K => (trace x = 0 ∧ SplitOctonion.norm x = 0) ∧ x 7 = 0) ≃
      NonzeroPolarSingularVectors K where
  toFun x := ⟨⟨⟨x.val,x.prop.2.1⟩,x.prop.2.2⟩,x.prop.1⟩
  invFun x := ⟨x.val.val.val,x.prop,x.val.val.prop,x.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

def polarConePointsEquiv : Atlas.LinearAlgebra.ConePoints (F := K)
    (fun x : Carrier K => (trace x = 0 ∧ SplitOctonion.norm x = 0) ∧ x 7 = 0) ≃
      PolarSingularPoints K where
  toFun p := ⟨⟨p.val,p.prop.1⟩,p.prop.2⟩
  invFun p := ⟨p.val.val,p.val.prop,p.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_polarSingularPoints [Finite K] :
    Nat.card (PolarSingularPoints K) = (Nat.card K ^ 5 - 1) / (Nat.card K - 1) := by
  rw [← Nat.card_congr (polarConePointsEquiv K),Atlas.LinearAlgebra.card_conePoints _ (polar_smul_iff K),
    Nat.card_congr (polarNonzeroConeEquiv K),card_nonzeroPolarSingularVectors]

abbrev LowerVectors := {x : Carrier K // inLowerPlane x}

def lowerVectorsEquiv : LowerVectors K ≃ (Fin 3 → K) where
  toFun x := ![x.val 0,x.val 1,x.val 2]
  invFun t := ⟨![t 0,t 1,t 2,0,0,0,0,0],by simp [inLowerPlane]⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨h3,h4,h5,h6,h7⟩ := x.prop
    funext i; fin_cases i <;> simp [h3,h4,h5,h6,h7]
  right_inv t := by funext i; fin_cases i <;> rfl

theorem card_lowerVectors [Finite K] : Nat.card (LowerVectors K) = Nat.card K ^ 3 := by
  rw [Nat.card_congr (lowerVectorsEquiv K),Nat.card_fun,Nat.card_fin]

theorem lower_smul_iff (a : Kˣ) (x : Carrier K) : inLowerPlane (a • x) ↔ inLowerPlane x := by
  simp [inLowerPlane,Units.smul_def,a.ne_zero]

def lowerConePointsEquiv : Atlas.LinearAlgebra.ConePoints (F := K) (inLowerPlane (K := K)) ≃
    {p : SingularPoints K // inLowerPlane p.val.rep} where
  toFun p := ⟨⟨p.val,by
    obtain ⟨h3,h4,h5,h6,h7⟩ := p.prop
    constructor <;> simp [trace,SplitOctonion.norm,h3,h4,h5,h6,h7]⟩,p.prop⟩
  invFun p := ⟨p.val.val,p.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

def lowerNonzeroConeEquiv : Atlas.LinearAlgebra.NonzeroCone (inLowerPlane (K := K)) ≃
    {x : LowerVectors K // x.val ≠ 0} where
  toFun x := ⟨⟨x.val,x.prop.2⟩,x.prop.1⟩
  invFun x := ⟨x.val.val,x.prop,x.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_nonzeroLowerVectors [Finite K] : Nat.card {x : LowerVectors K // x.val ≠ 0} =
    Nat.card K ^ 3 - 1 := by
  classical
  let := Fintype.ofFinite K
  let : Unique {x : LowerVectors K // x.val = 0} :=
    { default := ⟨⟨0,by simp [inLowerPlane]⟩,rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext x.prop) }
  have hz : Fintype.card {x : LowerVectors K // x.val = 0} = 1 := Fintype.card_unique
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hz,
    ← Nat.card_eq_fintype_card,card_lowerVectors]

theorem card_lowerSingularPoints [Finite K] :
    Nat.card {p : SingularPoints K // inLowerPlane p.val.rep} =
      (Nat.card K ^ 3 - 1) / (Nat.card K - 1) := by
  rw [← Nat.card_congr (lowerConePointsEquiv K),Atlas.LinearAlgebra.card_conePoints _ (lower_smul_iff K),
    Nat.card_congr (lowerNonzeroConeEquiv K),card_nonzeroLowerVectors]

end Atlas.G2
