/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianDeterminantGlue.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianDeterminantRows

/-!
# IcosianDeterminantGlue

Matrix glue with prescribed block determinants has explicit information
parameters. Encoding and decoding these parameters give the equivalence
used to count determinant-constrained glue words.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianDeterminantGlue.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


namespace Atlas.Codes
open scoped Matrix BigOperators

/-- Actual two-column glue with prescribed block determinants and a nonzero
common second row. -/
def IcosianDeterminantGlue {F : Type*} [Field F] (d : Fin 3 → F) :=
  {m : icosianMatrixGlue F // (∀ i,Matrix.det (m.val i)=d i) ∧
    (fun j => m.val 0 1 j)≠0}

def IcosianDeterminantParameters {F : Type*} [Field F] (d : Fin 3 → F) :=
  (y : {y : IcosianRow F // y≠0}) ×
    (IcosianDetRow y.val (d 0) × IcosianDetRow y.val (d 1))

noncomputable def icosianDeterminantEncode {F : Type*} [Field F]
    (d : Fin 3 → F) (p : IcosianDeterminantParameters d) : IcosianMatrixGlueWord F :=
  fun i r j => if r=0 then ![p.2.1.val j,p.2.2.val j,-p.2.1.val j-p.2.2.val j] i
    else p.1.val j

theorem icosianDeterminantEncode_mem {F : Type*} [Field F]
    (d : Fin 3 → F) (p : IcosianDeterminantParameters d) :
    icosianDeterminantEncode d p∈icosianMatrixGlue F := by
  intro j
  change p.1.val j=p.1.val j ∧ p.1.val j=p.1.val j ∧
    p.2.1.val j+p.2.2.val j+(-p.2.1.val j-p.2.2.val j)=0
  exact ⟨rfl,rfl,by ring⟩

theorem icosianDeterminantEncode_det {F : Type*} [Field F]
    (d : Fin 3 → F) (hd : d 0+d 1+d 2=0) (p : IcosianDeterminantParameters d)
    (i : Fin 3) : Matrix.det (icosianDeterminantEncode d p i)=d i := by
  have h0 := p.2.1.property
  have h1 := p.2.2.property
  unfold icosianRowDet at h0 h1
  fin_cases i
  · simpa [Matrix.det_fin_two,icosianDeterminantEncode] using h0
  · simpa [Matrix.det_fin_two,icosianDeterminantEncode] using h1
  · simp [Matrix.det_fin_two,icosianDeterminantEncode]
    linear_combination -h0-h1-hd

noncomputable def icosianDeterminantEncodeElement {F : Type*} [Field F]
    (d : Fin 3 → F) (hd : d 0+d 1+d 2=0) (p : IcosianDeterminantParameters d) :
    IcosianDeterminantGlue d :=
  ⟨⟨icosianDeterminantEncode d p,icosianDeterminantEncode_mem d p⟩,
    fun i => icosianDeterminantEncode_det d hd p i,p.1.property⟩

noncomputable def icosianDeterminantDecode {F : Type*} [Field F]
    (d : Fin 3 → F) (m : IcosianDeterminantGlue d) : IcosianDeterminantParameters d :=
  ⟨⟨fun j => m.val.val 0 1 j,m.property.2⟩,
    ⟨⟨fun j => m.val.val 0 0 j,by
      simpa [icosianRowDet,Matrix.det_fin_two] using m.property.1 0⟩,
    ⟨fun j => m.val.val 1 0 j,by
      have h := (icosianMatrixGlue_constraints _).mp m.val.property
      simpa [icosianRowDet,Matrix.det_fin_two,(h 0).1,(h 1).1] using m.property.1 1⟩⟩⟩

noncomputable def icosianDeterminantGlueEquiv {F : Type*} [Field F]
    (d : Fin 3 → F) (hd : d 0+d 1+d 2=0) :
    IcosianDeterminantParameters d ≃ IcosianDeterminantGlue d where
  toFun := icosianDeterminantEncodeElement d hd
  invFun := icosianDeterminantDecode d
  left_inv p := by
    cases p
    rfl
  right_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    funext i r j
    have h := ((icosianMatrixGlue_constraints _).mp m.val.property) j
    fin_cases i <;> fin_cases r <;>
      simp only [icosianDeterminantEncodeElement,icosianDeterminantEncode,
        icosianDeterminantDecode] <;> try rfl
    · exact h.1
    · change -m.val.val 0 0 j-m.val.val 1 0 j=m.val.val 2 0 j
      linear_combination -h.2.2
    · exact h.1.trans h.2.1

noncomputable def icosianDeterminantParameterEquiv {F : Type*} [Field F]
    (d : Fin 3 → F) : IcosianDeterminantParameters d ≃
      ({y : IcosianRow F // y≠0} × (F × F)) :=
  Equiv.sigmaEquivProdOfEquiv (fun y => Equiv.prodCongr
    (icosianDetRowEquiv y.val y.property (d 0)).symm
    (icosianDetRowEquiv y.val y.property (d 1)).symm)

theorem icosianNonzeroRows_card {F : Type*} [Field F] [Finite F] :
    Nat.card {y : IcosianRow F // y≠0}=Nat.card F^2-1 := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp [IcosianRow,Nat.card_eq_fintype_card]

theorem icosianDeterminantGlue_card {F : Type*} [Field F] [Finite F]
    (d : Fin 3 → F) (hd : d 0+d 1+d 2=0) :
    Nat.card (IcosianDeterminantGlue d)=(Nat.card F^2-1)*Nat.card F^2 := by
  rw [← Nat.card_congr (icosianDeterminantGlueEquiv d hd),
    Nat.card_congr (icosianDeterminantParameterEquiv d),Nat.card_prod,
    Nat.card_prod,icosianNonzeroRows_card,pow_two]

theorem icosianDeterminantGlue_card_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=4) (d : Fin 3 → F) (hd : d 0+d 1+d 2=0) :
    Nat.card (IcosianDeterminantGlue d)=240 := by
  rw [icosianDeterminantGlue_card d hd,hF]
  norm_num

end Atlas.Codes
