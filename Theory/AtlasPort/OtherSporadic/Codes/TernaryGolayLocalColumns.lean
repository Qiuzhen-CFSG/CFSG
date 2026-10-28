/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolayLocalColumns.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayLocalColumnData

/-!
# TernaryGolayLocalColumns

Admissible information triples determine code-preserving coordinate permutations.
The encoder and decoder recover each column from the marked information set.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolayLocalColumns.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes

def ternaryPermutationTriple (σ : Equiv.Perm (Fin 12)) : TernaryInformationTriple :=
  ![σ.symm 3, σ.symm 4, σ.symm 11]

def TernaryFixFirstThree (σ : Equiv.Perm (Fin 12)) : Prop :=
  σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2

def TernaryCoordinatePreserves (σ : Equiv.Perm (Fin 12)) : Prop :=
  ∀ w ∈ ternaryGolay, (fun i => w (σ.symm i)) ∈ ternaryGolay

theorem ternaryPermutation_information (σ : Equiv.Perm (Fin 12))
    (hσ : TernaryFixFirstThree σ) (hp : TernaryCoordinatePreserves σ)
    (p : TernaryParameters) :
    ternaryEncoder (ternaryInformationMap (ternaryPermutationTriple σ) p) =
      fun i => ternaryEncoder p (σ.symm i) := by
  have hw := (ternaryGolay_mem_iff_decode _).mp
    (hp (ternaryEncoder p) ⟨p,rfl⟩)
  have h0 : σ.symm 0 = 0 := (σ.symm_apply_eq.mpr hσ.1.symm)
  have h1 : σ.symm 1 = 1 := (σ.symm_apply_eq.mpr hσ.2.1.symm)
  have h2 : σ.symm 2 = 2 := (σ.symm_apply_eq.mpr hσ.2.2.symm)
  have he : ternaryDecoder (fun i => ternaryEncoder p (σ.symm i)) =
      ternaryInformationMap (ternaryPermutationTriple σ) p := by
    funext k
    fin_cases k
    · change ternaryEncoder p (σ.symm 0) = p 0
      rw [h0]; rfl
    · change ternaryEncoder p (σ.symm 1) = p 1
      rw [h1]; rfl
    · change ternaryEncoder p (σ.symm 2) = p 2
      rw [h2]; rfl
    · rfl
    · rfl
    · rfl
  rw [he] at hw
  exact hw

theorem ternaryPermutation_column (σ : Equiv.Perm (Fin 12))
    (hσ : TernaryFixFirstThree σ) (hp : TernaryCoordinatePreserves σ) (i : Fin 12) :
    ternaryInformationColumn (ternaryPermutationTriple σ) i =
      ternaryBasisColumn (σ.symm i) := by
  funext k
  exact congrFun (ternaryPermutation_information σ hσ hp (Pi.single k 1)) i

theorem ternaryPermutationTriple_admissible (σ : Equiv.Perm (Fin 12))
    (hσ : TernaryFixFirstThree σ) (hp : TernaryCoordinatePreserves σ) :
    TernaryAdmissibleTriple (ternaryPermutationTriple σ) := by
  have hg (i : Fin 12) (hi : 3 ≤ i.val) : 3 ≤ (σ.symm i).val := by
    by_contra h
    have he : σ.symm i = 0 ∨ σ.symm i = 1 ∨ σ.symm i = 2 := by
      have hb : (σ.symm i).val < 3 := by omega
      omega
    rcases he with he | he | he
    · have hh := congrArg σ he; simp only [Equiv.apply_symm_apply,hσ.1] at hh; subst i; contradiction
    · have hh := congrArg σ he; simp only [Equiv.apply_symm_apply,hσ.2.1] at hh; subst i; contradiction
    · have hh := congrArg σ he; simp only [Equiv.apply_symm_apply,hσ.2.2] at hh; subst i; contradiction
  refine ⟨?_,?_,?_⟩
  · intro k; fin_cases k <;> apply hg <;> decide
  · have hi : Function.Injective (fun k : Fin 3 => (![3,4,11] k : Fin 12)) := by decide
    have he : ternaryPermutationTriple σ = σ.symm ∘ (fun k : Fin 3 => (![3,4,11] k : Fin 12)) := by
      funext k; fin_cases k <;> rfl
    rw [he]
    exact σ.symm.injective.comp hi
  · intro k
    rw [ternaryPermutation_column σ hσ hp]
    exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

theorem ternaryPermutationTriple_injective (σ τ : Equiv.Perm (Fin 12))
    (hσ : TernaryFixFirstThree σ) (hτ : TernaryFixFirstThree τ)
    (hp : TernaryCoordinatePreserves σ) (hq : TernaryCoordinatePreserves τ)
    (he : ternaryPermutationTriple σ = ternaryPermutationTriple τ) : σ = τ := by
  have hs : σ.symm = τ.symm := by
    apply Equiv.ext
    intro i
    apply ternaryBasisColumn_injective
    rw [← ternaryPermutation_column σ hσ hp, ← ternaryPermutation_column τ hτ hq, he]
  have hh := congrArg Equiv.symm hs
  simpa using hh

end Atlas.Codes
