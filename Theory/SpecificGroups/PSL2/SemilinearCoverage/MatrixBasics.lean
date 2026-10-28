module

public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Matrix coordinates for binary PSL₂ automorphism coverage

The upper root group here is the existing upper-unipotent subgroup of SL₂;
the Borel is its actual normalizer. The triangular conjugation formula and
Sylow subgroup are supplied by the SL₂ library. These coordinate lemmas let
the automorphism proof use those exact groups and the canonical PSL₂ quotient.

The matrix conventions and Weyl calculation are adapted from
`BenderSuzuki/Converse/PSL2.lean`, preserving that development. They support
the automorphism assertion in GLS2, Chapter G, immediately before Theorem
26.24, Step 5 (`refs/KGroup/GLS2/ChapterG.tex`).
-/

namespace Theory.PSL2.SemilinearCoverage

public abbrev SL2 (K : Type*) [Field K] := Matrix.SpecialLinearGroup (Fin 2) K

variable {K : Type*} [Field K]

public abbrev uni (t : K) : SL2 K :=
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one t

public abbrev Unip (K : Type*) [Field K] : Subgroup (SL2 K) :=
  Matrix.SpecialLinearGroup.upperUnipotent K

public abbrev Borel (K : Type*) [Field K] : Subgroup (SL2 K) :=
  Matrix.SpecialLinearGroup.rankOneBorel K

/-- The determinant-one diagonal matrix with upper-left entry `r`. -/
@[expose] public def tor (r : Kˣ) : SL2 K :=
  ⟨!![(r : K), 0; 0, (↑r⁻¹ : K)], by simp [Matrix.det_fin_two]⟩

@[simp] public theorem tor_val (r : Kˣ) :
    (tor r).val = !![(r : K), 0; 0, (↑r⁻¹ : K)] := rfl

@[simp] public theorem uni_val (t : K) : (uni t).val = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, Matrix.SpecialLinearGroup.transvection_coe]

public theorem mem_Unip_iff (A : SL2 K) : A ∈ Unip K ↔ ∃ t : K, A = uni t := by
  simpa only [eq_comm] using Matrix.SpecialLinearGroup.mem_upperUnipotent K A

public theorem uni_injective : Function.Injective (uni : K → SL2 K) := by
  intro s t h
  have he := congrArg (fun A : SL2 K => A.val 0 1) h
  simpa using he

public theorem uni_mul_uni (s t : K) : uni s * uni t = uni (s + t) :=
  (Matrix.SpecialLinearGroup.transvection_add zero_ne_one s t).symm

public theorem mem_Borel_iff (A : SL2 K) : A ∈ Borel K ↔ A.val 1 0 = 0 :=
  Matrix.SpecialLinearGroup.mem_rankOneBorel_iff A

public theorem Unip_le_Borel : Unip K ≤ Borel K :=
  (Matrix.SpecialLinearGroup.upperUnipotent K).le_normalizer

public theorem Borel_conj_uni {A : SL2 K} (hA : A ∈ Borel K) (t : K) :
    A * uni t * A⁻¹ = uni (A.val 0 0 ^ 2 * t) :=
  Matrix.SpecialLinearGroup.triangular_conj_upper ((mem_Borel_iff A).mp hA) t

public theorem Unip_conj_mem {b u : SL2 K} (hb : b ∈ Borel K) (hu : u ∈ Unip K) :
    b * u * b⁻¹ ∈ Unip K :=
  (Subgroup.mem_normalizer_iff.mp hb u).mp hu

variable [CharP K 2]

/-- The characteristic-two Weyl involution. -/
@[expose] public def weyl (K : Type*) [Field K] [CharP K 2] : SL2 K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

@[simp] public theorem weyl_val : (weyl K).val = !![0, 1; 1, 0] := rfl

public theorem weyl_sq : weyl K * weyl K = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

public theorem weyl_notMem_Borel : weyl K ∉ Borel K := by
  rw [mem_Borel_iff]
  simp

end Theory.PSL2.SemilinearCoverage
