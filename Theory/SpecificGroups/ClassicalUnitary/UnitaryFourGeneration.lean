module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal

/-!
# Generation by the two unitary four-space flag parabolics

The stabilizers of the isotropic coordinate point and plane generate the
antidiagonal special unitary group in characteristic two. Two coordinate
permutations in these stabilizers move a nonzero first-column entry to the
last coordinate. A matrix from the already constructed point radical then
clears that isotropic column. Reversing the coordinates leaves a matrix in
the point stabilizer. This also gives an explicit opposite-cell factorization.

The proof uses only the stored field involution and characteristic two; it
includes the parameter q = 2. The projective statement uses the literal
canonical map to the image in PGL. We also record properness, incomparability
and strictness of the whole flag overlap, without identifying it with a Sylow
subgroup or asserting maximality here.

Source: the generation clause of Aschbacher--Smith, Definitions F.1.6--7,
printed p.261, for the U₄(q) amalgam in F.1.12(I)(6), printed p.263 of
`refs/quasithin.pdf`. This is an intrinsic matrix result, not the classification
of weak BN-pairs or the assertion about the degree-two extension.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- An involutory isometry has determinant one in characteristic two. -/
def involutionElement (M : Matrix (Fin 4) (Fin 4) F)
    (hM : M * M = 1)
    (hu : (form F σ hσ).conjTranspose M * gram F * M = gram F) :
    SU F (form F σ hσ) := by
  refine ⟨⟨M, M, hM, hM⟩, hu, ?_⟩
  apply Units.ext
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_one] at hd
  apply (iterateFrobeniusEquiv F 2 1).injective
  change M.det ^ (2 ^ 1) = (1 : F) ^ (2 ^ 1)
  simpa [pow_two] using hd

def pairSwapMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

def middleSwapMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]

def pairSwap : SU F (form F σ hσ) :=
  involutionElement F σ hσ (pairSwapMatrix F)
    (by ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [pairSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ])
    (by ext i j; fin_cases i <;> fin_cases j <;>
        simp [form, gram, pairSwapMatrix, HermitianForm.conjTranspose,
          Matrix.mul_apply, Fin.sum_univ_succ])

def middleSwap : SU F (form F σ hσ) :=
  involutionElement F σ hσ (middleSwapMatrix F)
    (by ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [middleSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ])
    (by ext i j; fin_cases i <;> fin_cases j <;>
        simp [form, gram, middleSwapMatrix, HermitianForm.conjTranspose,
          Matrix.mul_apply, Fin.sum_univ_succ])

theorem pairSwap_mem_plane : pairSwap F σ hσ ∈ planeParabolicSU F (form F σ hσ) := by
  rw [mem_planeParabolicSU]
  simp [pairSwap, involutionElement, pairSwapMatrix]

theorem middleSwap_mem_point : middleSwap F σ hσ ∈ pointParabolicSU F (form F σ hσ) := by
  rw [mem_pointParabolicSU]
  simp [middleSwap, involutionElement, middleSwapMatrix]

def reverse : SU F (form F σ hσ) :=
  pairSwap F σ hσ * middleSwap F σ hσ * pairSwap F σ hσ * middleSwap F σ hσ

theorem reverse_val : (reverse F σ hσ).val.val = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reverse, pairSwap, middleSwap, involutionElement, pairSwapMatrix,
      middleSwapMatrix, gram, Matrix.mul_apply, Fin.sum_univ_succ]

local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "Q" => planeParabolicSU F (form F σ hσ)

theorem reverse_mem_sup : reverse F σ hσ ∈ P ⊔ Q := by
  have ha : pairSwap F σ hσ ∈ P ⊔ Q := (le_sup_right : Q ≤ P ⊔ Q) (pairSwap_mem_plane F σ hσ)
  have hb : middleSwap F σ hσ ∈ P ⊔ Q := (le_sup_left : P ≤ P ⊔ Q) (middleSwap_mem_point F σ hσ)
  exact (P ⊔ Q).mul_mem ((P ⊔ Q).mul_mem ((P ⊔ Q).mul_mem ha hb) ha) hb

omit [Finite F] [CharP F 2] in
theorem column_isotropic (g : SU F (form F σ hσ)) (k : Fin 4) :
    σ (g.val.val 0 k) * g.val.val 3 k + σ (g.val.val 1 k) * g.val.val 2 k +
      σ (g.val.val 2 k) * g.val.val 1 k + σ (g.val.val 3 k) * g.val.val 0 k = 0 := by
  have hu := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M k k) g.property.1
  change ((form F σ hσ).conjTranspose g.val.val * gram F * g.val.val) k k = gram F k k at hu
  have hd : gram F k k = 0 := by fin_cases k <;> rfl
  rw [hd] at hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] at hu
  linear_combination hu

omit [Finite F] in
/-- A point radical sends an isotropic matrix column with nonzero last entry
onto the opposite coordinate point. The radical is also in the plane parabolic. -/
theorem exists_radical_clear_column (g : SU F (form F σ hσ)) (k : Fin 4)
    (hg : g.val.val 3 k ≠ 0) :
    ∃ c : RadicalCoordinates F σ,
      (radicalElement F σ hσ c).val.val *ᵥ (fun i => g.val.val i k) =
        ![0,0,0,g.val.val 3 k] := by
  let a := g.val.val 0 k / g.val.val 3 k
  let x := g.val.val 1 k / g.val.val 3 k
  let y := g.val.val 2 k / g.val.val 3 k
  have hiso : σ a + σ x * y + σ y * x + a = 0 := by
    dsimp [a, x, y]
    rw [map_div₀, map_div₀, map_div₀]
    have hs : σ (g.val.val 3 k) ≠ 0 := by simpa using hg
    field_simp [hg, hs]
    linear_combination column_isotropic F σ hσ g k
  have ht : σ a + σ (σ a) = σ x * y + σ y * x := by
    rw [hσ]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hiso
  let c : RadicalCoordinates F σ := ⟨x, y, σ a, ht⟩
  let r := radicalElement F σ hσ c
  have hclear : r.val.val *ᵥ (fun i => g.val.val i k) = ![0,0,0,g.val.val 3 k] := by
    have hscale (i : Fin 4) : g.val.val i k / g.val.val 3 k * g.val.val 3 k =
        g.val.val i k := div_mul_cancel₀ _ hg
    have h0 : g.val.val 0 k + σ y * g.val.val 1 k + σ x * g.val.val 2 k +
        σ a * g.val.val 3 k = 0 := by
      have he := congrArg (fun z : F => z * g.val.val 3 k) hiso
      dsimp [a, x, y] at he ⊢
      simp only [add_mul, mul_assoc, hscale, zero_mul] at he
      linear_combination he
    ext i
    fin_cases i
    · simpa [r, radicalElement, radicalMatrix, c, mulVec, dotProduct,
        Fin.sum_univ_succ, add_assoc] using h0
    · simp [r, radicalElement, radicalMatrix, c, mulVec, dotProduct,
        Fin.sum_univ_succ, x, div_mul_cancel₀ _ hg, CharTwo.add_self_eq_zero]
    · simp [r, radicalElement, radicalMatrix, c, mulVec, dotProduct,
        Fin.sum_univ_succ, y, div_mul_cancel₀ _ hg, CharTwo.add_self_eq_zero]
    · simp [r, radicalElement, radicalMatrix, c, mulVec, dotProduct, Fin.sum_univ_succ]
  exact ⟨c, hclear⟩

/-- The opposite point cell is a radical translate of the reverse Weyl cell. -/
theorem exists_radical_reverse_mul_mem_point (g : SU F (form F σ hσ))
    (hg : g.val.val 3 0 ≠ 0) :
    ∃ c : RadicalCoordinates F σ,
      reverse F σ hσ * radicalElement F σ hσ c * g ∈ P := by
  obtain ⟨c, hclear⟩ := exists_radical_clear_column F σ hσ g 0 hg
  let r := radicalElement F σ hσ c
  have hp : reverse F σ hσ * r * g ∈ P := by
    rw [mem_pointParabolicSU]
    have hc : (reverse F σ hσ * r * g).val.val *ᵥ Pi.single 0 1 =
        ![g.val.val 3 0,0,0,0] := by
      change ((reverse F σ hσ).val.val * r.val.val * g.val.val) *ᵥ _ = _
      rw [reverse_val, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_single_one]
      rw [show (g.val.val.col 0) = (fun i => g.val.val i 0) from rfl, hclear]
      ext i
      fin_cases i <;> simp [gram, mulVec, dotProduct, Fin.sum_univ_succ]
    exact ⟨by simpa using congrFun hc 1, by simpa using congrFun hc 2,
      by simpa using congrFun hc 3⟩
  exact ⟨c, hp⟩

/-- Generation from the point stabilizer and the adjacent coordinate swap. -/
theorem eq_top_of_point_and_pairSwap (H : Subgroup (SU F (form F σ hσ)))
    (hP : P ≤ H) (ha : pairSwap F σ hσ ∈ H) : H = ⊤ := by
  have hb : middleSwap F σ hσ ∈ H := hP (middleSwap_mem_point F σ hσ)
  have hw : reverse F σ hσ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) ha) hb
  have hlast (g : SU F (form F σ hσ)) (hg : g.val.val 3 0 ≠ 0) : g ∈ H := by
    obtain ⟨c, hc⟩ := exists_radical_reverse_mul_mem_point F σ hσ g hg
    have hr : radicalElement F σ hσ c ∈ H := hP
      (localSU_le_pointParabolicSU F _ (radicalElement_mem_local F σ hσ c))
    exact (H.mul_mem_cancel_left (H.mul_mem hw hr)).mp (hP hc)
  apply top_unique
  intro g _
  by_cases h3 : g.val.val 3 0 ≠ 0
  · exact hlast g h3
  by_cases h2 : g.val.val 2 0 ≠ 0
  · apply (H.mul_mem_cancel_left ha).mp
    apply hlast
    simpa [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h2
  by_cases h1 : g.val.val 1 0 ≠ 0
  · apply (H.mul_mem_cancel_left (H.mul_mem ha hb)).mp
    apply hlast
    simpa [pairSwap, middleSwap, involutionElement, pairSwapMatrix, middleSwapMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] using h1
  have h0 : g.val.val 0 0 ≠ 0 := by
    intro h0
    apply GeneralLinearGroup.det_ne_zero g.val
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    fin_cases i <;> simp_all
  apply (H.mul_mem_cancel_left hw).mp
  apply hlast
  change ((reverse F σ hσ).val.val * g.val.val) 3 0 ≠ 0
  rw [reverse_val]
  simpa [gram, Matrix.mul_apply, Fin.sum_univ_succ] using h0

/-- The two actual matrix flag stabilizers generate SU₄. -/
theorem parabolics_sup_eq_top : P ⊔ Q = ⊤ :=
  eq_top_of_point_and_pairSwap F σ hσ (P ⊔ Q) le_sup_left
    ((le_sup_right : Q ≤ P ⊔ Q) (pairSwap_mem_plane F σ hσ))

/-- Generation descends along the literal projection onto the image in PGL. -/
theorem projective_parabolics_sup_eq_top :
    (P).map (project F (form F σ hσ)) ⊔ (Q).map (project F (form F σ hσ)) = ⊤ := by
  rw [← Subgroup.map_sup, parabolics_sup_eq_top, Subgroup.map_top_of_surjective _
    (project_surjective F (form F σ hσ))]

/-- The radical used in elimination fixes both members of the coordinate flag. -/
theorem radical_mem_borel (c : RadicalCoordinates F σ) :
    radicalElement F σ hσ c ∈ borelSU F (form F σ hσ) := by
  refine ⟨localSU_le_pointParabolicSU F _ (radicalElement_mem_local F σ hσ c), ?_⟩
  change radicalElement F σ hσ c ∈ Q
  rw [mem_planeParabolicSU]
  simp [radicalElement, radicalMatrix]

theorem pairSwap_not_mem_point : pairSwap F σ hσ ∉ P := by
  rw [mem_pointParabolicSU]
  simp [pairSwap, involutionElement, pairSwapMatrix]

theorem middleSwap_not_mem_plane : middleSwap F σ hσ ∉ Q := by
  rw [mem_planeParabolicSU]
  simp [middleSwap, involutionElement, middleSwapMatrix]

/-- Neither maximal flag type can contain the other. -/
theorem parabolics_incomparable : ¬ P ≤ Q ∧ ¬ Q ≤ P := by
  exact ⟨fun h => middleSwap_not_mem_plane F σ hσ (h (middleSwap_mem_point F σ hσ)),
    fun h => pairSwap_not_mem_point F σ hσ (h (pairSwap_mem_plane F σ hσ))⟩

theorem point_ne_top : P ≠ ⊤ := by
  intro h
  exact pairSwap_not_mem_point F σ hσ (h ▸ Subgroup.mem_top _)

theorem plane_ne_top : Q ≠ ⊤ := by
  intro h
  exact middleSwap_not_mem_plane F σ hσ (h ▸ Subgroup.mem_top _)

theorem borel_lt_point : borelSU F (form F σ hσ) < P := by
  apply lt_of_le_of_ne inf_le_left
  intro h
  exact (parabolics_incomparable F σ hσ).1 (h ▸ inf_le_right)

theorem borel_lt_plane : borelSU F (form F σ hσ) < Q := by
  apply lt_of_le_of_ne inf_le_right
  intro h
  exact (parabolics_incomparable F σ hσ).2 (h ▸ inf_le_left)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
