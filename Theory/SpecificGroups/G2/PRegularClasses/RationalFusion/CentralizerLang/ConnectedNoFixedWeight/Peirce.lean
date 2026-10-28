module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.FixedIdempotents
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

/-!
# The literal determinant-one Peirce action

Coordinates 0, 5, 6 form the Peirce three-space between the idempotents at 3
and 4. An octonion automorphism fixing those idempotents preserves this space.
Its alternating triple product is the determinant, so restriction has
determinant one. The products of pairs of its basis vectors give coordinates
1, 2, 7, proving that restriction is faithful. Commutation with the G₂ torus
then becomes the usual diagonal-matrix weight relation.

These are coordinate lemmas for Steinberg 8.5 and 12.5,
`refs/KGroup/GLS3/Chapter2St2.tex`; the multiplication table is the licensed
ATLAS port (`LICENSES/ATLAS.txt`). No surjectivity onto SL₃ is asserted here.
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
variable {K : Type*} [Field K]

def peirceIndex : Fin 3 → Fin 8 := ![0,5,6]

def peirceVector (x : Fin 3 → K) : Carrier K := ![x 0,0,0,0,0,x 1,x 2,0]

def peirceMatrix (g : Model K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => g.val (basisVector (peirceIndex j)) (peirceIndex i)

private theorem peirceVector_eq (x : Carrier K)
    (hl : mul (basisVector 3) x = x) (hr : mul x (basisVector 4) = x) :
    x = peirceVector (fun i => x (peirceIndex i)) := by
  have h1 : x 1 = 0 := by simpa [mul, basisVector] using (congrFun hl 1).symm
  have h2 : x 2 = 0 := by simpa [mul, basisVector] using (congrFun hl 2).symm
  have h3 : x 3 = 0 := by simpa [mul, basisVector] using (congrFun hr 3).symm
  have h4 : x 4 = 0 := by simpa [mul, basisVector] using (congrFun hl 4).symm
  have h7 : x 7 = 0 := by simpa [mul, basisVector] using (congrFun hl 7).symm
  ext i
  fin_cases i <;> simp [peirceVector, peirceIndex, h1, h2, h3, h4, h7]

theorem peirce_basis_image (g : Model K)
    (h3 : g.val (basisVector 3) = basisVector 3)
    (h4 : g.val (basisVector 4) = basisVector 4) (j : Fin 3) :
    g.val (basisVector (peirceIndex j)) = peirceVector (fun i => peirceMatrix g i j) := by
  apply peirceVector_eq
  · rw [← h3, ← automorphism_mul]
    congr 1
    fin_cases j <;> ext i <;> fin_cases i <;> simp [mul, basisVector, peirceIndex]
  · rw [← h4, ← automorphism_mul]
    congr 1
    fin_cases j <;> ext i <;> fin_cases i <;> simp [mul, basisVector, peirceIndex]

/-- The alternating triple product forces determinant one on the Peirce three-space. -/
theorem peirceMatrix_det (g : Model K)
    (h3 : g.val (basisVector 3) = basisVector 3)
    (h4 : g.val (basisVector 4) = basisVector 4) : (peirceMatrix g).det = 1 := by
  have hprod : mul (mul (basisVector 0 : Carrier K) (basisVector 5)) (basisVector 6) =
      -(basisVector 4) := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have h := congrArg (fun x : Carrier K => x 4) (congrArg g.val hprod)
  rw [automorphism_mul, automorphism_mul, map_neg, h4] at h
  rw [show (basisVector 0 : Carrier K) = basisVector (peirceIndex 0) from rfl,
    show (basisVector 5 : Carrier K) = basisVector (peirceIndex 1) from rfl,
    show (basisVector 6 : Carrier K) = basisVector (peirceIndex 2) from rfl,
    peirce_basis_image g h3 h4 0, peirce_basis_image g h3 h4 1,
    peirce_basis_image g h3 h4 2] at h
  simp [mul, peirceVector, basisVector] at h
  rw [Matrix.det_fin_three]
  linear_combination -h

/-- Products of the three Peirce basis vectors recover the opposite three-space. -/
theorem peirceMatrix_injective_on_fixers (g h : Model K)
    (hg3 : g.val (basisVector 3) = basisVector 3)
    (hg4 : g.val (basisVector 4) = basisVector 4)
    (hh3 : h.val (basisVector 3) = basisVector 3)
    (hh4 : h.val (basisVector 4) = basisVector 4)
    (he : peirceMatrix g = peirceMatrix h) : g = h := by
  have hb (j : Fin 3) : g.val (basisVector (peirceIndex j)) =
      h.val (basisVector (peirceIndex j)) := by
    rw [peirce_basis_image g hg3 hg4, peirce_basis_image h hh3 hh4, he]
  have h0 : g.val (basisVector 0) = h.val (basisVector 0) := hb 0
  have h5 : g.val (basisVector 5) = h.val (basisVector 5) := hb 1
  have h6 : g.val (basisVector 6) = h.val (basisVector 6) := hb 2
  have h05 : mul (basisVector 0 : Carrier K) (basisVector 5) = basisVector 1 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have h60 : mul (basisVector 6 : Carrier K) (basisVector 0) = basisVector 2 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have h56 : mul (basisVector 5 : Carrier K) (basisVector 6) = basisVector 7 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro i
  suffices g.val (basisVector i) = h.val (basisVector i) by
    simpa [Pi.basisFun_apply, basisVector] using this
  fin_cases i <;> dsimp only
  · exact h0
  · change g.val (basisVector (1 : Fin 8)) = h.val (basisVector (1 : Fin 8))
    rw [← h05, automorphism_mul, automorphism_mul, h0, h5]
  · change g.val (basisVector (2 : Fin 8)) = h.val (basisVector (2 : Fin 8))
    rw [← h60, automorphism_mul, automorphism_mul, h6, h0]
  · change g.val (basisVector (3 : Fin 8)) = h.val (basisVector (3 : Fin 8))
    rw [hg3, hh3]
  · change g.val (basisVector (4 : Fin 8)) = h.val (basisVector (4 : Fin 8))
    rw [hg4, hh4]
  · exact h5
  · exact h6
  · change g.val (basisVector (7 : Fin 8)) = h.val (basisVector (7 : Fin 8))
    rw [← h56, automorphism_mul, automorphism_mul, h5, h6]

def peirceWeights (l m : Kˣ) : Fin 3 → Kˣ := ![l,l⁻¹*m,m⁻¹]

theorem peirceWeights_prod (l m : Kˣ) : ∏ i, peirceWeights l m i = 1 := by
  simp [peirceWeights, Fin.prod_univ_succ]

theorem peirceWeights_eq (l m : Kˣ) (i : Fin 3) :
    peirceWeights l m i = torusWeights l m (peirceIndex i) := by
  fin_cases i <;> rfl

theorem peirceMatrix_weight_relation (l m : Kˣ) (g : Model K)
    (hg : g ∈ Subgroup.centralizer ({torus l m} : Set (Model K))) (i j : Fin 3) :
    (peirceWeights l m i : K) * peirceMatrix g i j =
      (peirceWeights l m j : K) * peirceMatrix g i j := by
  by_cases he : peirceWeights l m i = peirceWeights l m j
  · rw [he]
  · have hz := centralizer_entry_zero l m g hg (peirceIndex i) (peirceIndex j)
      (by simpa only [← peirceWeights_eq] using he)
    change peirceMatrix g i j = 0 at hz
    rw [hz, mul_zero, mul_zero]

end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
