module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.WordMatrices
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.FusionProducts

/-!
# Local fusion from certified matrix evaluations

For each of the 26 nonzero normal forms, a positive word in the two ATLAS
program outputs conjugates that form to `u` or `z`. We certify `r * g = g * n`
and cancel in the group, avoiding inverse-matrix data for the conjugator.
The explicit witnesses and ATLAS attribution are recorded in `Conjugacy.Rows`.
The only outstanding inputs here identify the shared rows with the actual
program outputs and normal forms; no enumeration or subgroup-order premise
is used.
-/

public section
namespace Janko4.Simplicity
open Janko4.GeneratorCertificates ThreeLocalCertificates
open ThreeLocalCertificates.Conjugacy

private theorem conjugate_of_products {r g n : Model}
    {rr gr nr pr : Vector Nat 112}
    (hr : toMatrix r = decodeRows rr) (hg : toMatrix g = decodeRows gr)
    (hn : toMatrix n = decodeRows nr)
    (hl : packedMul rr gr = pr) (hp : packedMul gr nr = pr) :
    r = g * n * g⁻¹ := by
  have h : r * g = g * n := by
    apply toMatrix_injective
    rw [map_mul, map_mul, hr, hg, hn, ← decode_packedMul, ← decode_packedMul, hl, hp]
  calc
    r = (r * g) * g⁻¹ := by simp [mul_assoc]
    _ = g * n * g⁻¹ := by rw [h]

/-- All nonidentity local normal forms have one of the two proposed local
representatives, given the shared matrix evaluation certificates. -/
theorem threeLocalNormalForm_conjugacy_of_matrices
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hx : toMatrix (threeLocalProgram (a hA) (b hB)).1 = decodeRows programFstRows)
    (hy : toMatrix (threeLocalProgram (a hA) (b hB)).2 = decodeRows programSndRows)
    (hu : toMatrix (threeLocalU hA hB) = decodeRows uRows)
    (hz : toMatrix (threeLocalZ hA hB) = decodeRows zRows)
    (hn : ∀ t, toMatrix (threeLocalNormalForm hA hB t) = decodeRows (normalRows t)) :
    ∀ t : Fin 3 × Fin 3 × Fin 3, t ≠ (0,0,0) →
      ∃ (i : Fin 2) (g : Model),
        threeLocalRepresentative hA hB i = g * threeLocalNormalForm hA hB t * g⁻¹ := by
  let x := (threeLocalProgram (a hA) (b hB)).1
  let y := (threeLocalProgram (a hA) (b hB)).2
  rintro ⟨i,j,k⟩ ht
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact (ht rfl).elim
  · refine ⟨1, 1, ?_⟩
    simp [threeLocalRepresentative, threeLocalNormalForm]
  · refine ⟨1, (conj110101101011 x y), ?_⟩
    exact conjugate_of_products hz (conj110101101011_matrix x y hx hy) (hn (0,0,2))
      fusion002_left fusion002_right
  · refine ⟨0, (conj111011111011011 x y), ?_⟩
    exact conjugate_of_products hu (conj111011111011011_matrix x y hx hy) (hn (0,1,0))
      fusion010_left fusion010_right
  · refine ⟨0, (conj111010111010101 x y), ?_⟩
    exact conjugate_of_products hu (conj111010111010101_matrix x y hx hy) (hn (0,1,1))
      fusion011_left fusion011_right
  · refine ⟨0, (conj1110110111110110 x y), ?_⟩
    exact conjugate_of_products hu (conj1110110111110110_matrix x y hx hy) (hn (0,1,2))
      fusion012_left fusion012_right
  · refine ⟨0, (conj110101011101011 x y), ?_⟩
    exact conjugate_of_products hu (conj110101011101011_matrix x y hx hy) (hn (0,2,0))
      fusion020_left fusion020_right
  · refine ⟨0, (conj1110101110101010 x y), ?_⟩
    exact conjugate_of_products hu (conj1110101110101010_matrix x y hx hy) (hn (0,2,1))
      fusion021_left fusion021_right
  · refine ⟨0, (conj111011011111011 x y), ?_⟩
    exact conjugate_of_products hu (conj111011011111011_matrix x y hx hy) (hn (0,2,2))
      fusion022_left fusion022_right
  · refine ⟨0, 1, ?_⟩
    simp [threeLocalRepresentative, threeLocalNormalForm]
  · refine ⟨0, (conj011011101111 x y), ?_⟩
    exact conjugate_of_products hu (conj011011101111_matrix x y hx hy) (hn (1,0,1))
      fusion101_left fusion101_right
  · refine ⟨0, (conj110111011110 x y), ?_⟩
    exact conjugate_of_products hu (conj110111011110_matrix x y hx hy) (hn (1,0,2))
      fusion102_left fusion102_right
  · refine ⟨0, (conj11011010 x y), ?_⟩
    exact conjugate_of_products hu (conj11011010_matrix x y hx hy) (hn (1,1,0))
      fusion110_left fusion110_right
  · refine ⟨0, (conj1101111101 x y), ?_⟩
    exact conjugate_of_products hu (conj1101111101_matrix x y hx hy) (hn (1,1,1))
      fusion111_left fusion111_right
  · refine ⟨0, (conj01101101 x y), ?_⟩
    exact conjugate_of_products hu (conj01101101_matrix x y hx hy) (hn (1,1,2))
      fusion112_left fusion112_right
  · refine ⟨0, (conj1110101101010 x y), ?_⟩
    exact conjugate_of_products hu (conj1110101101010_matrix x y hx hy) (hn (1,2,0))
      fusion120_left fusion120_right
  · refine ⟨0, (conj0111010110101 x y), ?_⟩
    exact conjugate_of_products hu (conj0111010110101_matrix x y hx hy) (hn (1,2,1))
      fusion121_left fusion121_right
  · refine ⟨0, (conj110101101011 x y), ?_⟩
    exact conjugate_of_products hu (conj110101101011_matrix x y hx hy) (hn (1,2,2))
      fusion122_left fusion122_right
  · refine ⟨0, x, ?_⟩
    exact conjugate_of_products hu hx (hn (2,0,0))
      fusion200_left fusion200_right
  · refine ⟨0, (conj0110111011110 x y), ?_⟩
    exact conjugate_of_products hu (conj0110111011110_matrix x y hx hy) (hn (2,0,1))
      fusion201_left fusion201_right
  · refine ⟨0, (conj11011101111 x y), ?_⟩
    exact conjugate_of_products hu (conj11011101111_matrix x y hx hy) (hn (2,0,2))
      fusion202_left fusion202_right
  · refine ⟨0, (conj111010110101 x y), ?_⟩
    exact conjugate_of_products hu (conj111010110101_matrix x y hx hy) (hn (2,1,0))
      fusion210_left fusion210_right
  · refine ⟨0, (conj01110101101010 x y), ?_⟩
    exact conjugate_of_products hu (conj01110101101010_matrix x y hx hy) (hn (2,1,1))
      fusion211_left fusion211_right
  · refine ⟨0, (conj0110101101011 x y), ?_⟩
    exact conjugate_of_products hu (conj0110101101011_matrix x y hx hy) (hn (2,1,2))
      fusion212_left fusion212_right
  · refine ⟨0, (conj1101101 x y), ?_⟩
    exact conjugate_of_products hu (conj1101101_matrix x y hx hy) (hn (2,2,0))
      fusion220_left fusion220_right
  · refine ⟨0, (conj01101111101 x y), ?_⟩
    exact conjugate_of_products hu (conj01101111101_matrix x y hx hy) (hn (2,2,1))
      fusion221_left fusion221_right
  · refine ⟨0, (conj011011010 x y), ?_⟩
    exact conjugate_of_products hu (conj011011010_matrix x y hx hy) (hn (2,2,2))
      fusion222_left fusion222_right

end Janko4.Simplicity
