module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# No invariant binary bilinear form on the even hexacode module

The existing two even generators act on F₄³ by
`(x,y,z) ↦ (x+y+z,x,y)` and `(x,y,z) ↦ (z,ωx,ω²y)`.
On the six binary coordinate vectors, their invariance equations have full
rank on the 36 bilinear coefficients. The small elimination certificate below
uses explicit linear combinations, checked in characteristic two. Coordinate
reconstruction then proves that every invariant bilinear form is zero.

The final transport keeps the actual actor map and allows an arbitrary kernel;
its image need only contain the even cover. It is used on the literal moving
central quotient in the exceptional small-MS radius argument.

Source: Meierfrankenfeld--Stellmacher (1993), the self-dual constituent step
of (3.8), printed pp.878--879; Aschbacher--Smith K.1.3, printed p.453.
The code and concrete operators retain the ATLAS attribution of the imported
modules: Gerald Höhn and ATLAS contributors, ATLAS Research and Attribution
License 1.0 (`LICENSES/ATLAS.txt`). The elimination certificate is derived here
from those existing operators.
-/

@[expose] public noncomputable section
open Atlas.Codes
namespace Representation.Hexacode
open SixDimensional.EvenImage
private def q : Fin 6 → (Fin 3 → F) :=
  ![![1,0,0], ![omega,0,0], ![0,1,0], ![0,omega,0], ![0,0,1], ![0,0,omega]]
private def coeff (v : Fin 3 → F) : Fin 6 → Bit :=
  ![(v 0).re, (v 0).im, (v 1).re, (v 1).im, (v 2).re, (v 2).im]
private theorem reconstruct : ∀ v : Fin 3 → F, ∑ i, coeff v i • q i = v := by
  decide +kernel
private def opA (v : Fin 3 → F) : Fin 3 → F := ![v 0 + v 1 + v 2, v 0, v 1]
private def opB (v : Fin 3 → F) : Fin 3 → F := ![v 2, omega * v 0, omega ^ 2 * v 1]
private theorem opA_q : ∀ i, opA (q i) = ![q 0 + q 2, q 1 + q 3, q 0 + q 4, q 1 + q 5, q 0, q 1] i := by
  decide +kernel
private theorem opB_q : ∀ i, opB (q i) = ![q 3, q 2 + q 3, q 4 + q 5, q 4, q 0, q 1] i := by
  decide +kernel
set_option linter.unusedSimpArgs false in
private theorem coefficient_zero (m : Fin 6 → Fin 6 → Bit)
    (h0 : m 0 0 + m 0 2 + m 2 0 + m 2 2 = m 0 0)
    (h1 : m 0 1 + m 0 3 + m 2 1 + m 2 3 = m 0 1)
    (h2 : m 0 0 + m 0 4 + m 2 0 + m 2 4 = m 0 2)
    (h3 : m 0 1 + m 0 5 + m 2 1 + m 2 5 = m 0 3)
    (h4 : m 0 0 + m 2 0 = m 0 4)
    (h5 : m 0 1 + m 2 1 = m 0 5)
    (h6 : m 1 0 + m 1 2 + m 3 0 + m 3 2 = m 1 0)
    (h7 : m 1 1 + m 1 3 + m 3 1 + m 3 3 = m 1 1)
    (h8 : m 1 0 + m 1 4 + m 3 0 + m 3 4 = m 1 2)
    (h9 : m 1 1 + m 1 5 + m 3 1 + m 3 5 = m 1 3)
    (h10 : m 1 0 + m 3 0 = m 1 4)
    (h11 : m 1 1 + m 3 1 = m 1 5)
    (h12 : m 0 0 + m 0 2 + m 4 0 + m 4 2 = m 2 0)
    (h13 : m 0 1 + m 0 3 + m 4 1 + m 4 3 = m 2 1)
    (h14 : m 0 0 + m 0 4 + m 4 0 + m 4 4 = m 2 2)
    (h15 : m 0 1 + m 0 5 + m 4 1 + m 4 5 = m 2 3)
    (h16 : m 0 0 + m 4 0 = m 2 4)
    (h17 : m 0 1 + m 4 1 = m 2 5)
    (h18 : m 1 0 + m 1 2 + m 5 0 + m 5 2 = m 3 0)
    (h19 : m 1 1 + m 1 3 + m 5 1 + m 5 3 = m 3 1)
    (h20 : m 1 0 + m 1 4 + m 5 0 + m 5 4 = m 3 2)
    (h21 : m 1 1 + m 1 5 + m 5 1 + m 5 5 = m 3 3)
    (h22 : m 1 0 + m 5 0 = m 3 4)
    (h23 : m 1 1 + m 5 1 = m 3 5)
    (h36 : m 3 3 = m 0 0)
    (h37 : m 3 2 + m 3 3 = m 0 1)
    (h38 : m 3 4 + m 3 5 = m 0 2)
    (h39 : m 3 4 = m 0 3)
    (h40 : m 3 0 = m 0 4)
    (h41 : m 3 1 = m 0 5)
    (h42 : m 2 3 + m 3 3 = m 1 0)
    (h43 : m 2 2 + m 2 3 + m 3 2 + m 3 3 = m 1 1)
    (h46 : m 2 0 + m 3 0 = m 1 4)
    (h47 : m 2 1 + m 3 1 = m 1 5)
    (h52 : m 4 0 + m 5 0 = m 2 4)
    (h53 : m 4 1 + m 5 1 = m 2 5)
    : ∀ i j, m i j = 0 := by
  have htwo : (2 : Bit) = 0 := by decide
  have hfour : (4 : Bit) = 0 := by decide
  intro i j
  fin_cases i <;> fin_cases j
  · change m 0 0 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h5 + h7 + h9 + h17 + h23 + h36 + h41 + h47 + h53
  · change m 0 1 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h4 + h5 + h6 + h7 + h8 + h9 + h16 + h17 + h22 + h23 + h37 + h40 + h41 + h46 + h47 + h52 + h53
  · change m 0 2 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h1 + h4 + h6 + h8 + h10 + h11 + h36 + h39 + h40 + h43 + h47
  · change m 0 3 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h5 + h7 + h9 + h10 + h37 + h38 + h39 + h41 + h42 + h43 + h46 + h47
  · change m 0 4 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h4 + h5 + h7 + h9 + h16 + h22 + h37 + h38 + h41 + h42 + h43 + h47 + h52
  · change m 0 5 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h4 + h6 + h7 + h8 + h9 + h17 + h23 + h36 + h37 + h39 + h40 + h41 + h42 + h46 + h47 + h53
  · change m 1 0 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h10 + h16 + h17 + h22 + h23 + h36 + h37 + h38 + h42 + h43 + h46 + h52 + h53
  · change m 1 1 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h11 + h16 + h22 + h36 + h39 + h42 + h47 + h52
  · change m 1 2 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h5 + h7 + h8 + h9 + h37 + h38 + h41 + h42 + h43 + h46 + h47
  · change m 1 3 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h4 + h5 + h6 + h7 + h8 + h36 + h37 + h39 + h40 + h41 + h42 + h46
  · change m 1 4 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h4 + h5 + h7 + h9 + h17 + h23 + h36 + h40 + h41 + h46 + h47 + h53
  · change m 1 5 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h4 + h6 + h7 + h8 + h9 + h16 + h17 + h22 + h23 + h37 + h40 + h46 + h52 + h53
  · change m 2 0 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h16 + h17 + h22 + h23 + h36 + h37 + h38 + h42 + h43 + h52 + h53
  · change m 2 1 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h16 + h22 + h36 + h39 + h42 + h52
  · change m 2 2 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h1 + h4 + h6 + h8 + h10 + h11 + h16 + h17 + h22 + h23 + h37 + h38 + h39 + h40 + h42 + h47 + h52 + h53
  · change m 2 3 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h5 + h7 + h9 + h10 + h16 + h22 + h36 + h37 + h38 + h41 + h43 + h46 + h47 + h52
  · change m 2 4 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h1 + h2 + h6 + h8 + h10 + h11 + h36 + h39 + h40 + h43 + h47
  · change m 2 5 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h3 + h7 + h9 + h10 + h37 + h38 + h39 + h41 + h42 + h43 + h46 + h47
  · change m 3 0 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h4 + h5 + h7 + h9 + h16 + h22 + h37 + h38 + h40 + h41 + h42 + h43 + h47 + h52
  · change m 3 1 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h4 + h6 + h7 + h8 + h9 + h17 + h23 + h36 + h37 + h39 + h40 + h42 + h46 + h47 + h53
  · change m 3 2 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h4 + h6 + h8 + h16 + h22 + h40 + h46 + h52
  · change m 3 3 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h5 + h7 + h9 + h17 + h23 + h41 + h47 + h53
  · change m 3 4 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h5 + h7 + h9 + h10 + h37 + h38 + h41 + h42 + h43 + h46 + h47
  · change m 3 5 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h4 + h5 + h6 + h7 + h8 + h9 + h11 + h36 + h37 + h39 + h40 + h41 + h42 + h46
  · change m 4 0 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h1 + h2 + h5 + h6 + h7 + h8 + h9 + h10 + h11 + h16 + h17 + h23 + h39 + h40 + h41 + h43 + h53
  · change m 4 1 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h3 + h4 + h5 + h6 + h8 + h10 + h16 + h22 + h23 + h38 + h39 + h40 + h42 + h43 + h52 + h53
  · change m 4 2 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h2 + h4 + h12 + h17 + h22 + h23 + h36 + h37 + h38 + h42 + h43 + h52 + h53
  · change m 4 3 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h3 + h5 + h13 + h16 + h17 + h22 + h36 + h39 + h42 + h52
  · change m 4 4 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h2 + h5 + h7 + h9 + h14 + h16 + h17 + h23 + h36 + h41 + h47 + h53
  · change m 4 5 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h15 + h16 + h22 + h23 + h37 + h40 + h41 + h46 + h47 + h52 + h53
  · change m 5 0 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h5 + h7 + h9 + h16 + h17 + h23 + h36 + h41 + h47 + h52 + h53
  · change m 5 1 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h4 + h5 + h6 + h7 + h8 + h9 + h16 + h22 + h23 + h37 + h40 + h41 + h46 + h47 + h52
  · change m 5 2 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h4 + h5 + h7 + h8 + h9 + h10 + h16 + h18 + h37 + h38 + h40 + h41 + h42 + h43 + h47 + h52
  · change m 5 3 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h4 + h6 + h7 + h8 + h11 + h17 + h19 + h36 + h37 + h39 + h40 + h42 + h46 + h47 + h53
  · change m 5 4 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h0 + h6 + h8 + h10 + h16 + h17 + h20 + h23 + h36 + h37 + h38 + h42 + h43 + h46 + h52 + h53
  · change m 5 5 = 0
    linear_combination (norm := (ring_nf; simp only [htwo, hfour, mul_zero, add_zero, zero_add, sub_zero, neg_zero])) h1 + h7 + h9 + h11 + h16 + h21 + h22 + h23 + h36 + h39 + h42 + h47 + h52
set_option linter.unusedSimpArgs false in
private theorem coordinate_form_zero
    (B : LinearMap.BilinForm Bit (Fin 3 → F))
    (hA : ∀ v w, B (opA v) (opA w) = B v w)
    (hB : ∀ v w, B (opB v) (opB w) = B v w) : B = 0 := by
  have h0 := hA (q 0) (q 0)
  simp only [opA_q] at h0
  change B (q 0 + q 2) (q 0 + q 2) = B (q 0) (q 0) at h0
  simp only [map_add, LinearMap.add_apply] at h0
  have h1 := hA (q 0) (q 1)
  simp only [opA_q] at h1
  change B (q 0 + q 2) (q 1 + q 3) = B (q 0) (q 1) at h1
  simp only [map_add, LinearMap.add_apply] at h1
  have h2 := hA (q 0) (q 2)
  simp only [opA_q] at h2
  change B (q 0 + q 2) (q 0 + q 4) = B (q 0) (q 2) at h2
  simp only [map_add, LinearMap.add_apply] at h2
  have h3 := hA (q 0) (q 3)
  simp only [opA_q] at h3
  change B (q 0 + q 2) (q 1 + q 5) = B (q 0) (q 3) at h3
  simp only [map_add, LinearMap.add_apply] at h3
  have h4 := hA (q 0) (q 4)
  simp only [opA_q] at h4
  change B (q 0 + q 2) (q 0) = B (q 0) (q 4) at h4
  simp only [map_add, LinearMap.add_apply] at h4
  have h5 := hA (q 0) (q 5)
  simp only [opA_q] at h5
  change B (q 0 + q 2) (q 1) = B (q 0) (q 5) at h5
  simp only [map_add, LinearMap.add_apply] at h5
  have h6 := hA (q 1) (q 0)
  simp only [opA_q] at h6
  change B (q 1 + q 3) (q 0 + q 2) = B (q 1) (q 0) at h6
  simp only [map_add, LinearMap.add_apply] at h6
  have h7 := hA (q 1) (q 1)
  simp only [opA_q] at h7
  change B (q 1 + q 3) (q 1 + q 3) = B (q 1) (q 1) at h7
  simp only [map_add, LinearMap.add_apply] at h7
  have h8 := hA (q 1) (q 2)
  simp only [opA_q] at h8
  change B (q 1 + q 3) (q 0 + q 4) = B (q 1) (q 2) at h8
  simp only [map_add, LinearMap.add_apply] at h8
  have h9 := hA (q 1) (q 3)
  simp only [opA_q] at h9
  change B (q 1 + q 3) (q 1 + q 5) = B (q 1) (q 3) at h9
  simp only [map_add, LinearMap.add_apply] at h9
  have h10 := hA (q 1) (q 4)
  simp only [opA_q] at h10
  change B (q 1 + q 3) (q 0) = B (q 1) (q 4) at h10
  simp only [map_add, LinearMap.add_apply] at h10
  have h11 := hA (q 1) (q 5)
  simp only [opA_q] at h11
  change B (q 1 + q 3) (q 1) = B (q 1) (q 5) at h11
  simp only [map_add, LinearMap.add_apply] at h11
  have h12 := hA (q 2) (q 0)
  simp only [opA_q] at h12
  change B (q 0 + q 4) (q 0 + q 2) = B (q 2) (q 0) at h12
  simp only [map_add, LinearMap.add_apply] at h12
  have h13 := hA (q 2) (q 1)
  simp only [opA_q] at h13
  change B (q 0 + q 4) (q 1 + q 3) = B (q 2) (q 1) at h13
  simp only [map_add, LinearMap.add_apply] at h13
  have h14 := hA (q 2) (q 2)
  simp only [opA_q] at h14
  change B (q 0 + q 4) (q 0 + q 4) = B (q 2) (q 2) at h14
  simp only [map_add, LinearMap.add_apply] at h14
  have h15 := hA (q 2) (q 3)
  simp only [opA_q] at h15
  change B (q 0 + q 4) (q 1 + q 5) = B (q 2) (q 3) at h15
  simp only [map_add, LinearMap.add_apply] at h15
  have h16 := hA (q 2) (q 4)
  simp only [opA_q] at h16
  change B (q 0 + q 4) (q 0) = B (q 2) (q 4) at h16
  simp only [map_add, LinearMap.add_apply] at h16
  have h17 := hA (q 2) (q 5)
  simp only [opA_q] at h17
  change B (q 0 + q 4) (q 1) = B (q 2) (q 5) at h17
  simp only [map_add, LinearMap.add_apply] at h17
  have h18 := hA (q 3) (q 0)
  simp only [opA_q] at h18
  change B (q 1 + q 5) (q 0 + q 2) = B (q 3) (q 0) at h18
  simp only [map_add, LinearMap.add_apply] at h18
  have h19 := hA (q 3) (q 1)
  simp only [opA_q] at h19
  change B (q 1 + q 5) (q 1 + q 3) = B (q 3) (q 1) at h19
  simp only [map_add, LinearMap.add_apply] at h19
  have h20 := hA (q 3) (q 2)
  simp only [opA_q] at h20
  change B (q 1 + q 5) (q 0 + q 4) = B (q 3) (q 2) at h20
  simp only [map_add, LinearMap.add_apply] at h20
  have h21 := hA (q 3) (q 3)
  simp only [opA_q] at h21
  change B (q 1 + q 5) (q 1 + q 5) = B (q 3) (q 3) at h21
  simp only [map_add, LinearMap.add_apply] at h21
  have h22 := hA (q 3) (q 4)
  simp only [opA_q] at h22
  change B (q 1 + q 5) (q 0) = B (q 3) (q 4) at h22
  simp only [map_add, LinearMap.add_apply] at h22
  have h23 := hA (q 3) (q 5)
  simp only [opA_q] at h23
  change B (q 1 + q 5) (q 1) = B (q 3) (q 5) at h23
  simp only [map_add, LinearMap.add_apply] at h23
  have h36 := hB (q 0) (q 0)
  simp only [opB_q] at h36
  change B (q 3) (q 3) = B (q 0) (q 0) at h36
  have h37 := hB (q 0) (q 1)
  simp only [opB_q] at h37
  change B (q 3) (q 2 + q 3) = B (q 0) (q 1) at h37
  simp only [map_add, LinearMap.add_apply] at h37
  have h38 := hB (q 0) (q 2)
  simp only [opB_q] at h38
  change B (q 3) (q 4 + q 5) = B (q 0) (q 2) at h38
  simp only [map_add, LinearMap.add_apply] at h38
  have h39 := hB (q 0) (q 3)
  simp only [opB_q] at h39
  change B (q 3) (q 4) = B (q 0) (q 3) at h39
  have h40 := hB (q 0) (q 4)
  simp only [opB_q] at h40
  change B (q 3) (q 0) = B (q 0) (q 4) at h40
  have h41 := hB (q 0) (q 5)
  simp only [opB_q] at h41
  change B (q 3) (q 1) = B (q 0) (q 5) at h41
  have h42 := hB (q 1) (q 0)
  simp only [opB_q] at h42
  change B (q 2 + q 3) (q 3) = B (q 1) (q 0) at h42
  simp only [map_add, LinearMap.add_apply] at h42
  have h43 := hB (q 1) (q 1)
  simp only [opB_q] at h43
  change B (q 2 + q 3) (q 2 + q 3) = B (q 1) (q 1) at h43
  simp only [map_add, LinearMap.add_apply] at h43
  have h46 := hB (q 1) (q 4)
  simp only [opB_q] at h46
  change B (q 2 + q 3) (q 0) = B (q 1) (q 4) at h46
  simp only [map_add, LinearMap.add_apply] at h46
  have h47 := hB (q 1) (q 5)
  simp only [opB_q] at h47
  change B (q 2 + q 3) (q 1) = B (q 1) (q 5) at h47
  simp only [map_add, LinearMap.add_apply] at h47
  have h52 := hB (q 2) (q 4)
  simp only [opB_q] at h52
  change B (q 4 + q 5) (q 0) = B (q 2) (q 4) at h52
  simp only [map_add, LinearMap.add_apply] at h52
  have h53 := hB (q 2) (q 5)
  simp only [opB_q] at h53
  change B (q 4 + q 5) (q 1) = B (q 2) (q 5) at h53
  simp only [map_add, LinearMap.add_apply] at h53
  have hz : ∀ i j, B (q i) (q j) = 0 := by
    apply coefficient_zero (fun i j => B (q i) (q j))
    · convert h0 using 1
      abel
    · convert h1 using 1
      abel
    · convert h2 using 1
      abel
    · convert h3 using 1
      abel
    · exact h4
    · exact h5
    · convert h6 using 1
      abel
    · convert h7 using 1
      abel
    · convert h8 using 1
      abel
    · convert h9 using 1
      abel
    · exact h10
    · exact h11
    · convert h12 using 1
      abel
    · convert h13 using 1
      abel
    · convert h14 using 1
      abel
    · convert h15 using 1
      abel
    · exact h16
    · exact h17
    · convert h18 using 1
      abel
    · convert h19 using 1
      abel
    · convert h20 using 1
      abel
    · convert h21 using 1
      abel
    · exact h22
    · exact h23
    · exact h36
    · exact h37
    · exact h38
    · exact h39
    · exact h40
    · exact h41
    · exact h42
    · convert h43 using 1
      abel
    · exact h46
    · exact h47
    · exact h52
    · exact h53
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change B v w = 0
  rw [← reconstruct v, ← reconstruct w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hz, smul_zero,
    Finset.sum_const_zero, LinearMap.zero_apply]

/-- The even hexacode action admits no invariant binary bilinear form. -/
theorem even_invariant_bilinear_eq_zero
    (B : LinearMap.BilinForm Bit hexacode)
    (hB : ∀ g : HexEvenAutomorphisms, ∀ v w,
      B (evenAction g v) (evenAction g w) = B v w) : B = 0 := by
  let C := B.compl₁₂ binaryCoordinates.symm.toLinearMap binaryCoordinates.symm.toLinearMap
  have hA (v : hexacode) : binaryCoordinates (evenAction generatorA v) =
      opA (binaryCoordinates v) := generatorA_coordinates v
  have hD (v : hexacode) : binaryCoordinates (evenAction generatorB v) =
      opB (binaryCoordinates v) := generatorB_coordinates v
  have hCA (v w) : C (opA v) (opA w) = C v w := by
    obtain ⟨v,rfl⟩ := binaryCoordinates.surjective v
    obtain ⟨w,rfl⟩ := binaryCoordinates.surjective w
    change B (binaryCoordinates.symm (opA (binaryCoordinates v)))
      (binaryCoordinates.symm (opA (binaryCoordinates w))) =
      B (binaryCoordinates.symm (binaryCoordinates v)) (binaryCoordinates.symm (binaryCoordinates w))
    rw [←hA,←hA,binaryCoordinates.symm_apply_apply,binaryCoordinates.symm_apply_apply,
      binaryCoordinates.symm_apply_apply,binaryCoordinates.symm_apply_apply]
    exact hB generatorA v w
  have hCB (v w) : C (opB v) (opB w) = C v w := by
    obtain ⟨v,rfl⟩ := binaryCoordinates.surjective v
    obtain ⟨w,rfl⟩ := binaryCoordinates.surjective w
    change B (binaryCoordinates.symm (opB (binaryCoordinates v)))
      (binaryCoordinates.symm (opB (binaryCoordinates w))) =
      B (binaryCoordinates.symm (binaryCoordinates v)) (binaryCoordinates.symm (binaryCoordinates w))
    rw [←hD,←hD,binaryCoordinates.symm_apply_apply,binaryCoordinates.symm_apply_apply,
      binaryCoordinates.symm_apply_apply,binaryCoordinates.symm_apply_apply]
    exact hB generatorB v w
  have hz := coordinate_form_zero C hCA hCB
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change B v w = 0
  have hh := LinearMap.congr_fun (LinearMap.congr_fun hz (binaryCoordinates v)) (binaryCoordinates w)
  change B (binaryCoordinates.symm (binaryCoordinates v))
    (binaryCoordinates.symm (binaryCoordinates w)) = 0 at hh
  simpa only [binaryCoordinates.symm_apply_apply] using hh

/-- The obstruction transports through a specified actor map whose image
contains the even cover; the action kernel need not split. -/
theorem invariant_bilinear_eq_zero_of_hexacode_marking
    {H W : Type*} [Group H] [AddCommGroup W] [Module Bit W]
    (ρ : Representation Bit H W) (π : H →* HexAutomorphisms)
    (hπ : hexSign.ker ≤ π.range) (E : W ≃ₗ[Bit] hexacode)
    (hE : ∀ g v, E (ρ g v) = action (π g) (E v))
    (B : LinearMap.BilinForm Bit W)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) : B = 0 := by
  let C := B.compl₁₂ E.symm.toLinearMap E.symm.toLinearMap
  have hC : C = 0 := even_invariant_bilinear_eq_zero C (by
    intro g v w
    obtain ⟨a,ha⟩ := hπ g.property
    have he (v : hexacode) : E.symm (evenAction g v) = ρ a (E.symm v) := by
      apply E.injective
      rw [E.apply_symm_apply,hE,ha,E.apply_symm_apply]
      rfl
    change B (E.symm (evenAction g v)) (E.symm (evenAction g w)) = B (E.symm v) (E.symm w)
    rw [he,he]
    exact hB a _ _)
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change B v w = 0
  have hh := LinearMap.congr_fun (LinearMap.congr_fun hC (E v)) (E w)
  change B (E.symm (E v)) (E.symm (E w)) = 0 at hh
  simpa only [E.symm_apply_apply] using hh
end Representation.Hexacode
