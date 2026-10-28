module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Two explicit generators of SL₅(2)

The column masks below are the natural LEFT actions extracted from the native
J₄ octad-pullback construction ([ATLAS J4G1-max3W1](https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max3W1),
after its specified marking).
Bit i of column j is matrix entry (i,j). The proof checks short matrix words
for an elementary transvection and the cyclic permutation of the five axes.
Conjugation and three-index commutators give every elementary transvection;
Mathlib's diagonal/transvection induction then gives the whole group.

All witness products are checked by the Lean kernel. The bounded search used
to discover the two words and the ATLAS group-order calculation are not inputs
to the proof. This module makes no claim about their realization in J₄.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open SL5TenDimensional

/-- Interpret column masks, with bit i in row i. -/
def columnMatrix (c : Fin 5 → ℕ) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if (c j).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
theorem determinant_A0 : (columnMatrix ![10,23,4,22,27]).det = 1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem determinant_A1 : (columnMatrix ![9,22,11,8,12]).det = 1 := by decide +kernel

/-- First natural matrix for left conjugation. -/
def A0 : Group := ⟨columnMatrix ![10,23,4,22,27], determinant_A0⟩
/-- Second natural matrix for left conjugation (inverse of the right-action matrix). -/
def A1 : Group := ⟨columnMatrix ![9,22,11,8,12], determinant_A1⟩

private def Realized (H : Subgroup Group) (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  ∃ g ∈ H, g.val = M

private theorem realized_mul {H : Subgroup Group}
    {M N P : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (hM : Realized H M) (hN : Realized H N) (h : M * N = P) : Realized H P := by
  obtain ⟨g,hg,rfl⟩ := hM
  obtain ⟨k,hk,rfl⟩ := hN
  exact ⟨g*k,H.mul_mem hg hk,h⟩

set_option maxRecDepth 10000 in
private theorem roots_realized (H : Subgroup Group) (hA : A0 ∈ H) (hB : A1 ∈ H)
    (i j : Fin 5) (hij : i ≠ j) : Realized H (Matrix.transvection i j 1) := by
  have m0 : Realized H (columnMatrix ![1,2,4,8,16]) :=
    ⟨1,H.one_mem,by decide +kernel⟩
  have m1 : Realized H (columnMatrix ![10,23,4,22,27]) := ⟨A0,hA,rfl⟩
  have m2 : Realized H (columnMatrix ![9,22,11,8,12]) := ⟨A1,hB,rfl⟩
  -- m4 is A1 cubed, the inverse letter used in the two short words.
  have m3 : Realized H (columnMatrix ![1,17,23,8,3]) :=
    realized_mul m2 m2 (by decide +kernel)
  have m4 : Realized H (columnMatrix ![9,5,24,8,31]) :=
    realized_mul m3 m2 (by decide +kernel)
  have m5 : Realized H (columnMatrix ![28,8,11,22,18]) :=
    realized_mul m1 m2 (by decide +kernel)
  have m6 : Realized H (columnMatrix ![30,13,11,17,16]) :=
    realized_mul m5 m1 (by decide +kernel)
  have m7 : Realized H (columnMatrix ![15,22,2,17,26]) :=
    realized_mul m6 m2 (by decide +kernel)
  have m8 : Realized H (columnMatrix ![7,1,2,14,18]) :=
    realized_mul m7 m1 (by decide +kernel)
  have m9 : Realized H (columnMatrix ![9,17,8,14,12]) :=
    realized_mul m8 m2 (by decide +kernel)
  have m10 : Realized H (columnMatrix ![31,28,8,21,26]) :=
    realized_mul m9 m1 (by decide +kernel)
  have m11 : Realized H (columnMatrix ![10,14,22,21,29]) :=
    realized_mul m10 m2 (by decide +kernel)
  have m12 : Realized H (columnMatrix ![31,5,17,21,3]) :=
    realized_mul m11 m2 (by decide +kernel)
  have m13 : Realized H (columnMatrix ![16,8,17,23,12]) :=
    realized_mul m12 m1 (by decide +kernel)
  have m14 : Realized H (columnMatrix ![7,1,27,23,18]) :=
    realized_mul m13 m4 (by decide +kernel)
  have m15 : Realized H (columnMatrix ![22,15,27,8,3]) :=
    realized_mul m14 m1 (by decide +kernel)
  have m16 : Realized H (columnMatrix ![30,23,17,8,19]) :=
    realized_mul m15 m2 (by decide +kernel)
  have m17 : Realized H (columnMatrix ![31,11,17,21,18]) :=
    realized_mul m16 m1 (by decide +kernel)
  have m18 : Realized H (columnMatrix ![10,14,7,21,2]) :=
    realized_mul m17 m4 (by decide +kernel)
  have m19 : Realized H (columnMatrix ![27,1,7,11,19]) :=
    realized_mul m18 m1 (by decide +kernel)
  have m20 : Realized H (columnMatrix ![16,21,17,11,12]) :=
    realized_mul m19 m2 (by decide +kernel)
  have m21 : Realized H (columnMatrix ![30,24,17,8,2]) :=
    realized_mul m20 m1 (by decide +kernel)
  have m22 : Realized H (columnMatrix ![22,15,10,8,29]) :=
    realized_mul m21 m4 (by decide +kernel)
  have m23 : Realized H (columnMatrix ![30,28,21,8,6]) :=
    realized_mul m22 m4 (by decide +kernel)
  have m24 : Realized H (columnMatrix ![20,17,21,15,12]) :=
    realized_mul m23 m1 (by decide +kernel)
  have m25 : Realized H (columnMatrix ![27,1,3,15,19]) :=
    realized_mul m24 m4 (by decide +kernel)
  have m26 : Realized H (columnMatrix ![14,10,3,17,6]) :=
    realized_mul m25 m1 (by decide +kernel)
  have m27 : Realized H (columnMatrix ![31,13,23,17,16]) :=
    realized_mul m26 m4 (by decide +kernel)
  have m28 : Realized H (columnMatrix ![28,21,23,10,19]) :=
    realized_mul m27 m1 (by decide +kernel)
  have m29 : Realized H (columnMatrix ![22,11,25,10,7]) :=
    realized_mul m28 m4 (by decide +kernel)
  have m30 : Realized H (columnMatrix ![1,3,25,21,16]) :=
    realized_mul m29 m1 (by decide +kernel)
  have m31 : Realized H (columnMatrix ![20,10,23,21,12]) :=
    realized_mul m30 m2 (by decide +kernel)
  have m32 : Realized H (columnMatrix ![31,5,23,17,7]) :=
    realized_mul m31 m1 (by decide +kernel)
  have m33 : Realized H (columnMatrix ![14,8,22,17,27]) :=
    realized_mul m32 m4 (by decide +kernel)
  have m34 : Realized H (columnMatrix ![31,24,10,17,26]) :=
    realized_mul m33 m4 (by decide +kernel)
  have m35 : Realized H (columnMatrix ![9,23,10,8,12]) :=
    realized_mul m34 m1 (by decide +kernel)
  -- The 33-letter word gives the elementary transvection E₀₁.
  have m36 : Realized H (columnMatrix ![1,3,4,8,16]) :=
    realized_mul m35 m4 (by decide +kernel)
  have m37 : Realized H (columnMatrix ![10,17,2,22,29]) :=
    realized_mul m5 m2 (by decide +kernel)
  have m38 : Realized H (columnMatrix ![7,4,2,14,16]) :=
    realized_mul m37 m1 (by decide +kernel)
  have m39 : Realized H (columnMatrix ![9,5,30,14,31]) :=
    realized_mul m38 m4 (by decide +kernel)
  have m40 : Realized H (columnMatrix ![11,13,30,4,29]) :=
    realized_mul m39 m1 (by decide +kernel)
  have m41 : Realized H (columnMatrix ![15,14,2,4,26]) :=
    realized_mul m40 m2 (by decide +kernel)
  have m42 : Realized H (columnMatrix ![10,25,2,22,31]) :=
    realized_mul m41 m1 (by decide +kernel)
  have m43 : Realized H (columnMatrix ![28,8,9,22,24]) :=
    realized_mul m42 m4 (by decide +kernel)
  have m44 : Realized H (columnMatrix ![30,5,9,25,26]) :=
    realized_mul m43 m1 (by decide +kernel)
  have m45 : Realized H (columnMatrix ![7,22,2,25,16]) :=
    realized_mul m44 m2 (by decide +kernel)
  have m46 : Realized H (columnMatrix ![15,3,2,4,24]) :=
    realized_mul m45 m1 (by decide +kernel)
  have m47 : Realized H (columnMatrix ![11,25,8,4,6]) :=
    realized_mul m46 m2 (by decide +kernel)
  have m48 : Realized H (columnMatrix ![15,23,22,4,12]) :=
    realized_mul m47 m2 (by decide +kernel)
  have m49 : Realized H (columnMatrix ![19,2,22,13,16]) :=
    realized_mul m48 m1 (by decide +kernel)
  have m50 : Realized H (columnMatrix ![30,5,29,13,26]) :=
    realized_mul m49 m4 (by decide +kernel)
  have m51 : Realized H (columnMatrix ![8,28,29,2,12]) :=
    realized_mul m50 m1 (by decide +kernel)
  have m52 : Realized H (columnMatrix ![10,21,14,2,7]) :=
    realized_mul m51 m4 (by decide +kernel)
  have m53 : Realized H (columnMatrix ![23,22,14,28,26]) :=
    realized_mul m52 m1 (by decide +kernel)
  have m54 : Realized H (columnMatrix ![11,2,29,28,18]) :=
    realized_mul m53 m2 (by decide +kernel)
  have m55 : Realized H (columnMatrix ![30,6,29,13,7]) :=
    realized_mul m54 m1 (by decide +kernel)
  have m56 : Realized H (columnMatrix ![19,28,21,13,16]) :=
    realized_mul m55 m2 (by decide +kernel)
  have m57 : Realized H (columnMatrix ![17,10,21,25,18]) :=
    realized_mul m56 m1 (by decide +kernel)
  have m58 : Realized H (columnMatrix ![8,13,2,25,12]) :=
    realized_mul m57 m2 (by decide +kernel)
  have m59 : Realized H (columnMatrix ![20,11,2,3,16]) :=
    realized_mul m58 m1 (by decide +kernel)
  have m60 : Realized H (columnMatrix ![23,25,28,3,1]) :=
    realized_mul m59 m2 (by decide +kernel)
  have m61 : Realized H (columnMatrix ![26,19,28,4,12]) :=
    realized_mul m60 m1 (by decide +kernel)
  have m62 : Realized H (columnMatrix ![30,6,8,4,29]) :=
    realized_mul m61 m4 (by decide +kernel)
  have m63 : Realized H (columnMatrix ![2,13,8,19,1]) :=
    realized_mul m62 m1 (by decide +kernel)
  have m64 : Realized H (columnMatrix ![17,10,18,19,21]) :=
    realized_mul m63 m4 (by decide +kernel)
  have m65 : Realized H (columnMatrix ![25,28,18,13,29]) :=
    realized_mul m64 m1 (by decide +kernel)
  have m66 : Realized H (columnMatrix ![20,19,8,13,31]) :=
    realized_mul m65 m2 (by decide +kernel)
  have m67 : Realized H (columnMatrix ![30,16,8,4,21]) :=
    realized_mul m66 m1 (by decide +kernel)
  have m68 : Realized H (columnMatrix ![26,22,17,4,23]) :=
    realized_mul m67 m4 (by decide +kernel)
  have m69 : Realized H (columnMatrix ![18,10,17,16,31]) :=
    realized_mul m68 m1 (by decide +kernel)
  -- The 36-letter word gives the cycle eᵢ ↦ eᵢ₊₁ (indices modulo five).
  have m70 : Realized H (columnMatrix ![2,4,8,16,1]) :=
    realized_mul m69 m2 (by decide +kernel)
  have m71 : Realized H (columnMatrix ![4,8,16,1,2]) :=
    realized_mul m70 m70 (by decide +kernel)
  have m72 : Realized H (columnMatrix ![16,1,2,4,8]) :=
    realized_mul m71 m71 (by decide +kernel)
  -- Conjugate E₀₁ around the cycle, then take three-index commutators.
  have m73 : Realized H (columnMatrix ![2,6,8,16,1]) :=
    realized_mul m70 m36 (by decide +kernel)
  have m74 : Realized H (columnMatrix ![1,2,6,8,16]) :=
    realized_mul m73 m72 (by decide +kernel)
  have m75 : Realized H (columnMatrix ![2,4,12,16,1]) :=
    realized_mul m70 m74 (by decide +kernel)
  have m76 : Realized H (columnMatrix ![1,2,4,12,16]) :=
    realized_mul m75 m72 (by decide +kernel)
  have m77 : Realized H (columnMatrix ![2,4,8,24,1]) :=
    realized_mul m70 m76 (by decide +kernel)
  have m78 : Realized H (columnMatrix ![1,2,4,8,24]) :=
    realized_mul m77 m72 (by decide +kernel)
  have m79 : Realized H (columnMatrix ![2,4,8,16,17]) :=
    realized_mul m70 m78 (by decide +kernel)
  have m80 : Realized H (columnMatrix ![17,2,4,8,16]) :=
    realized_mul m79 m72 (by decide +kernel)
  have m81 : Realized H (columnMatrix ![1,3,7,8,16]) :=
    realized_mul m36 m74 (by decide +kernel)
  have m82 : Realized H (columnMatrix ![1,2,7,8,16]) :=
    realized_mul m81 m36 (by decide +kernel)
  have m83 : Realized H (columnMatrix ![1,2,5,8,16]) :=
    realized_mul m82 m74 (by decide +kernel)
  have m84 : Realized H (columnMatrix ![1,2,6,14,16]) :=
    realized_mul m74 m76 (by decide +kernel)
  have m85 : Realized H (columnMatrix ![1,2,4,14,16]) :=
    realized_mul m84 m74 (by decide +kernel)
  have m86 : Realized H (columnMatrix ![1,2,4,10,16]) :=
    realized_mul m85 m76 (by decide +kernel)
  have m87 : Realized H (columnMatrix ![1,2,4,12,28]) :=
    realized_mul m76 m78 (by decide +kernel)
  have m88 : Realized H (columnMatrix ![1,2,4,8,28]) :=
    realized_mul m87 m76 (by decide +kernel)
  have m89 : Realized H (columnMatrix ![1,2,4,8,20]) :=
    realized_mul m88 m78 (by decide +kernel)
  have m90 : Realized H (columnMatrix ![25,2,4,8,24]) :=
    realized_mul m78 m80 (by decide +kernel)
  have m91 : Realized H (columnMatrix ![25,2,4,8,16]) :=
    realized_mul m90 m78 (by decide +kernel)
  have m92 : Realized H (columnMatrix ![9,2,4,8,16]) :=
    realized_mul m91 m80 (by decide +kernel)
  have m93 : Realized H (columnMatrix ![17,19,4,8,16]) :=
    realized_mul m80 m36 (by decide +kernel)
  have m94 : Realized H (columnMatrix ![1,19,4,8,16]) :=
    realized_mul m93 m80 (by decide +kernel)
  have m95 : Realized H (columnMatrix ![1,18,4,8,16]) :=
    realized_mul m94 m36 (by decide +kernel)
  have m96 : Realized H (columnMatrix ![1,2,5,13,16]) :=
    realized_mul m83 m76 (by decide +kernel)
  have m97 : Realized H (columnMatrix ![1,2,4,13,16]) :=
    realized_mul m96 m83 (by decide +kernel)
  have m98 : Realized H (columnMatrix ![1,2,4,9,16]) :=
    realized_mul m97 m76 (by decide +kernel)
  have m99 : Realized H (columnMatrix ![1,2,4,10,26]) :=
    realized_mul m86 m78 (by decide +kernel)
  have m100 : Realized H (columnMatrix ![1,2,4,8,26]) :=
    realized_mul m99 m86 (by decide +kernel)
  have m101 : Realized H (columnMatrix ![1,2,4,8,18]) :=
    realized_mul m100 m78 (by decide +kernel)
  have m102 : Realized H (columnMatrix ![21,2,4,8,20]) :=
    realized_mul m89 m80 (by decide +kernel)
  have m103 : Realized H (columnMatrix ![21,2,4,8,16]) :=
    realized_mul m102 m89 (by decide +kernel)
  have m104 : Realized H (columnMatrix ![5,2,4,8,16]) :=
    realized_mul m103 m80 (by decide +kernel)
  have m105 : Realized H (columnMatrix ![9,11,4,8,16]) :=
    realized_mul m92 m36 (by decide +kernel)
  have m106 : Realized H (columnMatrix ![1,11,4,8,16]) :=
    realized_mul m105 m92 (by decide +kernel)
  have m107 : Realized H (columnMatrix ![1,10,4,8,16]) :=
    realized_mul m106 m36 (by decide +kernel)
  have m108 : Realized H (columnMatrix ![1,18,22,8,16]) :=
    realized_mul m95 m74 (by decide +kernel)
  have m109 : Realized H (columnMatrix ![1,2,22,8,16]) :=
    realized_mul m108 m95 (by decide +kernel)
  have m110 : Realized H (columnMatrix ![1,2,20,8,16]) :=
    realized_mul m109 m74 (by decide +kernel)
  have m111 : Realized H (columnMatrix ![1,2,4,9,25]) :=
    realized_mul m98 m78 (by decide +kernel)
  have m112 : Realized H (columnMatrix ![1,2,4,8,25]) :=
    realized_mul m111 m98 (by decide +kernel)
  have m113 : Realized H (columnMatrix ![1,2,4,8,17]) :=
    realized_mul m112 m78 (by decide +kernel)
  have m114 : Realized H (columnMatrix ![19,2,4,8,18]) :=
    realized_mul m101 m80 (by decide +kernel)
  have m115 : Realized H (columnMatrix ![19,2,4,8,16]) :=
    realized_mul m114 m101 (by decide +kernel)
  have m116 : Realized H (columnMatrix ![3,2,4,8,16]) :=
    realized_mul m115 m80 (by decide +kernel)
  have m117 : Realized H (columnMatrix ![5,7,4,8,16]) :=
    realized_mul m104 m36 (by decide +kernel)
  have m118 : Realized H (columnMatrix ![1,7,4,8,16]) :=
    realized_mul m117 m104 (by decide +kernel)
  have m119 : Realized H (columnMatrix ![1,6,4,8,16]) :=
    realized_mul m118 m36 (by decide +kernel)
  have m120 : Realized H (columnMatrix ![1,10,14,8,16]) :=
    realized_mul m107 m74 (by decide +kernel)
  have m121 : Realized H (columnMatrix ![1,2,14,8,16]) :=
    realized_mul m120 m107 (by decide +kernel)
  have m122 : Realized H (columnMatrix ![1,2,12,8,16]) :=
    realized_mul m121 m74 (by decide +kernel)
  have m123 : Realized H (columnMatrix ![1,2,20,28,16]) :=
    realized_mul m110 m76 (by decide +kernel)
  have m124 : Realized H (columnMatrix ![1,2,4,28,16]) :=
    realized_mul m123 m110 (by decide +kernel)
  have m125 : Realized H (columnMatrix ![1,2,4,24,16]) :=
    realized_mul m124 m76 (by decide +kernel)
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact (show Matrix.transvection (0 : Fin 5) 1 (1 : ZMod 2) =
        columnMatrix ![1,3,4,8,16] from by decide +kernel).symm ▸ m36
  · exact (show Matrix.transvection (0 : Fin 5) 2 (1 : ZMod 2) =
        columnMatrix ![1,2,5,8,16] from by decide +kernel).symm ▸ m83
  · exact (show Matrix.transvection (0 : Fin 5) 3 (1 : ZMod 2) =
        columnMatrix ![1,2,4,9,16] from by decide +kernel).symm ▸ m98
  · exact (show Matrix.transvection (0 : Fin 5) 4 (1 : ZMod 2) =
        columnMatrix ![1,2,4,8,17] from by decide +kernel).symm ▸ m113
  · exact (show Matrix.transvection (1 : Fin 5) 0 (1 : ZMod 2) =
        columnMatrix ![3,2,4,8,16] from by decide +kernel).symm ▸ m116
  · exact (hij rfl).elim
  · exact (show Matrix.transvection (1 : Fin 5) 2 (1 : ZMod 2) =
        columnMatrix ![1,2,6,8,16] from by decide +kernel).symm ▸ m74
  · exact (show Matrix.transvection (1 : Fin 5) 3 (1 : ZMod 2) =
        columnMatrix ![1,2,4,10,16] from by decide +kernel).symm ▸ m86
  · exact (show Matrix.transvection (1 : Fin 5) 4 (1 : ZMod 2) =
        columnMatrix ![1,2,4,8,18] from by decide +kernel).symm ▸ m101
  · exact (show Matrix.transvection (2 : Fin 5) 0 (1 : ZMod 2) =
        columnMatrix ![5,2,4,8,16] from by decide +kernel).symm ▸ m104
  · exact (show Matrix.transvection (2 : Fin 5) 1 (1 : ZMod 2) =
        columnMatrix ![1,6,4,8,16] from by decide +kernel).symm ▸ m119
  · exact (hij rfl).elim
  · exact (show Matrix.transvection (2 : Fin 5) 3 (1 : ZMod 2) =
        columnMatrix ![1,2,4,12,16] from by decide +kernel).symm ▸ m76
  · exact (show Matrix.transvection (2 : Fin 5) 4 (1 : ZMod 2) =
        columnMatrix ![1,2,4,8,20] from by decide +kernel).symm ▸ m89
  · exact (show Matrix.transvection (3 : Fin 5) 0 (1 : ZMod 2) =
        columnMatrix ![9,2,4,8,16] from by decide +kernel).symm ▸ m92
  · exact (show Matrix.transvection (3 : Fin 5) 1 (1 : ZMod 2) =
        columnMatrix ![1,10,4,8,16] from by decide +kernel).symm ▸ m107
  · exact (show Matrix.transvection (3 : Fin 5) 2 (1 : ZMod 2) =
        columnMatrix ![1,2,12,8,16] from by decide +kernel).symm ▸ m122
  · exact (hij rfl).elim
  · exact (show Matrix.transvection (3 : Fin 5) 4 (1 : ZMod 2) =
        columnMatrix ![1,2,4,8,24] from by decide +kernel).symm ▸ m78
  · exact (show Matrix.transvection (4 : Fin 5) 0 (1 : ZMod 2) =
        columnMatrix ![17,2,4,8,16] from by decide +kernel).symm ▸ m80
  · exact (show Matrix.transvection (4 : Fin 5) 1 (1 : ZMod 2) =
        columnMatrix ![1,18,4,8,16] from by decide +kernel).symm ▸ m95
  · exact (show Matrix.transvection (4 : Fin 5) 2 (1 : ZMod 2) =
        columnMatrix ![1,2,20,8,16] from by decide +kernel).symm ▸ m110
  · exact (show Matrix.transvection (4 : Fin 5) 3 (1 : ZMod 2) =
        columnMatrix ![1,2,4,24,16] from by decide +kernel).symm ▸ m125
  · exact (hij rfl).elim

/-- Any subgroup containing the two displayed matrices is the full SL₅(2). -/
theorem eq_top_of_contains (H : Subgroup Group) (hA : A0 ∈ H) (hB : A1 ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro g _
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun x => x ∈ H) g ?_ ?_ (fun _ _ => H.mul_mem)
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    have hd : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe, hc1]
    rw [hd]
    exact H.one_mem
  · intro i j hij c
    by_cases hc : c = 0
    · subst c
      simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using H.one_mem
    · rw [(by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc]
      obtain ⟨a,ha,he⟩ := roots_realized H hA hB i j hij
      have h : a = Matrix.SpecialLinearGroup.transvection hij 1 := Subtype.ext he
      exact h ▸ ha

/-- The literal two-generator closure, without a group-order enumeration. -/
theorem closure_generators : Subgroup.closure ({A0,A1} : Set Group) = ⊤ :=
  eq_top_of_contains _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

end Representation.SL5ExteriorSquare.TwoGeneratorRecognition
