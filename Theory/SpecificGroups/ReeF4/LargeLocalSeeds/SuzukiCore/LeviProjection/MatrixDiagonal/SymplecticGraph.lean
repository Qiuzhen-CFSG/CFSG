module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.MatrixGraph
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.Basic

/-!
# The paired matrix relation is the exceptional symplectic graph

The four signed matrices from `MatrixGraph` are precisely the native
symplectic root families numbered 2, 6, 3, and 7, after changing to Suzuki's
basis. Two explicit Weyl conjugations supply the other four root families.
Symplectic Gaussian elimination therefore proves that the signed families
generate the whole matrix group Sp₄.

The existing exterior-square automorphism, followed by the `m`th Frobenius
power, has exactly the prescribed paired-generator formula. Generation
identifies the whole paired subgroup with its graph. Injectivity of the
coordinate embedding proves functionality and identifies the paired diagonal
with the image of the genuine fixed subgroup. These arguments work for every
`m`, including zero, independently of any representation of the F₄ Levi.

Identifying the fixed symplectic matrices with the concrete Suzuki generators
is a separate calculation. No fixed-point generation principle is assumed.
Source: Aschbacher–Smith F.1.12(I)(5), printed p.263 (PDF p.274), and
`refs/KGroup/GLS3/chapter2.tex`, §2.4, Table 2.4 type V, and §2.5.
-/

@[expose] public noncomputable section

namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.MatrixDiagonal

open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Representation.OneCohomology.SymplecticFour
open GraphFieldFixedResidual

/-- Embed the actual symplectic matrices in the specified Suzuki basis. -/
def coordinatesHom (m : ℕ) : Sp (CoefficientField m) →* MatrixGroup m :=
  ((Matrix.reindexRingEquiv (CoefficientField m) suzukiIndex).toMonoidHom.comp
    (Matrix.symplecticGroup (Fin 2) (CoefficientField m)).subtype).toHomUnits

theorem coordinatesHom_val (m : ℕ) (g : Sp (CoefficientField m)) :
    (coordinatesHom m g).val = matrixCoordinates (RingEquiv.refl _) g := rfl

/-- Native symplectic root indices for long+, short+, long−, short−. -/
def simpleIndex (i : Fin 4) : Fin 8 := ![2, 6, 3, 7] i

/-- The four signed simple families inside the actual symplectic group. -/
def simpleRoot (m : ℕ) (a : Fin 4 × CoefficientField m) : Sp (CoefficientField m) :=
  rootElement (simpleIndex a.1) a.2

theorem coordinatesHom_simpleRoot (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    coordinatesHom m (simpleRoot m (i, t)) = matrixGenerator m i t := by
  apply Units.ext
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [coordinatesHom_val, matrixCoordinates, suzukiIndex, simpleRoot, simpleIndex,
      rootElement, rootMatrix, matrixGenerator, generatorMatrix, Matrix.fromBlocks,
      Matrix.single, CharTwo.neg_eq]

variable {F : Type*} [Field F] [CharP F 2]

private def shortWeyl : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1
private def longWeyl : Sp F := rootElement 2 1 * rootElement 3 1 * rootElement 2 1

private theorem shortWeyl_val : (shortWeyl : Sp F).val =
    Matrix.fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [shortWeyl, rootElement, rootMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem longWeyl_val : (longWeyl : Sp F).val =
    Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1]
      !![0, 0; 0, 1] !![1, 0; 0, 0] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [longWeyl, rootElement, rootMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      CharTwo.add_self_eq_zero]

private theorem conjugate_long_root (i : Fin 2) (t : F) :
    shortWeyl * rootElement (![2, 3] i) t * shortWeyl = rootElement (![0, 1] i) t := by
  apply Subtype.ext
  change shortWeyl.val * (rootElement _ t).val * shortWeyl.val = _
  rw [shortWeyl_val]
  ext j k
  fin_cases i <;> rcases j with j | j <;> rcases k with k | k <;>
    fin_cases j <;> fin_cases k <;>
    simp [rootElement, rootMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single]

private theorem conjugate_short_root (i : Fin 2) (t : F) :
    longWeyl * rootElement (![6, 7] i) t * longWeyl = rootElement (![4, 5] i) t := by
  apply Subtype.ext
  change longWeyl.val * (rootElement _ t).val * longWeyl.val = _
  rw [longWeyl_val]
  ext j k
  fin_cases i <;> rcases j with j | j <;> rcases k with k | k <;>
    fin_cases j <;> fin_cases k <;>
    simp [rootElement, rootMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      CharTwo.neg_eq]

theorem coordinatesHom_injective (m : ℕ) : Function.Injective (coordinatesHom m) := by
  intro g h hgh
  exact matrixCoordinates_injective (RingEquiv.refl _) (congrArg Units.val hgh)

/-- The genuine automorphism has exactly the paired generator formula. -/
theorem graphFieldAut_simpleRoot (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    graphFieldAut m (simpleRoot m (i, t)) =
      simpleRoot m (swapIndex i, twistParameter m i t) := by
  change (ExceptionalGraph.graphAut ^ (2 * m + 1)) (rootElement (simpleIndex i) t) = _
  rw [pow_succ, MulAut.mul_apply, graphAut_even, ExceptionalGraph.graphAut_apply,
    ExceptionalGraph.graphEnd_root, ExceptionalGraph.fieldAutomorphism_root]
  fin_cases i <;>
    simp [simpleRoot, simpleIndex, swapIndex, twistParameter_eq,
      ExceptionalGraph.rootPermutation, ExceptionalGraph.rootParameter,
      iterateFrobenius_def, ← pow_mul, ← pow_succ']

/-- The graph of the concrete exceptional automorphism, in the specified basis. -/
def pairCoordinates (m : ℕ) : Sp (CoefficientField m) →* MatrixGroup m × MatrixGroup m :=
  (coordinatesHom m).prod
    ((coordinatesHom m).comp (graphFieldAut (F := CoefficientField m) m).toMonoidHom)

theorem pairCoordinates_simpleRoot (m : ℕ) (a : Fin 4 × CoefficientField m) :
    pairCoordinates m (simpleRoot m a) = pairedGenerator m a := by
  rcases a with ⟨i, t⟩
  apply Prod.ext
  · exact coordinatesHom_simpleRoot m i t
  · change coordinatesHom m (graphFieldAut m (simpleRoot m (i, t))) = _
    rw [graphFieldAut_simpleRoot, coordinatesHom_simpleRoot]
    rfl

/-- The four signed simple root families generate all of Sp₄. The other four
families are the displayed Weyl conjugates, so this uses actual matrix generation. -/
theorem simpleRoot_generate (m : ℕ) :
    Subgroup.closure (Set.range (simpleRoot m)) = ⊤ := by
  let H := Subgroup.closure (Set.range (simpleRoot m))
  have h2 (t : CoefficientField m) : rootElement 2 t ∈ H :=
    Subgroup.subset_closure ⟨(0, t), rfl⟩
  have h6 (t : CoefficientField m) : rootElement 6 t ∈ H :=
    Subgroup.subset_closure ⟨(1, t), rfl⟩
  have h3 (t : CoefficientField m) : rootElement 3 t ∈ H :=
    Subgroup.subset_closure ⟨(2, t), rfl⟩
  have h7 (t : CoefficientField m) : rootElement 7 t ∈ H :=
    Subgroup.subset_closure ⟨(3, t), rfl⟩
  have hs : shortWeyl ∈ H := H.mul_mem (H.mul_mem (h6 1) (h7 1)) (h6 1)
  have hl : longWeyl ∈ H := H.mul_mem (H.mul_mem (h2 1) (h3 1)) (h2 1)
  apply eq_top_of_rootElement_mem
  intro i t
  fin_cases i
  · have he : shortWeyl * rootElement 2 t * shortWeyl = rootElement 0 t :=
      conjugate_long_root 0 t
    exact (congrArg (fun x => x ∈ H) he).mp (H.mul_mem (H.mul_mem hs (h2 t)) hs)
  · have he : shortWeyl * rootElement 3 t * shortWeyl = rootElement 1 t :=
      conjugate_long_root 1 t
    exact (congrArg (fun x => x ∈ H) he).mp (H.mul_mem (H.mul_mem hs (h3 t)) hs)
  · exact h2 t
  · exact h3 t
  · have he : longWeyl * rootElement 6 t * longWeyl = rootElement 4 t :=
      conjugate_short_root 0 t
    exact (congrArg (fun x => x ∈ H) he).mp (H.mul_mem (H.mul_mem hl (h6 t)) hl)
  · have he : longWeyl * rootElement 7 t * longWeyl = rootElement 5 t :=
      conjugate_short_root 1 t
    exact (congrArg (fun x => x ∈ H) he).mp (H.mul_mem (H.mul_mem hl (h7 t)) hl)
  · exact h6 t
  · exact h7 t

/-- Every pair in the generated relation comes from the actual exceptional
automorphism, and every symplectic matrix supplies a pair. -/
theorem pairedSubgroup_eq_range (m : ℕ) :
    pairedSubgroup m = (pairCoordinates m).range := by
  change Subgroup.closure (Set.range (pairedGenerator m)) = _
  rw [MonoidHom.range_eq_map, ← simpleRoot_generate m, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  exact (congrArg Set.range (funext (pairCoordinates_simpleRoot m))).symm

/-- Elementwise graph coverage; no fixed-point surjectivity principle is used. -/
theorem mem_pairedSubgroup_iff (m : ℕ) (A B : MatrixGroup m) :
    (A, B) ∈ pairedSubgroup m ↔
      ∃ g : Sp (CoefficientField m),
        coordinatesHom m g = A ∧ coordinatesHom m (graphFieldAut m g) = B := by
  rw [pairedSubgroup_eq_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  · rintro ⟨g, hg₁, hg₂⟩
    exact ⟨g, Prod.ext hg₁ hg₂⟩

/-- The generated relation is functional in its first coordinate. -/
theorem pairedSubgroup_functional (m : ℕ) {A B C : MatrixGroup m}
    (hAB : (A, B) ∈ pairedSubgroup m) (hAC : (A, C) ∈ pairedSubgroup m) : B = C := by
  obtain ⟨g, hg₁, hg₂⟩ := (mem_pairedSubgroup_iff m A B).mp hAB
  obtain ⟨h, hh₁, hh₂⟩ := (mem_pairedSubgroup_iff m A C).mp hAC
  have hgh := coordinatesHom_injective m (hg₁.trans hh₁.symm)
  exact hg₂.symm.trans (hgh ▸ hh₂)

/-- The diagonal is precisely the coordinate image of the genuine fixed subgroup. -/
theorem pairedDiagonal_eq_map_fixed (m : ℕ) :
    pairedDiagonal m =
      ((graphFieldAut (F := CoefficientField m) m).fixedSubgroup).map (coordinatesHom m) := by
  ext A
  change (A, A) ∈ pairedSubgroup m ↔ _
  rw [mem_pairedSubgroup_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg₁, hg₂⟩
    exact ⟨g, (MulAut.mem_fixedSubgroup _ _).mpr
      (coordinatesHom_injective m (hg₂.trans hg₁.symm)), hg₁⟩
  · rintro ⟨g, hg, hA⟩
    exact ⟨g, hA,
      (congrArg (coordinatesHom m) ((MulAut.mem_fixedSubgroup _ _).mp hg)).trans hA⟩

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.MatrixDiagonal
