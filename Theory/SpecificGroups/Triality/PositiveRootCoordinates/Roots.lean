module

public import Theory.AlgebraicGroup.RootSystems.TypeD4DiagramTriality

/-!
# An orbit-compatible ordering of the positive D4 roots

The order is α₀, α₂, α₃, α₁, α₀+α₁, α₁+α₂, α₁+α₃,
α₀+α₁+α₂, α₁+α₂+α₃, α₀+α₁+α₃, α₀+α₁+α₂+α₃,
α₀+2α₁+α₂+α₃. It is grouped into the three length-three diagram
orbits and the three singleton orbits. Its entries are actual indices of
`typeDRootPairing 2`; coordinate expansion proves the diagram action.

Source: GLS3, 2.3.6–7 and Table 2.4 (`refs/KGroup/GLS3/chapter2.tex`).
The matrix normal form and its equivariance require additional proofs.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
namespace Triality.Standard.PositiveCoordinates
noncomputable section

def difference (i j : Fin 4) (h : i < j) : TypeDRootIndex 4 :=
  ⟨⟨(i, j), h⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩

def sumRoot (i j : Fin 4) (h : i < j) : TypeDRootIndex 4 :=
  ⟨⟨(i, j), h⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

/-- Positive roots, in increasing height and with each diagram orbit contiguous. -/
def rootIndex : Fin 12 → TypeDRootIndex 4 :=
  ![difference 0 1 (by decide), difference 2 3 (by decide),
    sumRoot 2 3 (by decide), difference 1 2 (by decide),
    difference 0 2 (by decide), difference 1 3 (by decide),
    sumRoot 1 3 (by decide), difference 0 3 (by decide),
    sumRoot 1 2 (by decide), sumRoot 0 3 (by decide),
    sumRoot 0 2 (by decide), sumRoot 0 1 (by decide)]

/-- Three cycles (0 1 2), (4 5 6), (7 8 9), and three singleton orbits. -/
def diagram : Equiv.Perm (Fin 12) where
  toFun := ![1, 2, 0, 3, 5, 6, 4, 8, 9, 7, 10, 11]
  invFun := ![2, 0, 1, 3, 6, 4, 5, 9, 7, 8, 10, 11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Simple-root coefficients of the twelve displayed roots. -/
def coefficients : Fin 12 → Fin 4 → ℝ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 1, 0, 0],
    ![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 1], ![1, 1, 1, 0],
    ![0, 1, 1, 1], ![1, 1, 0, 1], ![1, 1, 1, 1], ![1, 2, 1, 1]]

theorem root_expansion (i : Fin 12) :
    (typeDRootPairing 2).root (rootIndex i) =
      ∑ j : Fin 4, coefficients i j •
        (typeDRootPairing 2).root (typeDSimpleRootIndex 2 j) := by
  apply Subtype.ext
  ext k
  fin_cases i <;> fin_cases k <;>
    norm_num [rootIndex, coefficients, difference, sumRoot, Fin.sum_univ_succ,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      typeDSimpleRootIndex, basisVector, Pi.single_apply, Fin.ext_iff]

theorem diagram_rootIndex (i : Fin 12) :
    typeD4DiagramEquiv.indexEquiv (rootIndex i) = rootIndex (diagram i) := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, root_expansion, root_expansion]
  simp only [map_sum, map_smul, RootPairing.Hom.root_weightMap_apply,
    typeD4DiagramEquiv_numbered]
  fin_cases i <;>
    simp [coefficients, diagram, typeD4DiagramPermutation, Fin.sum_univ_succ] <;>
    module

def simplePosition : Fin 4 → Fin 12 := ![0, 3, 1, 2]

theorem rootIndex_simple (i : Fin 4) :
    rootIndex (simplePosition i) = typeDSimpleRootIndex 2 i := by
  fin_cases i <;> rfl

theorem rootIndex_injective : Function.Injective rootIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [rootIndex, difference, sumRoot, Prod.mk.injEq, Subtype.mk.injEq] <;>
    norm_num at h

def leftParent : Fin 8 → Fin 12 := ![0, 1, 2, 4, 5, 6, 7, 10]
def rightParent : Fin 8 → Fin 12 := ![3, 3, 3, 1, 2, 0, 2, 3]

theorem root_add (i : Fin 8) :
    (typeDRootPairing 2).root (rootIndex ⟨i + 4, by omega⟩) =
      (typeDRootPairing 2).root (rootIndex (leftParent i)) +
        (typeDRootPairing 2).root (rootIndex (rightParent i)) := by
  rw [root_expansion, root_expansion, root_expansion]
  fin_cases i <;> simp [coefficients, leftParent, rightParent, Fin.sum_univ_succ] <;>
    module

theorem rootIndex_positive (i : Fin 12) :
    (typeDRootPairing_base 2).IsPos (rootIndex i) := by
  have hs (j : Fin 4) :
      (typeDRootPairing_base 2).IsPos (rootIndex (simplePosition j)) := by
    rw [rootIndex_simple]
    exact (typeDRootPairing_base 2).isPos_of_mem_support
      (typeDRootPairing_baseEquiv 2 j).property
  have h0 := hs 0
  have h1 := hs 2
  have h2 := hs 3
  have h3 := hs 1
  have h4 := h0.add h3 (root_add 0)
  have h5 := h1.add h3 (root_add 1)
  have h6 := h2.add h3 (root_add 2)
  have h7 := h4.add h1 (root_add 3)
  have h8 := h5.add h2 (root_add 4)
  have h9 := h6.add h0 (root_add 5)
  have h10 := h7.add h2 (root_add 6)
  have h11 := h10.add h3 (root_add 7)
  fin_cases i <;> assumption

private theorem exists_rootIndex_of_first_sign (r : TypeDRootIndex 4) (h : r.2.1.1 = 1) :
    ∃ i, rootIndex i = r := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  dsimp at h
  subst s
  have ht' : t = -1 ∨ t = 1 := by simpa using ht
  rcases ht' with rfl | rfl
  all_goals
    fin_cases i <;> fin_cases j <;> simp only [Fin.mk_lt_mk] at hij <;> try omega
  all_goals
    first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩
    | exact ⟨7, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩
    | exact ⟨11, rfl⟩

private theorem exists_rootIndex_or_neg (r : TypeDRootIndex 4) :
    ∃ i, r = rootIndex i ∨
      (typeDRootPairing 2).root r = -(typeDRootPairing 2).root (rootIndex i) := by
  rcases r with ⟨p, ⟨s, hs⟩, ⟨t, ht⟩⟩
  have hs' : s = -1 ∨ s = 1 := by simpa using hs
  rcases hs' with rfl | hs
  ·
    let r' : TypeDRootIndex 4 := ⟨p, ⟨1, by simp⟩, ⟨-t, by
      have ht' : t = -1 ∨ t = 1 := by simpa using ht
      rcases ht' with rfl | rfl <;> norm_num⟩⟩
    obtain ⟨i, hi⟩ := exists_rootIndex_of_first_sign r' rfl
    refine ⟨i, Or.inr ?_⟩
    rw [hi]
    apply Subtype.ext
    simp only [typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      Submodule.coe_neg, r', neg_smul, one_smul]
    module
  · obtain ⟨i, hi⟩ := exists_rootIndex_of_first_sign ⟨p, ⟨s, by simp [hs]⟩, ⟨t, ht⟩⟩ hs
    exact ⟨i, Or.inl hi.symm⟩

theorem range_rootIndex : Set.range rootIndex =
    {r | (typeDRootPairing_base 2).IsPos r} := by
  ext r
  constructor
  · rintro ⟨i, rfl⟩
    exact rootIndex_positive i
  · intro hr
    obtain ⟨i, hi | hi⟩ := exists_rootIndex_or_neg r
    · exact ⟨i, hi.symm⟩
    · let := (typeDRootPairing 2).indexNeg
      have h : r = -(rootIndex i) := (typeDRootPairing 2).root_eq_neg_iff.mp hi
      rw [h] at hr
      exact False.elim ((RootPairing.Base.IsPos.neg_iff_not (b := typeDRootPairing_base 2) _).mp hr
        (rootIndex_positive i))


@[simp] theorem diagram_three (i : Fin 12) :
    diagram (diagram (diagram i)) = i := by
  fin_cases i <;> rfl

theorem diagram_fixed_iff (i : Fin 12) :
    diagram i = i ↔ i = 3 ∨ i = 10 ∨ i = 11 := by
  fin_cases i <;> decide

end
end Triality.Standard.PositiveCoordinates
