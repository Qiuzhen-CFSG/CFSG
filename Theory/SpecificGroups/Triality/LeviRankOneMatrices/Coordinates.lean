module
public import Theory.AlgebraicGroup.RootSystems.Classical
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coordinates for the D4 rank-one action

At each numbered simple root, order the 24 roots as the two roots ±α,
eight strings (β, β-α), and six orthogonal roots. Together with the four
Cartan coordinates this is the full 28-dimensional Geck lattice. The explicit
permutations below are bijections, so reindexing loses no coordinates.

Source: the rank-one subsystem construction in GLS3 §2.6, Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`). The identification of these coordinates with
the integral Geck operators is a separate matrix calculation.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.Parabolics.RankOneMatrices
noncomputable section
abbrev SpecialIndex := Fin 4 ⊕ Fin 2
abbrev BlockIndex := SpecialIndex ⊕ ((Fin 2 × Fin 8) ⊕ Fin 6)
abbrev LatticeIndex := (typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)

def pairTable (k : Fin 6) : {p : Fin 4 × Fin 4 // p.1 < p.2} :=
  ⟨![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] k,
    by fin_cases k <;> decide⟩
def pairEquiv : Fin 6 ≃ {p : Fin 4 × Fin 4 // p.1 < p.2} :=
  Equiv.ofBijective pairTable (by decide +kernel)
def signEquiv : Fin 2 ≃ ({-1, 1} : Set ℝ) where
  toFun k := ⟨if k = 0 then 1 else -1, by split_ifs <;> simp⟩
  invFun s := if s.1 = 1 then 0 else 1
  left_inv k := by fin_cases k <;> norm_num
  right_inv s := by
    apply Subtype.ext
    rcases s with ⟨s, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> norm_num

/-- Lexicographic numbering of the roots ±e_a ±e_b, with a < b. -/
def rootEnumeration : Fin 24 ≃ TypeDRootIndex 4 :=
  (finProdFinEquiv : Fin 6 × Fin 4 ≃ Fin 24).symm.trans
    (Equiv.prodCongr pairEquiv
      ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.trans
        (Equiv.prodCongr signEquiv signEquiv)))

/-- At each vertex: α, -α; eight pairs (β, β-α); then the six orthogonal roots. -/
def rootOrderTable (i : Fin 4) : Fin 24 → Fin 24 :=
  ![![1, 2, 4, 12, 5, 13, 8, 16, 9, 17, 14, 6, 15, 7, 18, 10, 19, 11, 0, 3, 20, 21, 22, 23],
    ![13, 14, 0, 4, 2, 6, 5, 1, 7, 3, 16, 20, 17, 21, 22, 18, 23, 19, 8, 9, 10, 11, 12, 15],
    ![21, 22, 4, 8, 6, 10, 9, 5, 11, 7, 12, 16, 14, 18, 17, 13, 19, 15, 0, 1, 2, 3, 20, 23],
    ![20, 23, 4, 9, 6, 11, 8, 5, 10, 7, 12, 17, 14, 19, 16, 13, 18, 15, 0, 1, 2, 3, 21, 22]] i

def rootOrder (i : Fin 4) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (rootOrderTable i) (by fin_cases i <;> decide +kernel)

/-- Join the two exceptional roots, eight strings, and six fixed roots. -/
def rootBlockEnumeration : (Fin 2 ⊕ ((Fin 2 × Fin 8) ⊕ Fin 6)) ≃ Fin 24 :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr ((Equiv.prodComm _ _).trans finProdFinEquiv)
      (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

/-- An explicit reindexing of the full Cartan-plus-root lattice. -/
def latticeEquiv (i : Fin 4) : BlockIndex ≃ LatticeIndex :=
  (Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (typeDRootPairing_baseEquiv 2)
      (rootBlockEnumeration.trans ((rootOrder i).trans rootEnumeration)))

end
end Triality.Standard.Parabolics.RankOneMatrices
