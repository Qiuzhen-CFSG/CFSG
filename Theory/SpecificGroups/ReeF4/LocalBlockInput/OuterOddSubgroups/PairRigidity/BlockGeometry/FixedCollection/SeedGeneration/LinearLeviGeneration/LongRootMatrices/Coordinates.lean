module

public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Operators
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Block coordinates at the long F₄ end root

The full 52-dimensional Cartan-plus-root lattice decomposes into the six
Cartan/±α coordinates, fourteen natural root strings, and eighteen fixed
root coordinates. The explicit permutation below uses the already certified
F₄ enumeration in `TraceValues.Operators`. In particular it includes the
short roots as well as the long roots.

Source: GLS3 §§2.3–2.4, Table 2.4 type VI, and the common-lattice subsystem
construction of §2.6; `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices
open ReeF4.Cartan.FieldSeparation.TraceValues

abbrev SpecialIndex := Fin 4 ⊕ Fin 2
abbrev BlockIndex := SpecialIndex ⊕ ((Fin 2 × Fin 14) ⊕ Fin 18)

def blockEnumeration : BlockIndex ≃ Fin 52 :=
  (Equiv.sumCongr finSumFinEquiv
    ((Equiv.sumCongr ((Equiv.prodComm _ _).trans finProdFinEquiv)
      (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

/-- First the Cartan coordinates and ±α, then the ordered strings (β, β−α),
then the fixed roots, in the certified numbering of the F₄ lattice. -/
def orderTable : Fin 52 → Fin 52 :=
  ![0, 1, 2, 3, 26, 25, 7, 9, 8, 6, 13, 17, 15, 19, 16, 12, 18, 14, 30, 34, 31, 35, 32, 28, 33, 29, 40, 38, 41, 39, 48, 46, 49, 47, 4, 5, 10, 11, 20, 21, 22, 23, 24, 27, 36, 37, 42, 43, 44, 45, 50, 51]

def order : Equiv.Perm (Fin 52) :=
  Equiv.ofBijective orderTable (by decide +kernel)

/-- Block coordinates expressed in the existing numbered F₄ basis. -/
def numberedEquiv : BlockIndex ≃ Fin 52 := blockEnumeration.trans order

/-- The actual F₄ Cartan-plus-root lattice, with every coordinate retained. -/
def latticeEquiv : BlockIndex ≃ Basis := numberedEquiv.trans basisEquiv

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices
