module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Data120
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Norm.Products

/-!
# The initial degree-120 polynomial norm belongs to the generated algebra

Node 19 is the supplied straight-line expression for 1 + g + ... + g^22,
where g is the product of the two published matrices. The checked
products and additions below construct it using only the identity
and the two generators. No density or native-action premise is used.

Source: the unchanged ATLAS M24G1-f2r120B0 matrices and
`Degrees120252/source/density-120.json`; see the source README.
Python supplies data only. All identities are checked in Lean.
-/

set_option Elab.async false
@[expose] public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120

private theorem mem0 (Q : Subalgebra (ZMod 2) (Mat 120)) : matrix c0 ∈ Q :=
  FactorAlgebras.Certificate.one_mem Q c0 (by decide +kernel)

private theorem mem1 (Q : Subalgebra (ZMod 2) (Mat 120))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix c1 ∈ Q := hA 0

private theorem mem2 (Q : Subalgebra (ZMod 2) (Mat 120))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix c2 ∈ Q := hA 1

private theorem mem3 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c3 ∈ Q := by
  exact Norm.product3 ▸ Q.mul_mem (mem1 Q hA) (mem2 Q hA)

set_option maxRecDepth 8192 in
private theorem add4 :
    ∀ i : Fin 120, entry c0 i.val ^^^ entry c3 i.val = entry c4 i.val :=
  by decide +kernel

private theorem mem4 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c4 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c0 c3 c4 (mem0 Q) (mem3 Q hA) add4

private theorem mem5 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c5 ∈ Q := by
  exact Norm.product5 ▸ Q.mul_mem (mem3 Q hA) (mem3 Q hA)

private theorem mem6 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c6 ∈ Q := by
  exact Norm.product6 ▸ Q.mul_mem (mem5 Q hA) (mem4 Q hA)

set_option maxRecDepth 8192 in
private theorem add7 :
    ∀ i : Fin 120, entry c4 i.val ^^^ entry c6 i.val = entry c7 i.val :=
  by decide +kernel

private theorem mem7 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c7 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c4 c6 c7 (mem4 Q hA) (mem6 Q hA) add7

private theorem mem8 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c8 ∈ Q := by
  exact Norm.product8 ▸ Q.mul_mem (mem5 Q hA) (mem5 Q hA)

set_option maxRecDepth 8192 in
private theorem add9 :
    ∀ i : Fin 120, entry c7 i.val ^^^ entry c8 i.val = entry c9 i.val :=
  by decide +kernel

private theorem mem9 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c9 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c7 c8 c9 (mem7 Q hA) (mem8 Q hA) add9

private theorem mem10 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c10 ∈ Q := by
  exact Norm.product10 ▸ Q.mul_mem (mem8 Q hA) (mem3 Q hA)

private theorem mem11 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c11 ∈ Q := by
  exact Norm.product11 ▸ Q.mul_mem (mem10 Q hA) (mem9 Q hA)

set_option maxRecDepth 8192 in
private theorem add12 :
    ∀ i : Fin 120, entry c9 i.val ^^^ entry c11 i.val = entry c12 i.val :=
  by decide +kernel

private theorem mem12 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c12 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c9 c11 c12 (mem9 Q hA) (mem11 Q hA) add12

private theorem mem13 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c13 ∈ Q := by
  exact Norm.product13 ▸ Q.mul_mem (mem10 Q hA) (mem10 Q hA)

set_option maxRecDepth 8192 in
private theorem add14 :
    ∀ i : Fin 120, entry c12 i.val ^^^ entry c13 i.val = entry c14 i.val :=
  by decide +kernel

private theorem mem14 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c14 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c12 c13 c14 (mem12 Q hA) (mem13 Q hA) add14

private theorem mem15 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c15 ∈ Q := by
  exact Norm.product15 ▸ Q.mul_mem (mem13 Q hA) (mem3 Q hA)

private theorem mem16 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c16 ∈ Q := by
  exact Norm.product16 ▸ Q.mul_mem (mem15 Q hA) (mem14 Q hA)

set_option maxRecDepth 8192 in
private theorem add17 :
    ∀ i : Fin 120, entry c14 i.val ^^^ entry c16 i.val = entry c17 i.val :=
  by decide +kernel

private theorem mem17 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c17 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c14 c16 c17 (mem14 Q hA) (mem16 Q hA) add17

private theorem mem18 (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c18 ∈ Q := by
  exact Norm.product18 ▸ Q.mul_mem (mem15 Q hA) (mem15 Q hA)

set_option maxRecDepth 8192 in
private theorem add19 :
    ∀ i : Fin 120, entry c17 i.val ^^^ entry c18 i.val = entry c19 i.val :=
  by decide +kernel

/-- The literal norm node lies in every subalgebra containing the two generators. -/
theorem norm_mem (Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)))
    (hA : ∀ j : Fin 2, matrix120 j ∈ Q) : matrix (n := 120) c19 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c17 c18 c19 (mem17 Q hA) (mem18 Q hA) add19


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120
