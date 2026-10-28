/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianLatticeGlueQuotient.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoQuotient
public import Mathlib.LinearAlgebra.Isomorphisms
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite

/-!
# Icosian Lattice Glue Quotient

Reduction modulo two identifies the actual quotient L/(2I³) with the
complete matrix glue as a right-icosian module. Surjectivity and the
computed kernel yield the equivalence and quotient cardinality 4096.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianLatticeGlueQuotient.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- The complete matrix glue, with its actual right-icosian scalar action. -/
instance icosianMatrixGlue_icosianModule :
    Module icosianOrderᵐᵒᵖ (icosianMatrixGlue GoldenFour) where
  smul a x := ⟨icosianMatrixGlueRightMul x.val (icosianModuloTwo a.unop),
    icosianMatrixGlue_right_mem x.val x.property _⟩
  one_smul x := by
    apply Subtype.ext; funext i
    change x.val i * icosianModuloTwo 1 = x.val i
    rw [map_one,mul_one]
  mul_smul a b x := by
    apply Subtype.ext; funext i
    change x.val i * icosianModuloTwo (b.unop*a.unop) =
      (x.val i * icosianModuloTwo b.unop) * icosianModuloTwo a.unop
    rw [map_mul,mul_assoc]
  smul_zero a := by
    apply Subtype.ext; funext i
    change (0 : IcosianMatrix) * icosianModuloTwo a.unop = 0
    exact zero_mul _
  smul_add a x y := by
    apply Subtype.ext; funext i
    change (x.val i+y.val i) * icosianModuloTwo a.unop =
      x.val i * icosianModuloTwo a.unop + y.val i * icosianModuloTwo a.unop
    exact add_mul _ _ _
  add_smul a b x := by
    apply Subtype.ext; funext i
    change x.val i * icosianModuloTwo (a.unop+b.unop) =
      x.val i * icosianModuloTwo a.unop + x.val i * icosianModuloTwo b.unop
    rw [map_add,mul_add]
  zero_smul x := by
    apply Subtype.ext; funext i
    change x.val i * icosianModuloTwo 0 = 0
    rw [map_zero,mul_zero]

def icosianLatticeGlueReduction : icosianLeechModule →ₗ[icosianOrderᵐᵒᵖ]
    icosianMatrixGlue GoldenFour where
  toFun x := ⟨fun i => icosianModuloTwo (x.val i),
    (icosianLeechModule_matrix_glue x.val).mp x.property⟩
  map_add' x y := by apply Subtype.ext; funext i; exact map_add icosianModuloTwo _ _
  map_smul' a x := by
    apply Subtype.ext; funext i
    change icosianModuloTwo (x.val i * a.unop) = icosianModuloTwo (x.val i) * icosianModuloTwo a.unop
    exact map_mul icosianModuloTwo _ _

theorem icosianLatticeGlueReduction_surjective : Function.Surjective icosianLatticeGlueReduction := by
  intro m
  choose x hx using fun i => icosianModuloTwo_surjective (m.val i)
  have hm : x ∈ icosianLeechModule := by
    rw [icosianLeechModule_matrix_glue]
    simpa only [hx] using m.property
  exact ⟨⟨x,hm⟩,Subtype.ext (funext hx)⟩

/-- Twice the full coordinate module, viewed inside the actual lattice. -/
def icosianLatticeTwice : Submodule icosianOrderᵐᵒᵖ icosianLeechModule :=
  LinearMap.ker icosianLatticeGlueReduction

theorem icosianLatticeTwice_mem (x : icosianLeechModule) :
    x ∈ icosianLatticeTwice ↔ ∃ y : IcosianCoordinates, x.val = (2 : ℤ) • y := by
  change icosianLatticeGlueReduction x = 0 ↔ _
  constructor
  · intro h
    have hz (i : Fin 3) : icosianModuloTwo (x.val i)=0 :=
      congrFun (congrArg Subtype.val h) i
    choose y hy using fun i => (icosianModuloTwo_eq_zero_iff_two_mul (x.val i)).mp (hz i)
    refine ⟨y,?_⟩
    funext i
    simpa only [Pi.smul_apply,two_smul,two_mul] using hy i
  · rintro ⟨y,hy⟩
    apply Subtype.ext; funext i
    apply (icosianModuloTwo_eq_zero_iff_two_mul (x.val i)).mpr
    exact ⟨y i,by simpa only [Pi.smul_apply,two_smul,two_mul] using congrFun hy i⟩

/-- The actual quotient L/(2I³) is the complete right-matrix glue. -/
def icosianLatticeGlueQuotient :
    (icosianLeechModule ⧸ icosianLatticeTwice) ≃ₗ[icosianOrderᵐᵒᵖ]
      icosianMatrixGlue GoldenFour :=
  icosianLatticeGlueReduction.quotKerEquivOfSurjective icosianLatticeGlueReduction_surjective

theorem icosianLatticeGlueQuotient_mk (x : icosianLeechModule) :
    (icosianLatticeGlueQuotient (Submodule.Quotient.mk x)).val =
      fun i => icosianModuloTwo (x.val i) := rfl

theorem icosianLatticeGlueQuotient_card :
    Nat.card (icosianLeechModule ⧸ icosianLatticeTwice) = 4096 := by
  rw [Nat.card_congr icosianLatticeGlueQuotient.toEquiv]
  exact icosianMatrixGlue_card_four (by rw [Nat.card_eq_fintype_card,goldenFour_card])

end Atlas.Lattices
