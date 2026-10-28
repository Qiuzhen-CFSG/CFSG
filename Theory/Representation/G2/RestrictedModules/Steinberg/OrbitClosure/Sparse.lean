module

public import Theory.Representation.G2.RestrictedModules.Steinberg.Construction
public import Mathlib.Tactic.Module

/-!
# Sparse tensor generators for the G₂ binary orbit

These are explicit tensors in the natural tensor cube, grouped by torus weight.
The following modules certify their change of spanning family and the action of
all root, Weyl and torus generators. No dimension or independence is assumed.
Source: the concrete construction for GLS3 2.8.7 and 2.8.10(g).
-/

@[expose] public noncomputable section
namespace Atlas.G2.Restricted.Steinberg.OrbitClosure
open NaturalCoordinates
open scoped TensorProduct
variable (F : Type*) [Field F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

def b0 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 1) + pure F (e F 0) (e F 1) (e F 0)

def b1 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 2) + pure F (e F 0) (e F 2) (e F 0)

def b2 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 3) + pure F (e F 0) (e F 3) (e F 0)

def b3 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 4) + pure F (e F 0) (e F 4) (e F 0)

def b4 : Ambient F :=
  pure F (e F 1) (e F 0) (e F 1) + pure F (e F 1) (e F 1) (e F 0)

def b5 : Ambient F :=
  pure F (e F 0) (e F 1) (e F 2) + pure F (e F 0) (e F 2) (e F 1) + pure F (e F 1) (e F 0) (e F 2) + pure F (e F 1) (e F 2) (e F 0)

def b6 : Ambient F :=
  pure F (e F 1) (e F 1) (e F 2) + pure F (e F 1) (e F 2) (e F 1)

def b7 : Ambient F :=
  pure F (e F 0) (e F 1) (e F 3) + pure F (e F 0) (e F 3) (e F 1) + pure F (e F 1) (e F 0) (e F 3) + pure F (e F 1) (e F 3) (e F 0)

def b8 : Ambient F :=
  pure F (e F 1) (e F 1) (e F 3) + pure F (e F 1) (e F 3) (e F 1)

def b9 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 5) + pure F (e F 0) (e F 1) (e F 4) + pure F (e F 0) (e F 4) (e F 1) + pure F (e F 0) (e F 5) (e F 0) + pure F (e F 1) (e F 0) (e F 4) + pure F (e F 1) (e F 4) (e F 0)

def b10 : Ambient F :=
  pure F (e F 0) (e F 1) (e F 5) + pure F (e F 0) (e F 5) (e F 1) + pure F (e F 1) (e F 0) (e F 5) + pure F (e F 1) (e F 1) (e F 4) + pure F (e F 1) (e F 4) (e F 1) + pure F (e F 1) (e F 5) (e F 0)

def b11 : Ambient F :=
  pure F (e F 1) (e F 1) (e F 5) + pure F (e F 1) (e F 5) (e F 1)

def b12 : Ambient F :=
  pure F (e F 0) (e F 1) (e F 2) + pure F (e F 0) (e F 2) (e F 1) + pure F (e F 2) (e F 0) (e F 1) + pure F (e F 2) (e F 1) (e F 0)

def b13 : Ambient F :=
  pure F (e F 2) (e F 0) (e F 2) + pure F (e F 2) (e F 2) (e F 0)

def b14 : Ambient F :=
  pure F (e F 2) (e F 1) (e F 2) + pure F (e F 2) (e F 2) (e F 1)

def b15 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 5) + pure F (e F 0) (e F 2) (e F 3) + pure F (e F 0) (e F 3) (e F 2) + pure F (e F 0) (e F 5) (e F 0) + pure F (e F 2) (e F 0) (e F 3) + pure F (e F 2) (e F 3) (e F 0)

def b16 : Ambient F :=
  pure F (e F 1) (e F 1) (e F 4) + pure F (e F 1) (e F 2) (e F 3) + pure F (e F 1) (e F 3) (e F 2) + pure F (e F 1) (e F 4) (e F 1) + pure F (e F 2) (e F 1) (e F 3) + pure F (e F 2) (e F 3) (e F 1)

def b17 : Ambient F :=
  pure F (e F 0) (e F 2) (e F 4) + pure F (e F 0) (e F 4) (e F 2) + pure F (e F 2) (e F 0) (e F 4) + pure F (e F 2) (e F 4) (e F 0)

def b18 : Ambient F :=
  pure F (e F 1) (e F 2) (e F 4) + pure F (e F 1) (e F 4) (e F 2) + pure F (e F 2) (e F 1) (e F 4) + pure F (e F 2) (e F 2) (e F 3) + pure F (e F 2) (e F 3) (e F 2) + pure F (e F 2) (e F 4) (e F 1)

def b19 : Ambient F :=
  pure F (e F 2) (e F 2) (e F 4) + pure F (e F 2) (e F 4) (e F 2)

def b20 : Ambient F :=
  pure F (e F 0) (e F 2) (e F 5) + pure F (e F 0) (e F 5) (e F 2) + pure F (e F 2) (e F 0) (e F 5) + pure F (e F 2) (e F 2) (e F 3) + pure F (e F 2) (e F 3) (e F 2) + pure F (e F 2) (e F 5) (e F 0)

def b21 : Ambient F :=
  pure F (e F 1) (e F 2) (e F 5) + pure F (e F 1) (e F 5) (e F 2) + pure F (e F 2) (e F 1) (e F 5) + pure F (e F 2) (e F 5) (e F 1)

def b22 : Ambient F :=
  pure F (e F 2) (e F 2) (e F 5) + pure F (e F 2) (e F 5) (e F 2)

def b23 : Ambient F :=
  pure F (e F 0) (e F 1) (e F 3) + pure F (e F 0) (e F 3) (e F 1) + pure F (e F 3) (e F 0) (e F 1) + pure F (e F 3) (e F 1) (e F 0)

def b24 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 5) + pure F (e F 0) (e F 2) (e F 3) + pure F (e F 0) (e F 3) (e F 2) + pure F (e F 0) (e F 5) (e F 0) + pure F (e F 3) (e F 0) (e F 2) + pure F (e F 3) (e F 2) (e F 0)

def b25 : Ambient F :=
  pure F (e F 1) (e F 1) (e F 4) + pure F (e F 1) (e F 2) (e F 3) + pure F (e F 1) (e F 3) (e F 2) + pure F (e F 1) (e F 4) (e F 1) + pure F (e F 3) (e F 1) (e F 2) + pure F (e F 3) (e F 2) (e F 1)

def b26 : Ambient F :=
  pure F (e F 3) (e F 0) (e F 3) + pure F (e F 3) (e F 3) (e F 0)

def b27 : Ambient F :=
  pure F (e F 3) (e F 1) (e F 3) + pure F (e F 3) (e F 3) (e F 1)

def b28 : Ambient F :=
  pure F (e F 0) (e F 3) (e F 4) + pure F (e F 0) (e F 4) (e F 3) + pure F (e F 3) (e F 0) (e F 4) + pure F (e F 3) (e F 4) (e F 0)

def b29 : Ambient F :=
  pure F (e F 1) (e F 3) (e F 4) + pure F (e F 1) (e F 4) (e F 3) + pure F (e F 3) (e F 1) (e F 4) + pure F (e F 3) (e F 2) (e F 3) + pure F (e F 3) (e F 3) (e F 2) + pure F (e F 3) (e F 4) (e F 1)

def b30 : Ambient F :=
  pure F (e F 2) (e F 3) (e F 4) + pure F (e F 2) (e F 4) (e F 3) + pure F (e F 3) (e F 2) (e F 4) + pure F (e F 3) (e F 4) (e F 2)

def b31 : Ambient F :=
  pure F (e F 3) (e F 3) (e F 4) + pure F (e F 3) (e F 4) (e F 3)

def b32 : Ambient F :=
  pure F (e F 0) (e F 3) (e F 5) + pure F (e F 0) (e F 5) (e F 3) + pure F (e F 3) (e F 0) (e F 5) + pure F (e F 3) (e F 2) (e F 3) + pure F (e F 3) (e F 3) (e F 2) + pure F (e F 3) (e F 5) (e F 0)

def b33 : Ambient F :=
  pure F (e F 1) (e F 3) (e F 5) + pure F (e F 1) (e F 5) (e F 3) + pure F (e F 3) (e F 1) (e F 5) + pure F (e F 3) (e F 5) (e F 1)

def b34 : Ambient F :=
  pure F (e F 2) (e F 3) (e F 5) + pure F (e F 2) (e F 5) (e F 3) + pure F (e F 3) (e F 2) (e F 5) + pure F (e F 3) (e F 5) (e F 2)

def b35 : Ambient F :=
  pure F (e F 3) (e F 3) (e F 5) + pure F (e F 3) (e F 5) (e F 3)

def b36 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 5) + pure F (e F 0) (e F 1) (e F 4) + pure F (e F 0) (e F 4) (e F 1) + pure F (e F 0) (e F 5) (e F 0) + pure F (e F 4) (e F 0) (e F 1) + pure F (e F 4) (e F 1) (e F 0)

def b37 : Ambient F :=
  pure F (e F 0) (e F 2) (e F 4) + pure F (e F 0) (e F 4) (e F 2) + pure F (e F 4) (e F 0) (e F 2) + pure F (e F 4) (e F 2) (e F 0)

def b38 : Ambient F :=
  pure F (e F 1) (e F 2) (e F 4) + pure F (e F 1) (e F 4) (e F 2) + pure F (e F 4) (e F 1) (e F 2) + pure F (e F 4) (e F 2) (e F 1)

def b39 : Ambient F :=
  pure F (e F 0) (e F 3) (e F 4) + pure F (e F 0) (e F 4) (e F 3) + pure F (e F 4) (e F 0) (e F 3) + pure F (e F 4) (e F 3) (e F 0)

def b40 : Ambient F :=
  pure F (e F 1) (e F 3) (e F 4) + pure F (e F 1) (e F 4) (e F 3) + pure F (e F 4) (e F 1) (e F 3) + pure F (e F 4) (e F 3) (e F 1)

def b41 : Ambient F :=
  pure F (e F 4) (e F 0) (e F 4) + pure F (e F 4) (e F 4) (e F 0)

def b42 : Ambient F :=
  pure F (e F 2) (e F 3) (e F 4) + pure F (e F 2) (e F 4) (e F 3) + pure F (e F 4) (e F 1) (e F 4) + pure F (e F 4) (e F 2) (e F 3) + pure F (e F 4) (e F 3) (e F 2) + pure F (e F 4) (e F 4) (e F 1)

def b43 : Ambient F :=
  pure F (e F 4) (e F 2) (e F 4) + pure F (e F 4) (e F 4) (e F 2)

def b44 : Ambient F :=
  pure F (e F 4) (e F 3) (e F 4) + pure F (e F 4) (e F 4) (e F 3)

def b45 : Ambient F :=
  pure F (e F 0) (e F 4) (e F 5) + pure F (e F 0) (e F 5) (e F 4) + pure F (e F 2) (e F 3) (e F 4) + pure F (e F 2) (e F 4) (e F 3) + pure F (e F 4) (e F 0) (e F 5) + pure F (e F 4) (e F 2) (e F 3) + pure F (e F 4) (e F 3) (e F 2) + pure F (e F 4) (e F 5) (e F 0)

def b46 : Ambient F :=
  pure F (e F 1) (e F 4) (e F 5) + pure F (e F 1) (e F 5) (e F 4) + pure F (e F 4) (e F 1) (e F 5) + pure F (e F 4) (e F 5) (e F 1)

def b47 : Ambient F :=
  pure F (e F 2) (e F 4) (e F 5) + pure F (e F 2) (e F 5) (e F 4) + pure F (e F 4) (e F 2) (e F 5) + pure F (e F 4) (e F 5) (e F 2)

def b48 : Ambient F :=
  pure F (e F 3) (e F 4) (e F 5) + pure F (e F 3) (e F 5) (e F 4) + pure F (e F 4) (e F 3) (e F 5) + pure F (e F 4) (e F 5) (e F 3)

def b49 : Ambient F :=
  pure F (e F 4) (e F 4) (e F 5) + pure F (e F 4) (e F 5) (e F 4)

def b50 : Ambient F :=
  pure F (e F 0) (e F 1) (e F 5) + pure F (e F 0) (e F 5) (e F 1) + pure F (e F 5) (e F 0) (e F 1) + pure F (e F 5) (e F 1) (e F 0)

def b51 : Ambient F :=
  pure F (e F 0) (e F 2) (e F 5) + pure F (e F 0) (e F 5) (e F 2) + pure F (e F 5) (e F 0) (e F 2) + pure F (e F 5) (e F 2) (e F 0)

def b52 : Ambient F :=
  pure F (e F 1) (e F 2) (e F 5) + pure F (e F 1) (e F 5) (e F 2) + pure F (e F 5) (e F 1) (e F 2) + pure F (e F 5) (e F 2) (e F 1)

def b53 : Ambient F :=
  pure F (e F 0) (e F 3) (e F 5) + pure F (e F 0) (e F 5) (e F 3) + pure F (e F 5) (e F 0) (e F 3) + pure F (e F 5) (e F 3) (e F 0)

def b54 : Ambient F :=
  pure F (e F 1) (e F 3) (e F 5) + pure F (e F 1) (e F 5) (e F 3) + pure F (e F 5) (e F 1) (e F 3) + pure F (e F 5) (e F 3) (e F 1)

def b55 : Ambient F :=
  pure F (e F 0) (e F 4) (e F 5) + pure F (e F 0) (e F 5) (e F 4) + pure F (e F 5) (e F 0) (e F 4) + pure F (e F 5) (e F 4) (e F 0)

def b56 : Ambient F :=
  pure F (e F 1) (e F 4) (e F 5) + pure F (e F 1) (e F 5) (e F 4) + pure F (e F 2) (e F 3) (e F 5) + pure F (e F 2) (e F 5) (e F 3) + pure F (e F 5) (e F 1) (e F 4) + pure F (e F 5) (e F 2) (e F 3) + pure F (e F 5) (e F 3) (e F 2) + pure F (e F 5) (e F 4) (e F 1)

def b57 : Ambient F :=
  pure F (e F 2) (e F 4) (e F 5) + pure F (e F 2) (e F 5) (e F 4) + pure F (e F 5) (e F 2) (e F 4) + pure F (e F 5) (e F 4) (e F 2)

def b58 : Ambient F :=
  pure F (e F 3) (e F 4) (e F 5) + pure F (e F 3) (e F 5) (e F 4) + pure F (e F 5) (e F 3) (e F 4) + pure F (e F 5) (e F 4) (e F 3)

def b59 : Ambient F :=
  pure F (e F 2) (e F 3) (e F 5) + pure F (e F 2) (e F 5) (e F 3) + pure F (e F 5) (e F 0) (e F 5) + pure F (e F 5) (e F 2) (e F 3) + pure F (e F 5) (e F 3) (e F 2) + pure F (e F 5) (e F 5) (e F 0)

def b60 : Ambient F :=
  pure F (e F 5) (e F 1) (e F 5) + pure F (e F 5) (e F 5) (e F 1)

def b61 : Ambient F :=
  pure F (e F 5) (e F 2) (e F 5) + pure F (e F 5) (e F 5) (e F 2)

def b62 : Ambient F :=
  pure F (e F 5) (e F 3) (e F 5) + pure F (e F 5) (e F 5) (e F 3)

def b63 : Ambient F :=
  pure F (e F 5) (e F 4) (e F 5) + pure F (e F 5) (e F 5) (e F 4)

def generators : Fin 64 → Ambient F :=
  ![b0 F, b1 F, b2 F, b3 F, b4 F, b5 F, b6 F, b7 F, b8 F, b9 F, b10 F, b11 F, b12 F, b13 F, b14 F, b15 F, b16 F, b17 F, b18 F, b19 F, b20 F, b21 F, b22 F, b23 F, b24 F, b25 F, b26 F, b27 F, b28 F, b29 F, b30 F, b31 F, b32 F, b33 F, b34 F, b35 F, b36 F, b37 F, b38 F, b39 F, b40 F, b41 F, b42 F, b43 F, b44 F, b45 F, b46 F, b47 F, b48 F, b49 F, b50 F, b51 F, b52 F, b53 F, b54 F, b55 F, b56 F, b57 F, b58 F, b59 F, b60 F, b61 F, b62 F, b63 F]

def sparseSpan : Submodule F (Ambient F) :=
  Submodule.span F (Set.range (generators F))

omit [CharP F 2] in
theorem generator_mem (i : Fin 64) : generators F i ∈ sparseSpan F :=
  Submodule.subset_span ⟨i, rfl⟩

theorem rootA_e (a : F) (i : Fin 6) :
    NaturalCoordinates.action F (rootA a) (e F i) =
      ![e F 0, e F 1, e F 2, e F 3, e F 4 + a • e F 0, e F 5 + a • e F 1] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem rootB_e (a : F) (i : Fin 6) :
    NaturalCoordinates.action F (rootB a) (e F i) =
      ![e F 0, e F 1, e F 2, e F 3 + a • e F 0, e F 4, e F 5 + a • e F 2] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem rootC_e (a : F) (i : Fin 6) :
    NaturalCoordinates.action F (rootC a) (e F i) =
      ![e F 0, e F 1, e F 2, e F 3 + a • e F 1, e F 4 + a • e F 2, e F 5 + a^2 • e F 0] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem rootD_e (a : F) (i : Fin 6) :
    NaturalCoordinates.action F (rootD a) (e F i) =
      ![e F 0, e F 1, e F 2 + a • e F 0, e F 3, e F 4 + a^2 • e F 1, e F 5 + a • e F 3] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem rootE_e (a : F) (i : Fin 6) :
    NaturalCoordinates.action F (rootE a) (e F i) =
      ![e F 0, e F 1, e F 2 + a • e F 1, e F 3, e F 4 + a • e F 3, e F 5] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem rootF_e (a : F) (i : Fin 6) :
    NaturalCoordinates.action F (rootF a) (e F i) =
      ![e F 0, e F 1 + a • e F 0, e F 2, e F 3 + a^2 • e F 2, e F 4, e F 5 + a • e F 4] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem weylR_e (i : Fin 6) :
    NaturalCoordinates.action F weylR (e F i) =
      ![e F 0, e F 2, e F 1, e F 4, e F 3, e F 5] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem weylS_e (i : Fin 6) :
    NaturalCoordinates.action F weylS (e F i) =
      ![e F 1, e F 0, e F 3, e F 2, e F 5, e F 4] i := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp [e]

theorem cast2 : (2 : F) = 0 := by
  simpa using (CharP.cast_eq_mod F 2 2)

theorem cast3 : (3 : F) = 1 := by
  simpa using (CharP.cast_eq_mod F 2 3)

theorem cast4 : (4 : F) = 0 := by
  simpa using (CharP.cast_eq_mod F 2 4)

theorem cast5 : (5 : F) = 1 := by
  simpa using (CharP.cast_eq_mod F 2 5)

theorem cast6 : (6 : F) = 0 := by
  simpa using (CharP.cast_eq_mod F 2 6)

theorem cast7 : (7 : F) = 1 := by
  simpa using (CharP.cast_eq_mod F 2 7)

theorem cast8 : (8 : F) = 0 := by
  simpa using (CharP.cast_eq_mod F 2 8)

theorem rootA_e0 (a : F) : NaturalCoordinates.action F (rootA a) (e F 0) =
    e F 0 := rootA_e F a 0

theorem rootA_e1 (a : F) : NaturalCoordinates.action F (rootA a) (e F 1) =
    e F 1 := rootA_e F a 1

theorem rootA_e2 (a : F) : NaturalCoordinates.action F (rootA a) (e F 2) =
    e F 2 := rootA_e F a 2

theorem rootA_e3 (a : F) : NaturalCoordinates.action F (rootA a) (e F 3) =
    e F 3 := rootA_e F a 3

theorem rootA_e4 (a : F) : NaturalCoordinates.action F (rootA a) (e F 4) =
    e F 4 + a • e F 0 := rootA_e F a 4

theorem rootA_e5 (a : F) : NaturalCoordinates.action F (rootA a) (e F 5) =
    e F 5 + a • e F 1 := rootA_e F a 5

theorem rootB_e0 (a : F) : NaturalCoordinates.action F (rootB a) (e F 0) =
    e F 0 := rootB_e F a 0

theorem rootB_e1 (a : F) : NaturalCoordinates.action F (rootB a) (e F 1) =
    e F 1 := rootB_e F a 1

theorem rootB_e2 (a : F) : NaturalCoordinates.action F (rootB a) (e F 2) =
    e F 2 := rootB_e F a 2

theorem rootB_e3 (a : F) : NaturalCoordinates.action F (rootB a) (e F 3) =
    e F 3 + a • e F 0 := rootB_e F a 3

theorem rootB_e4 (a : F) : NaturalCoordinates.action F (rootB a) (e F 4) =
    e F 4 := rootB_e F a 4

theorem rootB_e5 (a : F) : NaturalCoordinates.action F (rootB a) (e F 5) =
    e F 5 + a • e F 2 := rootB_e F a 5

theorem rootC_e0 (a : F) : NaturalCoordinates.action F (rootC a) (e F 0) =
    e F 0 := rootC_e F a 0

theorem rootC_e1 (a : F) : NaturalCoordinates.action F (rootC a) (e F 1) =
    e F 1 := rootC_e F a 1

theorem rootC_e2 (a : F) : NaturalCoordinates.action F (rootC a) (e F 2) =
    e F 2 := rootC_e F a 2

theorem rootC_e3 (a : F) : NaturalCoordinates.action F (rootC a) (e F 3) =
    e F 3 + a • e F 1 := rootC_e F a 3

theorem rootC_e4 (a : F) : NaturalCoordinates.action F (rootC a) (e F 4) =
    e F 4 + a • e F 2 := rootC_e F a 4

theorem rootC_e5 (a : F) : NaturalCoordinates.action F (rootC a) (e F 5) =
    e F 5 + a^2 • e F 0 := rootC_e F a 5

theorem rootD_e0 (a : F) : NaturalCoordinates.action F (rootD a) (e F 0) =
    e F 0 := rootD_e F a 0

theorem rootD_e1 (a : F) : NaturalCoordinates.action F (rootD a) (e F 1) =
    e F 1 := rootD_e F a 1

theorem rootD_e2 (a : F) : NaturalCoordinates.action F (rootD a) (e F 2) =
    e F 2 + a • e F 0 := rootD_e F a 2

theorem rootD_e3 (a : F) : NaturalCoordinates.action F (rootD a) (e F 3) =
    e F 3 := rootD_e F a 3

theorem rootD_e4 (a : F) : NaturalCoordinates.action F (rootD a) (e F 4) =
    e F 4 + a^2 • e F 1 := rootD_e F a 4

theorem rootD_e5 (a : F) : NaturalCoordinates.action F (rootD a) (e F 5) =
    e F 5 + a • e F 3 := rootD_e F a 5

theorem rootE_e0 (a : F) : NaturalCoordinates.action F (rootE a) (e F 0) =
    e F 0 := rootE_e F a 0

theorem rootE_e1 (a : F) : NaturalCoordinates.action F (rootE a) (e F 1) =
    e F 1 := rootE_e F a 1

theorem rootE_e2 (a : F) : NaturalCoordinates.action F (rootE a) (e F 2) =
    e F 2 + a • e F 1 := rootE_e F a 2

theorem rootE_e3 (a : F) : NaturalCoordinates.action F (rootE a) (e F 3) =
    e F 3 := rootE_e F a 3

theorem rootE_e4 (a : F) : NaturalCoordinates.action F (rootE a) (e F 4) =
    e F 4 + a • e F 3 := rootE_e F a 4

theorem rootE_e5 (a : F) : NaturalCoordinates.action F (rootE a) (e F 5) =
    e F 5 := rootE_e F a 5

theorem rootF_e0 (a : F) : NaturalCoordinates.action F (rootF a) (e F 0) =
    e F 0 := rootF_e F a 0

theorem rootF_e1 (a : F) : NaturalCoordinates.action F (rootF a) (e F 1) =
    e F 1 + a • e F 0 := rootF_e F a 1

theorem rootF_e2 (a : F) : NaturalCoordinates.action F (rootF a) (e F 2) =
    e F 2 := rootF_e F a 2

theorem rootF_e3 (a : F) : NaturalCoordinates.action F (rootF a) (e F 3) =
    e F 3 + a^2 • e F 2 := rootF_e F a 3

theorem rootF_e4 (a : F) : NaturalCoordinates.action F (rootF a) (e F 4) =
    e F 4 := rootF_e F a 4

theorem rootF_e5 (a : F) : NaturalCoordinates.action F (rootF a) (e F 5) =
    e F 5 + a • e F 4 := rootF_e F a 5

theorem weylR_e0 : NaturalCoordinates.action F weylR (e F 0) =
    e F 0 := weylR_e F 0

theorem weylR_e1 : NaturalCoordinates.action F weylR (e F 1) =
    e F 2 := weylR_e F 1

theorem weylR_e2 : NaturalCoordinates.action F weylR (e F 2) =
    e F 1 := weylR_e F 2

theorem weylR_e3 : NaturalCoordinates.action F weylR (e F 3) =
    e F 4 := weylR_e F 3

theorem weylR_e4 : NaturalCoordinates.action F weylR (e F 4) =
    e F 3 := weylR_e F 4

theorem weylR_e5 : NaturalCoordinates.action F weylR (e F 5) =
    e F 5 := weylR_e F 5

theorem weylS_e0 : NaturalCoordinates.action F weylS (e F 0) =
    e F 1 := weylS_e F 0

theorem weylS_e1 : NaturalCoordinates.action F weylS (e F 1) =
    e F 0 := weylS_e F 1

theorem weylS_e2 : NaturalCoordinates.action F weylS (e F 2) =
    e F 3 := weylS_e F 2

theorem weylS_e3 : NaturalCoordinates.action F weylS (e F 3) =
    e F 2 := weylS_e F 3

theorem weylS_e4 : NaturalCoordinates.action F weylS (e F 4) =
    e F 5 := weylS_e F 4

theorem weylS_e5 : NaturalCoordinates.action F weylS (e F 5) =
    e F 4 := weylS_e F 5

/-- A linear operator preserving every displayed generator preserves its span. -/
theorem preserves_of_generators (g : Model F)
    (h : ∀ i, ambientAction F g (generators F i) ∈ sparseSpan F) :
    ∀ v ∈ sparseSpan F, ambientAction F g v ∈ sparseSpan F := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨i, rfl⟩ := hv; exact h i
  | zero => simpa only [map_zero (ambientAction F g)] using (sparseSpan F).zero_mem
  | add v w _ _ hv hw =>
    simpa only [map_add (ambientAction F g) v w] using (sparseSpan F).add_mem hv hw
  | smul a v _ hv =>
    simpa only [map_smul (ambientAction F g) a v] using (sparseSpan F).smul_mem a hv

end Atlas.G2.Restricted.Steinberg.OrbitClosure
