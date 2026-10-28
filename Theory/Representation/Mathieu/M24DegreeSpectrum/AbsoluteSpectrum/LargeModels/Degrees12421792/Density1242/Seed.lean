module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Fixed witnesses for the degree-1242 density calculation

The algebra element is `1 + A + B + B * A * B` in the untransposed ATLAS
matrices. The proposed column and row are packed binary vectors, with bit j at
coordinate j. These definitions assert no kernel, invertibility, or spanning
property. The independent certificate modules must establish those identities.

Source data: ATLAS `M24G1-f2r1242B0.m1/.m2`, preserved in
`../source/README.md`; application: James, J. Algebra 27 (1973), 57–111.
The reproducible, untrusted witness search is `source/discover.py`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242

abbrev Mat := Matrix (Fin 1242) (Fin 1242) (ZMod 2)

def wordValue {M : Type*} [Monoid M] (a b : M) (w : List Bool) : M :=
  (w.map fun s => if s then b else a).prod

theorem wordValue_mem {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R]
    (Q : Subalgebra k R) (a b : R) (ha : a ∈ Q) (hb : b ∈ Q) (w : List Bool) :
    wordValue a b w ∈ Q := by
  induction w with
  | nil => exact Q.one_mem
  | cons s w ih =>
    change (if s then b else a) * wordValue a b w ∈ Q
    apply Q.mul_mem _ ih
    cases s
    · exact ha
    · exact hb

/-- The exact short algebra expression found by the deterministic search. -/
def algebraElement : Mat :=
  1 + Data1242.first + Data1242.second + Data1242.second * Data1242.first * Data1242.second

theorem algebraElement_mem (Q : Subalgebra (ZMod 2) Mat)
    (ha : Data1242.first ∈ Q) (hb : Data1242.second ∈ Q) : algebraElement ∈ Q := by
  exact Q.add_mem (Q.add_mem (Q.add_mem Q.one_mem ha) hb) (Q.mul_mem (Q.mul_mem hb ha) hb)

def columnPacked : ℕ := 17037147507604636086766699703173503952498802011187558056834492729690083752681160731249399603659372424074460796681808481330099558042600267893168165013188002858059780241075376854288628127791151341125801981796757402910371902471771947207556756017224811088620939545456810902215712038279694773317960998410789518060459989063466865723089193002593675073422645579104866295470337427611

def rowPacked : ℕ := 21061692580008197485671482781253269300160455820308436690828959289225609640090201501167618546394048041350472433098902470439030123705204039418390546984429072249119297153232751869118711706317614914655756733213772058129032621621551261723462555011915311208797692733793051407545505531364154346965709100494091352198521838989142168372764860285265612125450399831198740436142717491119

def column : Fin 1242 → ZMod 2 := fun i => Thompson.BinaryMatrix.bit columnPacked i.val

def row : Fin 1242 → ZMod 2 := fun i => Thompson.BinaryMatrix.bit rowPacked i.val

/-- Left translates use the original matrices acting on columns. -/
def columnOrbit (w : List Bool) : Fin 1242 → ZMod 2 :=
  (wordValue Data1242.first Data1242.second w).mulVec column

/-- Right translates use the original ATLAS row convention. -/
def rowOrbit (w : List Bool) : Fin 1242 → ZMod 2 :=
  Matrix.vecMul row (wordValue Data1242.first Data1242.second w)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242
