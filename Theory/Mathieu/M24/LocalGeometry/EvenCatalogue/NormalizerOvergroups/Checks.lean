module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.Data
/-!
# Checked transitions of the 22 native catalogue rows

Each generator toggles one bit of a six-bit word. Three point images suffice
because the encompassing order-1024 enumeration has a certified three-point
base. The checks use direct point tables, avoiding nested multiplication-table
reduction. These are kernel checks of the actual native action.

Source: GLS3 Table 5.3e; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
open SylowNormalizer.OrderEnumeration
set_option maxRecDepth 100000
 theorem point_spec : ∀ c x, point c x = SylowNormalizer.OrderEnumeration.point (elementIndex c) x := by
  decide +kernel
 theorem generatorCode_spec : ∀ i a, elementIndex (generatorCode i a) = generatorIndex i a := by
  decide +kernel

def basePoint : Fin 3 → Fin 24 := ![0,1,5]
def toggle (a : Fin 6) (j : Fin 64) : Fin 64 :=
  ⟨(j.val ^^^ 2 ^ a.val) % 64, Nat.mod_lt _ (by decide)⟩
 theorem step_check : ∀ (i : Fin 22) (a : Fin 6) (j : Fin 64) (b : Fin 3),
    point (generatorCode i a) (point (rowCode i j) (basePoint b)) =
      point (rowCode i (toggle a j)) (basePoint b) := by
  intro i
  fin_cases i <;> decide +kernel
end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
