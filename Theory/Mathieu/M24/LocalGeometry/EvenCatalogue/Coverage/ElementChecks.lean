module

public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage.ElementData

/-!
# Kernel checks for the M₂₄ catalogue: ElementChecks

Products of conjugates exclude all other elements, and recover catalogue generators for every surviving element.
All computations use the certified enumeration of the actual Sylow carrier.
See `source/README.md` for the mathematical argument and reproduction command.
Source context: Aschbacher–Smith, printed pp.3–4; GLS3, Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
open SylowNormalizer OrderEnumeration
set_option maxRecDepth 100000

theorem rejection_check : ∀ i : Fin 1024,
    i = 0 ∨ i = goodIndex (goodCode i) ∨
    multiply (normalProduct i (rejectionWord i)) (normalProduct i (rejectionWord i)) ≠ 0 := by
  decide +kernel

theorem upper_check : ∀ j : Fin 143,
    product (generatorIndex (closureRow j)) (upperWord j) = goodIndex j := by
  decide +kernel

theorem lower_check : ∀ (j : Fin 143) (a : Fin 6),
    normalProduct (goodIndex j) (lowerWord j a) = generatorIndex (closureRow j) a := by
  decide +kernel


end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
