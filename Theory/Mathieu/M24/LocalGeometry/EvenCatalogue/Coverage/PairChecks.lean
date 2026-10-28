module

public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage.PairData

/-!
# Kernel checks for the M₂₄ catalogue: PairChecks

Generator words certify containment or enlargement for each pair of rows; incompatible pairs have a product with nonidentity square.
All computations use the certified enumeration of the actual Sylow carrier.
See `source/README.md` for the mathematical argument and reproduction command.
Source context: Aschbacher–Smith, printed pp.3–4; GLS3, Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
open SylowNormalizer OrderEnumeration
set_option maxRecDepth 100000

theorem pair_check : ∀ (i j : Fin 22), j ≤ i →
    (pairMode i j = 0 ∧ ∀ a : Fin 6,
      product (joinedGenerator i i) (pairWord i j a) = generatorIndex j a) ∨
    (i < pairTarget i j ∧ ∀ a : Fin 6,
      product (joinedGenerator i j) (pairWord i j a) = generatorIndex (pairTarget i j) a) ∨
    multiply (badPairProduct i j) (badPairProduct i j) ≠ 0 := by
  decide +kernel

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
