module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Contracts

/-!
# Local dimension obligations for higher binary SL₅ supports

Three conjugates of the standard graph operator generate a subgroup containing
the marked SL₅ image, as proved in `Higher.Generation`. Consequently a faithful
irreducible module of dimension at least 25 has graph displacement at least nine.

The two dimension estimates below remain obligations. They concern the original
binary local highest vectors, with no highest-weight comparison or extension of
scalars. The finite support calculation separates adjacent active roots from
the two separated pairs other than the endpoint pair. `Higher` applies both
estimates to the literal cyclic fixed-space contract.

This is an alternative reduction for Guralnick–Malle, *Classification of
2F-modules II*, Proposition 4.8(3B), author manuscript pp.27–28, used in
Aschbacher–Smith K.3.2, printed pp.454–455. It does not identify the source's
common fixed-space argument with a total-dimension bound.
-/

@[expose] public section

open Representation

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The outstanding dimension estimate when two adjacent roots are active. -/
def AdjacentDimensionBound
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    ∀ i ∈ J, ∀ j ∈ J, i.val + 1 = j.val → 25 ≤ Module.finrank (ZMod 2) V

/-- The outstanding dimension estimate for the two remaining separated pairs. -/
def SeparatedDimensionBound
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    (J = {0, 2} ∨ J = {1, 3}) → 25 ≤ Module.finrank (ZMod 2) V

/-- Every non-endpoint multiple support contains adjacent roots or is one of
the two separated pairs. No diagram-invariance assumption is needed. -/
theorem higher_support_cases (J : Finset (Fin 4)) (hcard : 2 ≤ J.card)
    (hne : J ≠ {0, 3}) :
    (∃ i ∈ J, ∃ j ∈ J, i.val + 1 = j.val) ∨ J = {0, 2} ∨ J = {1, 3} := by
  revert J
  decide +kernel

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
