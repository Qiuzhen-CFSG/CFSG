module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Branches

/-!
# The two source branches for inner binary SL₅ actors

In Proposition 4.7, the two end-node parabolics reduce an offending highest
weight to support on the two endpoints. Lemma 4.5 then excludes that pair by
common-centralizer estimates. We state these as separate, unproved contracts
on the actual binary representation and its local highest vectors. In
particular, neither contract assumes absolute irreducibility or a degree bound.

The finite support calculation below exhausts all eleven multiple supports.
Deleting each endpoint leaves at most one root only for the pair `{0,3}`.
This separates the parabolic argument from the adjoint-module argument; the
latter cannot be replaced by an individual-involution displacement bound.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Lemma 4.5, pp.23–24, and Proposition 4.7, pp.25–26; Aschbacher–Smith K.3.2,
printed pp.454–455.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner

open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The two literal end-node restrictions of an offending support have at most
one active root. This is a producer contract, not an established estimate. -/
def EndNodeSieve (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ J.card → ∀ B : Subgroup SL5TenDimensional.Group,
    IsElementaryTwo B → IsCubic σ B → rank B ≤ 6 →
    fixedCodim σ B ≤ 2 * rank B →
    (J.erase 0).card ≤ 1 ∧ (J.erase 3).card ≤ 1

/-- The endpoint-pair common-fixed-space estimate, retaining the adjoint case.
Its independent producer must prove the estimate from faithful irreducibility. -/
def EndpointEstimate (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ v : V, v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ {0, 3} v →
    ∀ B : Subgroup SL5TenDimensional.Group,
    IsElementaryTwo B → IsCubic σ B → rank B ≤ 6 →
    2 * rank B < fixedCodim σ B

/-- The complete finite support list; no multiple-root branch is omitted. -/
theorem multiple_support_iff (J : Finset (Fin 4)) :
    2 ≤ J.card ↔
      J = {0, 1} ∨ J = {0, 2} ∨ J = {0, 3} ∨
      J = {1, 2} ∨ J = {1, 3} ∨ J = {2, 3} ∨
      J = {0, 1, 2} ∨ J = {0, 1, 3} ∨ J = {0, 2, 3} ∨
      J = {1, 2, 3} ∨ J = {0, 1, 2, 3} := by
  revert J
  decide +kernel

/-- The simultaneous end-node conditions eliminate ten of the eleven supports. -/
theorem endpoint_of_end_node_bounds (J : Finset (Fin 4)) (hJ : 2 ≤ J.card)
    (hzero : (J.erase 0).card ≤ 1) (hthree : (J.erase 3).card ≤ 1) :
    J = {0, 3} := by
  revert J
  decide +kernel

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner
