module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.OrthogonalNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The literal two-component conclusions of G.9.3

Alternative (14) uses the natural matrix action of the actual central
quotient PSL₃(2), transported through its proved identification with GL₃(2),
and the external tensor action on the nine-dimensional binary space.
Alternative (15) uses the defining quadratic-isometry action of the genuine
elementary split orthogonal group Ω₄⁺(2ⁿ). The group and module comparisons
in `Conclusion` are linked by quasiequivalence, not by family names or orders.

These are output definitions; their existence from the source hypotheses
remains to be proved. The rank and degree conditions retain the original
actor. Source: Aschbacher--Smith, G.9.3(14),(15), printed p.354.
-/

@[expose] public noncomputable section

open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

abbrev ThreeGroup := PSL(3, ZMod 2)
abbrev ThreeSpace := Fin 3 → ZMod 2

/-- The usual three-dimensional PSL₃(2) action, including the actual
identification of its scalar quotient with binary invertible matrices. -/
def threeNatural : Representation (ZMod 2) ThreeGroup ThreeSpace where
  toFun g := (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) g).toLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

/-- The natural external tensor product for the two PSL₃(2) factors. -/
def threeTensor : Representation (ZMod 2) (ThreeGroup × ThreeGroup)
    (ThreeSpace ⊗[ZMod 2] ThreeSpace) where
  toFun g := TensorProduct.map (threeNatural g.1) (threeNatural g.2)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Module.End.mul_eq_comp, TensorProduct.map_comp]

/-- The orthogonal action preserves the explicit split quadratic form,
before scalar restriction to the binary field. -/
def fourOrthogonal (n : ℕ) : Representation (ZMod 2)
    (ClassicalOrthogonal.OmegaPlus 2 (GaloisField 2 n))
    (ClassicalOrthogonal.VectorD 2 (GaloisField 2 n)) :=
  Representation.restrictScalars
    (ClassicalOrthogonal.subgroupNatural (ClassicalOrthogonal.OmegaPlus 2 (GaloisField 2 n)))

theorem threeTensor_degree :
    Module.finrank (ZMod 2) (ThreeSpace ⊗[ZMod 2] ThreeSpace) = 9 := by
  simp [Module.finrank_tensorProduct, ThreeSpace]

theorem fourOrthogonal_degree {n : ℕ} (hn : 0 < n) :
    Module.finrank (ZMod 2) (ClassicalOrthogonal.VectorD 2 (GaloisField 2 n)) = 4 * n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (GaloisField 2 n)
    (ClassicalOrthogonal.VectorD 2 (GaloisField 2 n)),
    GaloisField.finrank 2 hn.ne', ClassicalOrthogonal.vectorD_finrank]
  omega

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The exact two-component alternatives, with `G` in (14) and `H` in (15).
Each group equivalence is part of an equivariant linear identification. -/
def Conclusion (ρ : Representation (ZMod 2) G V) (H : Subgroup G) (m : ℕ) : Prop :=
  (Quasiequivalent ρ threeTensor ∧ Module.finrank (ZMod 2) V = 9 ∧ m = 4) ∨
    ∃ n : ℕ, 1 < n ∧ Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal n) ∧
      Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n - 1 ≤ m

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
