module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlane
public import Theory.LinearAlgebra.ReducedColumnBasis

/-!
# Certificates for the concrete Lyons plane orbit

A tree of column bases, whose edges are checked matrix identities, constructs
actual translates of the seven-dimensional plane. Distinct reduced column
bases have distinct ranges. Thus a tree with 8,835,156 nodes suffices without
any closure assertion, ambient order, or local subgroup identification.

The ATLAS generators and the root basis are those of `Atlas111LocalIndexPlane`.
The numerical tree and its arithmetic checks remain separate obligations;
this module proves the mathematical interpretation of such certificates.
-/

@[expose] public section
namespace Lyons.OrderCertificate
open Matrix
open scoped Pointwise

/-- A square coordinate change after a generator step identifies two column spaces.
The old columns' independence forces the coordinate change to be invertible. -/
theorem separation_smul_range_of_mul (g : LyonsGroup)
    (U V : Matrix (Fin 111) (Fin 7) (ZMod 5))
    (C : Matrix (Fin 7) (Fin 7) (ZMod 5))
    (hU : Function.Injective U.mulVec) (h : matrixRepresentation g * U = V * C) :
    g • Set.range U.mulVec = Set.range V.mulVec := by
  have hi : Function.Injective C.mulVec := by
    intro x y hxy
    apply hU
    apply MulAction.injective g
    change matrixRepresentation g *ᵥ (U *ᵥ x) = matrixRepresentation g *ᵥ (U *ᵥ y)
    rw [mulVec_mulVec, mulVec_mulVec, h, ← mulVec_mulVec, ← mulVec_mulVec, hxy]
  have hs := Finite.surjective_of_injective hi
  ext v
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨C *ᵥ x, ?_⟩
    change V *ᵥ (C *ᵥ x) = matrixRepresentation g *ᵥ (U *ᵥ x)
    rw [mulVec_mulVec, mulVec_mulVec, h]
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hs x
    refine ⟨U *ᵥ y, ⟨y, rfl⟩, ?_⟩
    change matrixRepresentation g *ᵥ (U *ᵥ y) = V *ᵥ x
    rw [mulVec_mulVec, h, ← mulVec_mulVec, hy]

/-- A finite matrix certificate for distinct reachable planes. -/
structure SeparationPlaneOrbitTree (n : ℕ) [NeZero n] where
  columns : Fin n → Matrix (Fin 111) (Fin 7) (ZMod 5)
  root_columns : columns 0 = separationPlaneColumns
  parent : Fin n → Fin n
  parent_lt : ∀ i, i ≠ 0 → parent i < i
  letter : Fin n → Bool
  coefficient : Fin n → Matrix (Fin 7) (Fin 7) (ZMod 5)
  edge : ∀ i, i ≠ 0 → matrixRepresentation (indexGenerator (letter i)) *
    columns (parent i) = columns i * coefficient i
  independent : ∀ i, Function.Injective (columns i).mulVec
  distinct : Function.Injective (fun i => Set.range (columns i).mulVec)

namespace SeparationPlaneOrbitTree
variable {n : ℕ} [NeZero n]

/-- Tree induction constructs actual representatives in the fixed matrix group. -/
theorem exists_representative (T : SeparationPlaneOrbitTree n) (i : Fin n) :
    ∃ g : LyonsGroup, g • separationPlane = Set.range (T.columns i).mulVec := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · subst i
      exact ⟨1, by rw [one_smul, T.root_columns]; rfl⟩
    · obtain ⟨g, hg⟩ := ih (T.parent i) (T.parent_lt i hi)
      refine ⟨indexGenerator (T.letter i) * g, ?_⟩
      rw [mul_smul, hg]
      exact separation_smul_range_of_mul _ _ _ _ (T.independent _) (T.edge i hi)

/-- Representatives can be chosen from the tree without evaluating long words. -/
noncomputable def repr (T : SeparationPlaneOrbitTree n) (i : Fin n) : LyonsGroup :=
  (T.exists_representative i).choose

theorem repr_smul (T : SeparationPlaneOrbitTree n) (i : Fin n) :
    T.repr i • separationPlane = Set.range (T.columns i).mulVec :=
  (T.exists_representative i).choose_spec

/-- Distinct node spaces certify distinct translates. -/
theorem repr_injective (T : SeparationPlaneOrbitTree n) :
    Function.Injective (fun i => T.repr i • separationPlane) := by
  intro i j h
  apply T.distinct
  simpa only [T.repr_smul] using h

/-- A tree's number of nodes is a lower bound for the actual plane orbit. -/
theorem le_orbit_ncard (T : SeparationPlaneOrbitTree n) :
    n ≤ (MulAction.orbit LyonsGroup separationPlane).ncard := by
  let f : Fin n → MulAction.orbit LyonsGroup separationPlane :=
    fun i => ⟨T.repr i • separationPlane, MulAction.mem_orbit separationPlane (T.repr i)⟩
  have hf : Function.Injective f := fun i j h => T.repr_injective (congrArg Subtype.val h)
  have : Finite (MulAction.orbit LyonsGroup separationPlane) :=
    (Finite.finite_mulAction_orbit separationPlane).to_subtype
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf
end SeparationPlaneOrbitTree

/-- Numerical matrix distinctness suffices when each column basis is reduced. -/
theorem separation_ranges_injective_of_reduced {ι : Type*}
    (U : ι → Matrix (Fin 111) (Fin 7) (ZMod 5))
    (hred : ∀ i, ReducedColumnBasis (U i)) (hinj : Function.Injective U) :
    Function.Injective (fun i => Set.range (U i).mulVec) := by
  let : Fact (1 < 5) := ⟨by decide⟩
  intro i j h
  exact hinj ((hred i).eq_of_range_eq (hred j) h)

/-- The numerical orbit target follows from the specified complete tree. -/
theorem le_separationPlane_orbit_of_tree (T : SeparationPlaneOrbitTree 8835156) :
    8835156 ≤ (MulAction.orbit LyonsGroup separationPlane).ncard := T.le_orbit_ncard
end Lyons.OrderCertificate
