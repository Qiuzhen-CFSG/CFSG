module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts

/-!
# Local obligations in the block inspection for E.6.23

The three obligations separate construction of an overgroup from inspection
of its block and ordinary-component alternatives. They are unproved contracts,
not earlier-source theorems. The lifting obligation includes the solvable A₃
case, to which the perfect C-component family and 1.2.4 do not apply directly.

C.1.9 is retained with its precise extra hypothesis on O₂,₃, the preimage
of O₃ modulo O₂. No persistence or unconditional block commutation is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.9,
printed p.123; E.6.23, printed pp.254–255 (PDF pp.265–266).
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
open ComponentBalance

variable {G : Type*} [Group G]

/-- A genuine block of the indicated centralizer, with its inclusion. -/
def CentralizerBlock (A X : Subgroup G) : Prop :=
  X ≤ centralizer (A : Set G) ∧ ChapterC.IsBlock (X.subgroupOf (centralizer (A : Set G)))

/-- The additional local condition in C.1.9, with the core series in order. -/
def C19Condition (H : Type*) [Group H] : Prop :=
  let N := (pCore 3 (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))
  generalizedFitting N = pCore 2 N

/-- Exact C.1.9, restricted to the overgroups in the given ambient group. -/
def BlockCommutationInput (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G,
    ((∃ J : Subgroup H, ChapterC.IsBlock J ∧ ChapterC.IsAlternatingBlock J 3) →
      C19Condition H) →
    ∀ B D : Subgroup H, ChapterC.IsBlock B → ChapterC.IsBlock D →
      B ≠ D → ⁅B, D⁆ = ⊥

/-- Construct an actual overgroup before inspecting either of its two kinds. -/
def CorankTwoLifting (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∃ X : Subgroup G, L ≤ X ∧
          ((CentralizerBlock A X ∧ ChapterC.IsChiZeroBlock X) ∨ CentralizerComponent A X)

/-- Exclude a proper chi-zero block overgroup using its actual natural module. -/
def ProperBlockExclusion (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, L < X → CentralizerBlock A X →
          ChapterC.IsChiZeroBlock X → False

/-- Inspect an ordinary component overgroup, constructing every A₆ clause. -/
def ProperComponentInspection (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, L < X → CentralizerComponent A X →
          ProperSixEnlargement V U A L X

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
