module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.FoldedRoots
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.FixedWords

/-!
# Actual Levi torus actors for the radical calculation

Use the already proved pinned SL₂ six-root words. Their split images are
h₀(t)h₂(F(t))h₃(F²(t)) on the arms, and h₁(t) on the central vertex.
Each word lies in the root-generated subsystem Levi. Thus its existing
elementary lift descends to the exact Levi subgroup of the task, without
enlarging that subgroup by the full Cartan torus.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`). The convention
is left conjugation by n(t)n(-1), as verified by the pinned matrix maps in
`ConcreteBruhat.Torus.FixedWords`.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Parabolics ConcreteBruhat TorusCoordinates

/-- The actual elementary lift supplied by the pinned rank-one maps. -/
abbrev torusElementary (P : Parameters) (hp : P.prime = 2) (a : Node)
    (t : (RootField P a)ˣ) : ElementaryGroup P := foldedTorusElementary P hp a t

def torusActor (P : Parameters) (hp : P.prime = 2) (a : Node)
    (t : (RootField P a)ˣ) : Carrier P := toCarrier P (torusElementary P hp a t)

theorem torusElementary_arms_val (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) :
    elementaryInclusion P (torusElementary P hp .arms t) =
      torusWord P 0 t * torusWord P 2 (frobenius P t) *
        torusWord P 3 (frobenius P (frobenius P t)) :=
  inclusion_foldedTorus_arms P hp t

theorem torusElementary_central_val (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) :
    elementaryInclusion P (torusElementary P hp .central t) =
      torusWord P 1 (fixedUnit P t) := inclusion_foldedTorus_central P hp t

private theorem torusWord_mem (P : Parameters) (a : Node) (i : Fin 4)
    (hi : i ∈ a.support) (t : (ExtensionField P)ˣ) :
    torusWord P i t ∈ splitLevi P a := by
  have hw (u : ExtensionField P) : weylWord P i u ∈ splitLevi P a := by
    have hpos (v : ExtensionField P) : positiveRoot P i v ∈ splitLevi P a :=
      Subgroup.subset_closure ⟨i, hi, v, Or.inl rfl⟩
    have hneg (v : ExtensionField P) : negativeRoot P i v ∈ splitLevi P a :=
      Subgroup.subset_closure ⟨i, hi, v, Or.inr rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hpos u) (hneg _)) (hpos u)
  exact Subgroup.mul_mem _ (hw _) (hw _)

/-- The actors belong to the subsystem Levi, including at q = 2. -/
theorem torusActor_mem_levi (P : Parameters) (hp : P.prime = 2) (a : Node)
    (t : (RootField P a)ˣ) : torusActor P hp a t ∈ levi P a := by
  refine ⟨torusElementary P hp a t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ splitLevi P a
  cases a with
  | arms =>
    rw [torusElementary_arms_val]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (torusWord_mem P .arms 0 (by decide : (0 : Fin 4) ≠ 1) _)
      (torusWord_mem P .arms 2 (by decide : (2 : Fin 4) ≠ 1) _))
      (torusWord_mem P .arms 3 (by decide : (3 : Fin 4) ≠ 1) _)
  | central =>
    rw [torusElementary_central_val]
    exact torusWord_mem P .central 1 rfl _

end Triality.Standard.RadicalCoordinates.LeviCommutators
