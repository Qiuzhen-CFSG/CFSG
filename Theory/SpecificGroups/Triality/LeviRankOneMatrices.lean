module
public import Theory.SpecificGroups.Triality.LeviRankOne
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Comparison

/-!
# From the explicit D4 matrix action to pinned rank-one maps

The explicit matrix representation acts on the full Geck lattice and is faithful
on each natural root-string block. Its proved transvection formulas agree with
the integral Geck curves. Transvection generation therefore puts its entire image
inside the split D4 group and supplies the published pinned-map interface in
characteristic two, including the smallest field.

Source: GLS3 §§2.4 and 2.6, especially Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
namespace Triality.Standard.Parabolics

/-- The characteristic-two instance supplied by the source parameter. -/
theorem rankOneExtensionCharTwo (P : Parameters) (hp : P.prime = 2) :
    CharP (ExtensionField P) 2 := by
  rw [← hp]
  infer_instance

/-- Restrict the constructed faithful matrix action to the genuine split group
using only the two explicit curve comparisons. This is conditional assembly;
the integral matrix comparison must be proved to obtain the source maps. -/
def pinnedRankOneMapsOfCurveComparison (P : Parameters) (hp : P.prime = 2)
    (C : letI := rankOneExtensionCharTwo P hp
      RankOneMatrices.CurveComparison (F := ExtensionField P)) : PinnedRankOneMaps P := by
  letI := rankOneExtensionCharTwo P hp
  have hmem (i : Fin 4) (A : SL(2, ExtensionField P)) :
      RankOneMatrices.ambientHom i A ∈ subgroup (typeDRootPairing_base 2) (ExtensionField P) := by
    apply sl2_root_induction (fun A => RankOneMatrices.ambientHom i A ∈
      subgroup (typeDRootPairing_base 2) (ExtensionField P)) ?_ ?_ ?_ A
    · intro t
      rw [C.positive]
      exact positiveUnit_mem _ _
    · intro t
      rw [C.negative]
      exact negativeUnit_mem _ _
    · intro A B hA hB
      simpa only [map_mul] using Subgroup.mul_mem _ hA hB
  let f (i : Fin 4) : SL(2, ExtensionField P) →* SplitGroup P :=
    (RankOneMatrices.ambientHom i).codRestrict _ (hmem i)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i A B h
    exact RankOneMatrices.ambientHom_injective i (congrArg Subtype.val h)
  · intro i t
    exact Subtype.ext (C.positive i t)
  · intro i t
    exact Subtype.ext (C.negative i t)

/-- The faithful pinned SL₂ maps at all four simple roots of the genuine split
D4 group in characteristic two. Both pinning formulas are proved by the integral
matrix calculation, with no representation or subsystem identification assumed. -/
def pinnedRankOneMaps (P : Parameters) (hp : P.prime = 2) : PinnedRankOneMaps P :=
  pinnedRankOneMapsOfCurveComparison P hp (by
    let := rankOneExtensionCharTwo P hp
    exact RankOneMatrices.curveComparison)

end Triality.Standard.Parabolics
