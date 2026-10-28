/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonForwardChecks.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonGeneratorsData
public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonSpace
public import Theory.AtlasPort.Janko2.Codes.TernaryBinaryComparisonData

/-!
# Icosian Comparison Forward Checks

The 36 integral source generators map into the Golay Leech lattice.
Kernel-checked coordinate arithmetic verifies their images, parity,
binary Golay residues, and coordinate-sum congruences.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonForwardChecks.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix BigOperators

def icosianComparisonImageData : Matrix (Fin 36) (Fin 24) ℤ :=
![![4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,4,-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![4,-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![4,0,0,0,0,-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![-2,2,2,-2,2,-2,-2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,-4,0,-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![2,2,-2,-2,2,2,-2,-2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,4,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,-4,0,0,0],
![0,0,0,0,0,0,0,0,4,0,0,0,0,0,-4,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,4,0,0],
![0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,-4,0,0,0,0],
![0,0,0,0,0,0,0,0,-2,2,0,0,0,0,2,-2,0,0,2,-2,-2,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,-4,0,0,0,0,0,-4,0,0,0],
![0,0,0,0,0,0,0,0,2,-2,0,0,0,0,2,-2,0,0,-2,2,-2,2,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,4],
![0,0,0,0,0,0,0,0,0,0,-4,0,4,0,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-4,0,0,0,0,0,4],
![0,0,0,0,0,0,0,0,0,0,0,4,0,4,0,0,0,0,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,0,0,0,-4,0,0,0,0,0,0,0,0,0,4],
![0,0,0,0,0,0,0,0,0,0,-2,2,2,-2,0,0,-2,2,0,0,0,0,2,-2],
![0,0,0,0,0,0,0,0,0,0,-4,0,0,0,0,0,0,-4,0,0,0,0,0,0],
![0,0,0,0,0,0,0,0,0,0,-2,2,-2,2,0,0,-2,2,0,0,0,0,-2,2],
![4,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
![0,0,2,-2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,2,2,-2,2,0,0],
![2,-2,0,-2,0,-2,0,0,2,0,0,0,0,0,-2,0,0,0,0,-2,-2,0,0,0],
![0,2,0,-2,2,0,-2,0,0,0,0,0,0,0,2,-2,0,0,0,0,-2,2,0,0],
![4,-2,2,-6,4,0,-2,0,2,0,0,0,0,0,2,0,0,2,0,0,0,0,0,2],
![6,-2,2,-4,0,-2,0,0,0,0,-2,0,2,0,0,0,0,0,2,0,-2,0,0,0],
![4,2,2,-6,4,0,-2,0,2,0,0,0,0,0,2,0,0,-2,0,0,0,0,0,2],
![6,-2,0,-2,2,0,0,0,0,0,0,2,0,2,0,0,0,0,2,0,-2,0,0,0],
![6,0,2,-2,2,0,0,0,2,0,0,0,0,-2,0,0,0,0,0,-2,0,0,0,2],
![3,1,1,-1,1,-1,-1,1,-1,1,-1,1,1,-1,1,-1,-1,1,1,-1,-1,1,1,-1],
![4,-2,2,-4,2,2,0,0,2,0,-2,0,0,0,0,0,0,-2,0,-2,0,0,0,0],
![5,1,-1,-1,1,1,-1,-1,-1,1,-1,1,-1,1,1,-1,-1,1,1,-1,-1,1,-1,1]]

def icosianComparisonIntegerImage (j : Fin 36) : IntegerCoordinates :=
  fun p => icosianComparisonImageData j (icosianLeechCoordinateIndex p)

def icosianComparisonMask : Fin 36 → ℕ := ![0,0,0,0,0,64,0,64,0,0,0,0,0,1176,0,1176,0,0,0,0,0,792,0,792,0,1104,3954,1113,2919,3824,2919,4024,2844,1687,240,1934]

theorem icosianComparison_forward_arithmetic : ∀ j : Fin 36,
    let x := icosianComparisonIntegerImage j
    let m := x ((0,0),0) % 2
    icosianComparisonMatrix *ᵥ icosianRealCoordinates
      (icosianCoordinateEmbedding (icosianComparisonSourceGenerator j)) =
      rationalEmbedding x ∧
    (m=0 ∨ m=1) ∧ (∀ p, x p % 2=m) ∧
    halfResidue x m = comparisonBinaryCoefficients (icosianComparisonMask j) ∧
    (∑ p, x p) % 8 = 4*m := by
  decide +kernel

theorem icosianComparison_generator_check (j : Fin 36) :
    ∃ x : IntegerCoordinates, x ∈ leech ∧
      icosianComparison (icosianCoordinateEmbedding (icosianComparisonSourceGenerator j)) =
        rationalEmbedding x := by
  obtain ⟨he, hm, hp, hc, hs⟩ := icosianComparison_forward_arithmetic j
  refine ⟨_, (mem_leech _).mpr ⟨_, hm, hp, ?_, hs⟩, he⟩
  rw [hc]
  exact comparisonBinaryCoefficients_mem _

end Atlas.Lattices
