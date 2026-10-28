/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootCDCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormFiberCount
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootScalarFiberCounts

/-!
# Icosian Root CDCounts

The fixed-position root families with norms (1,1,2) and (1,τ²,σ²)
have sizes 7680 and 1920. The determinant-glue count is instantiated
with the proved scalar reduction-fiber sizes.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootCDCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra

def icosianRootCNorms : Fin 3 → GoldenInteger := ![1,1,2]
def icosianRootDNorms : Fin 3 → GoldenInteger :=
  ![1,QuadraticAlgebra.omega^2,(1-QuadraticAlgebra.omega)^2]

abbrev IcosianRootCStandard :=
  IcosianRootsWithNorms (fun i => goldenIntegerToRational (icosianRootCNorms i))
abbrev IcosianRootDStandard :=
  IcosianRootsWithNorms (fun i => goldenIntegerToRational (icosianRootDNorms i))

/-- The fixed-position (1,1,2) family: 240 matrix-glue words, with scalar fibers2,2,8. -/
theorem icosianRootCStandard_card : Nat.card IcosianRootCStandard=7680 := by
  let n := fun i => goldenIntegerToRational (icosianRootCNorms i)
  let d := fun i => goldenModuloTwo (icosianRootCNorms i)
  let k : Fin 3 → ℕ := ![2,2,8]
  have hn : (∑ i,n i)=4 := by decide +kernel
  have hd0 : d 0+d 1+d 2=0 := by decide +kernel
  have hne : ∃ i,d i≠0 := ⟨0,by decide +kernel⟩
  have hf : ∀ i (m : IcosianMatrix),Matrix.det m=d i → m≠0 →
      Nat.card (IcosianScalarNormReductionFiber (n i) m)=k i := by
    intro i m hm hm0
    fin_cases i
    · exact icosianScalarNorm_one_fiber_card m hm
    · exact icosianScalarNorm_one_fiber_card m hm
    · exact icosianScalarNorm_two_fiber_card m hm hm0
  have h := icosianRootsWithNorms_card n d k hn hd0
    (fun i x hx => icosianNorm_det_of_integral_value _ x hx) hne (by decide +kernel) hf
  convert h using 1; norm_num [k,Fin.prod_univ_succ]

/-- The fixed-position (1,τ²,σ²) family: 240 matrix-glue words, with three scalar fibers2. -/
theorem icosianRootDStandard_card : Nat.card IcosianRootDStandard=1920 := by
  let n := fun i => goldenIntegerToRational (icosianRootDNorms i)
  let d := fun i => goldenModuloTwo (icosianRootDNorms i)
  let k : Fin 3 → ℕ := ![2,2,2]
  have hn : (∑ i,n i)=4 := by decide +kernel
  have hd0 : d 0+d 1+d 2=0 := by decide +kernel
  have hne : ∃ i,d i≠0 := ⟨0,by decide +kernel⟩
  have hf : ∀ i (m : IcosianMatrix),Matrix.det m=d i → m≠0 →
      Nat.card (IcosianScalarNormReductionFiber (n i) m)=k i := by
    intro i m hm hm0
    fin_cases i
    · exact icosianScalarNorm_one_fiber_card m hm
    · have he : n 1=goldenTau^2 := by decide +kernel
      change Nat.card (IcosianScalarNormReductionFiber (n 1) m)=2
      rw [he]
      exact icosianScalarNorm_tau_fiber_card m hm
    · have he : n 2=goldenSigma^2 := by decide +kernel
      change Nat.card (IcosianScalarNormReductionFiber (n 2) m)=2
      rw [he]
      exact icosianScalarNorm_sigma_fiber_card m hm
  have h := icosianRootsWithNorms_card n d k hn hd0
    (fun i x hx => icosianNorm_det_of_integral_value _ x hx) hne (by decide +kernel) hf
  convert h using 1; norm_num [k,Fin.prod_univ_succ]

end Atlas.Lattices
