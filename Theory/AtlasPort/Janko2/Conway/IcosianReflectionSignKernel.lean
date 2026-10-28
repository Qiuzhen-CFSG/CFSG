/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionSignKernel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisReflections
public import Theory.AtlasPort.Janko2.Conway.IcosianFullFrameStabilizer

/-!
# IcosianReflectionSignKernel

Coordinate reflections generate the independent sign changes. These formulas show the
whole monomial reduction kernel lies in the reflection subgroup.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionSignKernel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianReflectionSigns (b : Fin 3 → Bool) : icosianHermitianGroup :=
  (if b 0 then icosianAxisReflection 0 else 1)*
    (if b 1 then icosianAxisReflection 1 else 1)*
      (if b 2 then icosianAxisReflection 2 else 1)

theorem icosianReflectionSigns_mem (b : Fin 3 → Bool) :
    icosianReflectionSigns b∈icosianReflectionGroup := by
  apply icosianReflectionGroup.mul_mem
  · apply icosianReflectionGroup.mul_mem
    · split_ifs <;> first | exact icosianAxisReflection_mem _ | exact icosianReflectionGroup.one_mem
    · split_ifs <;> first | exact icosianAxisReflection_mem _ | exact icosianReflectionGroup.one_mem
  · split_ifs <;> first | exact icosianAxisReflection_mem _ | exact icosianReflectionGroup.one_mem

theorem icosianReflectionSigns_apply (b : Fin 3 → Bool)
    (x : IcosianRationalCoordinates) (i : Fin 3) :
    (icosianReflectionSigns b).val x i=if b i then -x i else x i := by
  unfold icosianReflectionSigns
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    fin_cases i <;>
    simp [h0,h1,h2,icosianAxisReflection_apply,LinearEquiv.mul_apply]

/-- All eight sign lifts in the full glue projection kernel are actual products
of the three axis reflections. -/
theorem icosianMonomial_kernel_mem_reflections (g : icosianLiftedMonomial)
    (hg : icosianMonomialReduction g.val=1) :
    icosianMonomialToHermitian g∈icosianReflectionGroup := by
  obtain ⟨hu,hp⟩ := (icosianMonomialReduction_kernel_iff g.val).mp hg
  have hb (i : Fin 3) : ∃ b : Bool,
      (g.val.left i).val.val=if b then -1 else 1 := by
    rcases icosianNormOneReduction_kernel_values (g.val.left i) (hu i) with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose b hb using hb
  have he : icosianMonomialToHermitian g=icosianReflectionSigns b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    have ha := icosianMonomialToHermitian_apply g x i
    change (icosianMonomialToHermitian g).val x i=
      (g.val.left i).val.val*x (g.val.right.symm i) at ha
    rw [ha,icosianReflectionSigns_apply,hp,hb]
    change (if b i then (-1 : IcosianQuaternion) else 1)*x i=if b i then -x i else x i
    cases b i <;> simp
  rw [he]
  exact icosianReflectionSigns_mem b

end Atlas.Conway
