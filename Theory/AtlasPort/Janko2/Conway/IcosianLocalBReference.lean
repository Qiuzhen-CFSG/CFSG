/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalBReference.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianUpperUnitCount

/-!
# IcosianLocalBReference

An explicit repeated-coordinate root represents shape B. Its scalar and coordinate
constraints describe monomial elements fixing its line.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalBReference.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix

def icosianLocalBScalar : IcosianNormTwo :=
  ⟨icosianNormTwoRepresentative 0,icosianNormTwoRepresentative_norm 0⟩

theorem icosianLocalBScalar_mem : icosianLocalBScalar.val∈icosianP := by
  intro j
  change icosianModuloTwo (icosianNormTwoRepresentative 0) 1 j=0
  rw [icosianNormTwoRepresentative_reduction]
  fin_cases j <;> decide +kernel

def icosianLocalBPair : IcosianEdgePair :=
  ⟨(icosianLocalBScalar,icosianLocalBScalar),rfl,icosianLocalBScalar_mem⟩

def icosianLocalBRoot : IcosianRoot := icosianEdgeRootBase icosianLocalBPair

theorem icosianLocalBRoot_word (i : Fin 3) :
    icosianRootNormWord icosianLocalBRoot i=if i=0 then 0 else 2 := by
  apply icosianRootNormWord_of_norm
  fin_cases i
  · change icosianNorm (0 : IcosianQuaternion)=goldenIntegerToRational 0
    simp [icosianNorm]
  · change icosianNorm icosianLocalBScalar.val.val=goldenIntegerToRational 2
    simpa only [map_ofNat] using icosianLocalBScalar.property
  · change icosianNorm icosianLocalBScalar.val.val=goldenIntegerToRational 2
    simpa only [map_ofNat] using icosianLocalBScalar.property

theorem icosianLocalBRoot_shape : HasIcosianRootShape icosianLocalBRoot 1 := by
  apply (icosianRootShape_edge _).mpr
  apply icosianEdgeRoot_recognition _ 0
  · rfl
  · exact icosianEdgeRootBase_norm icosianLocalBPair

theorem icosianLocalBLine_permutation (g : icosianLiftedMonomial)
    (h : icosianMonomialToHermitian g • icosianRootPoint icosianLocalBRoot=
      icosianRootPoint icosianLocalBRoot) : g.val.right 0=0 := by
  have hn := icosianMonomial_line_permutation_norm g icosianLocalBRoot h 0
  rw [icosianLocalBRoot_word,icosianLocalBRoot_word] at hn
  have hk : g.val.right.symm 0=0 := by
    by_contra hk
    simp only [hk,if_false,ite_true] at hn
    have he := congrArg QuadraticAlgebra.re hn
    change (2 : ℤ)=0 at he
    omega
  have he := congrArg g.val.right hk
  simpa using he.symm

theorem icosianLocalBLine_repeated (g : icosianLiftedMonomial)
    (h : icosianMonomialToHermitian g • icosianRootPoint icosianLocalBRoot=
      icosianRootPoint icosianLocalBRoot) : g.val.left 1=g.val.left 2 := by
  have hp := icosianLocalBLine_permutation g h
  obtain ⟨u,hu⟩ := (icosianMonomial_line_iff g icosianLocalBRoot).mp h
  have hv (i : Fin 3) (hi : i≠0) :
      (icosianLocalBRoot.val (g.val.right.symm i)).val=icosianLocalBScalar.val.val := by
    have hk : g.val.right.symm i≠0 := by
      intro hh
      have he := congrArg g.val.right hh
      exact hi (by simpa only [g.val.right.apply_symm_apply,hp] using he)
    generalize g.val.right.symm i=k at *
    fin_cases k <;> simp_all [icosianLocalBRoot,icosianEdgeRootBase,icosianLocalBPair]
  have h1 := hu 1
  have h2 := hu 2
  rw [hv 1 (by decide)] at h1
  rw [hv 2 (by decide)] at h2
  apply Subtype.ext
  apply Subtype.ext
  have ht : icosianLocalBScalar.val.val≠0 := by
    intro hz
    have hn := icosianLocalBScalar.property
    rw [hz] at hn
    norm_num [icosianNorm] at hn
  apply mul_right_cancel₀ ht
  exact h1.trans h2.symm

end Atlas.Conway
