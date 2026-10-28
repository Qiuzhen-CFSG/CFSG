/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalCScalarNecessity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCScalarTest
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialLineScalar
public import Theory.AtlasPort.Janko2.Codes.IcosianGlueRepeatedBlocks

/-!
# IcosianLocalCScalarNecessity

A monomial element fixing the shape-C reference line satisfies the explicit scalar
test. Coordinate equations recover its common scalar and conjugates.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalCScalarNecessity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix

theorem icosianCandidateMatrix_integral (u : icosianOrder) :
    icosianCandidateMatrix u.val=icosianModuloTwo u := by
  rw [icosianCandidateMatrix_eq]
  apply congrArg icosianModuloTwo
  exact Subtype.ext (icosianIntegralCandidate_eq u.val u.property)

def icosianLocalUnitCoordinates (u : icosianNormOneGroup) : IcosianIntegerCoordinates :=
  (icosianNormOneCoordinatesEquiv.symm u).val

theorem icosianLocalUnitCoordinates_mem (u : icosianNormOneGroup) :
    icosianLocalUnitCoordinates u∈icosianNormOneCoordinates :=
  (icosianNormOneCoordinatesEquiv.symm u).property

theorem icosianLocalUnitCoordinates_value (u : icosianNormOneGroup) :
    icosianCoordinatesQuaternion (icosianLocalUnitCoordinates u)=u.val.val :=
  congrArg (fun v : icosianNormOneGroup => v.val.val)
    (icosianNormOneCoordinatesEquiv.apply_symm_apply u)

theorem icosianLocalCConjugate_mul (u : IcosianQuaternion) :
    icosianLocalCConjugate u*icosianLocalCScalar.val=icosianLocalCScalar.val*u := by
  have hq : star icosianLocalCScalar.val*icosianLocalCScalar.val=(2 : IcosianQuaternion) := by
    rw [Quaternion.star_mul_self]
    change (icosianNorm icosianLocalCScalar.val : IcosianQuaternion)=2
    rw [icosianLocalCScalar_norm]
    rfl
  change ((1/2 : ℚ) • (icosianLocalCScalar.val*u*star icosianLocalCScalar.val))*
    icosianLocalCScalar.val=_
  rw [smul_mul_assoc,mul_assoc,hq,mul_two,smul_add,← add_smul]
  norm_num

theorem icosianLocalCConjugate_of_mul (a u : IcosianQuaternion)
    (h : a*icosianLocalCScalar.val=icosianLocalCScalar.val*u) :
    icosianLocalCConjugate u=a := by
  have hn : icosianLocalCScalar.val≠0 := by
    intro hz
    have h := icosianLocalCScalar_norm
    rw [hz] at h
    norm_num [icosianNorm] at h
  apply mul_right_cancel₀ hn
  exact (icosianLocalCConjugate_mul u).trans h.symm

theorem icosianLocalCRoot_word (i : Fin 3) :
    icosianRootNormWord icosianLocalCRoot i=if i=0 then 2 else 1 := by
  apply icosianRootNormWord_of_norm
  fin_cases i
  · change icosianNorm icosianLocalCScalar.val=goldenIntegerToRational 2
    simpa only [map_ofNat] using icosianLocalCScalar_norm
  · change icosianNorm (1 : IcosianQuaternion)=goldenIntegerToRational 1
    rw [map_one]
    exact icosianNormOneGroup_norm 1
  · change icosianNorm (1 : IcosianQuaternion)=goldenIntegerToRational 1
    rw [map_one]
    exact icosianNormOneGroup_norm 1

theorem icosianLocalCLine_permutation (g : icosianLiftedMonomial)
    (h : icosianMonomialToHermitian g • icosianRootPoint icosianLocalCRoot=
      icosianRootPoint icosianLocalCRoot) : g.val.right 0=0 := by
  have hn := icosianMonomial_line_permutation_norm g icosianLocalCRoot h 0
  rw [icosianLocalCRoot_word,icosianLocalCRoot_word] at hn
  have hk : g.val.right.symm 0=0 := by
    by_contra hk
    simp only [hk,if_false,ite_true] at hn
    have he := congrArg QuadraticAlgebra.re hn
    change (1 : ℤ)=2 at he
    omega
  have he := congrArg g.val.right hk
  simpa using he.symm

theorem icosianLocalCLine_scalar_test (g : icosianLiftedMonomial)
    (hp : g.val.right 0=0) (u : icosianNormOneGroup)
    (hu : ∀ i,(g.val.left i).val.val*(icosianLocalCRoot.val (g.val.right.symm i)).val=
      (icosianLocalCRoot.val i).val*u.val.val) :
    IcosianLocalCScalarTest (icosianLocalUnitCoordinates u) := by
  have hp0 : g.val.right.symm 0=0 := by
    apply g.val.right.injective
    rw [g.val.right.apply_symm_apply,hp]
  have hv (i : Fin 3) (hi : i≠0) :
      (icosianLocalCRoot.val (g.val.right.symm i)).val=1 := by
    have hk : g.val.right.symm i≠0 := by
      intro h
      have he := congrArg g.val.right h
      exact hi (by simpa only [g.val.right.apply_symm_apply,hp] using he)
    generalize g.val.right.symm i=k at *
    fin_cases k <;> simp_all [icosianLocalCRoot,icosianLocalCVector]
  have hl1 : g.val.left 1=u := by
    apply Subtype.ext
    apply Subtype.ext
    have h := hu 1
    rw [hv 1 (by decide)] at h
    simpa [icosianLocalCRoot,icosianLocalCVector] using h
  have hl2 : g.val.left 2=u := by
    apply Subtype.ext
    apply Subtype.ext
    have h := hu 2
    rw [hv 2 (by decide)] at h
    simpa [icosianLocalCRoot,icosianLocalCVector] using h
  have hc : icosianLocalCConjugate u.val.val=(g.val.left 0).val.val := by
    apply icosianLocalCConjugate_of_mul
    have h := hu 0
    rw [hp0] at h
    exact h
  have hg := g.property
  change icosianMonomialReduction g.val∈icosianGlueMonomialStabilizer GoldenFour at hg
  rw [icosianGlueMonomialStabilizer_iff] at hg
  change IcosianGluePreserves (fun i => icosianNormOneReduction (g.val.left i)) at hg
  have he : (fun i => icosianNormOneReduction (g.val.left i))=
      ![icosianNormOneReduction (g.val.left 0),icosianNormOneReduction u,
        icosianNormOneReduction u] := by
    funext i
    fin_cases i <;> simp [hl1,hl2]
  rw [he] at hg
  have htwo (x : GoldenFour) : x+x=0 := by
    ext <;> simp [CharTwo.add_self_eq_zero]
  have hg' := (icosianGlue_repeated_blocks_iff htwo
    (icosianNormOneReduction u) (icosianNormOneReduction (g.val.left 0))).mp hg
  unfold IcosianLocalCScalarTest
  rw [icosianLocalUnitCoordinates_value]
  dsimp only
  rw [hc]
  have hm (v : icosianNormOneGroup) : icosianCandidateMatrix v.val.val=
      (icosianNormOneReduction v : IcosianMatrix) :=
    icosianCandidateMatrix_integral (icosianNormOneToOrder v)
  rw [hm,hm]
  exact ⟨(isIcosian_iff_integralTest _).mp (g.val.left 0).property,hg'⟩

end Atlas.Conway
