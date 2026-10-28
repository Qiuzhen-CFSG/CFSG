/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianScalarIntersection.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianConwayEmbedding
public import Theory.AtlasPort.Janko2.Conway.IcosianScalarFaithfulness
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# IcosianScalarIntersection

The scalar units and full quaternionic linear group meet exactly in the two Leech signs.
The projective kernel identifies the intersection and the two diagonal elements in the central-product kernel.

Source: Gerald Höhn, `Atlas/Conway/IcosianScalarIntersection.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianScalarRepresentation_minusOne :
    icosianScalarRepresentation icosianNormOneMinusOne=icosianCentralSign.val := by
  apply LinearEquiv.ext
  intro x
  funext i
  rw [icosianCentralSign_apply]
  change x i*star (-1 : IcosianQuaternion)= -x i
  simp

theorem icosianScalarsToCo0_minusOne :
    icosianScalarsToCo0 icosianNormOneMinusOne=negationIsometry := by
  rw [← icosianHermitianToCo0_sign]
  apply fullIsometryEquiv.injective
  rw [icosianScalarsToCo0_extension,icosianHermitianToCo0_extension]
  apply Subtype.ext
  change icosianAutomorphismComparison (icosianScalarRepresentation icosianNormOneMinusOne)=
    icosianAutomorphismComparison icosianCentralSign.val
  rw [icosianScalarRepresentation_minusOne]

/-- Right scalar operators that are also fully right-linear must be signs.
The independently verified projective kernel supplies this directly. -/
theorem icosianHermitian_eq_sign_of_scalar (g : icosianHermitianGroup)
    (u : icosianNormOneGroup) (hg : g.val=icosianScalarRepresentation u) :
    g=1 ∨ g=icosianCentralSign := by
  apply icosian_fix_rootPoints_eq_sign
  intro p
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [← icosianRootToPoint_smul]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (↑((Unitary.toUnits u.val)⁻¹) : IcosianQuaternion),?_⟩
  change icosianRightMul (icosianCoordinateEmbedding r.val) _=
    icosianCoordinateEmbedding (icosianHermitianRoot g r).val
  rw [icosianHermitianRoot_embedding,hg]
  rfl

theorem icosianHermitian_eq_scalar_of_Co0 (g : icosianHermitianGroup)
    (u : icosianNormOneGroup)
    (he : icosianHermitianToCo0 g=icosianScalarsToCo0 u) :
    g.val=icosianScalarRepresentation u := by
  apply icosianAutomorphismComparison.injective
  have h := congrArg fullIsometryEquiv he
  rw [icosianHermitianToCo0_extension,icosianScalarsToCo0_extension] at h
  exact congrArg Subtype.val h

/-- The actual right unit subgroup and the full linear centralizer meet exactly
in the two retained Leech signs. -/
theorem icosianScalars_inf_centralizer :
    icosianScalarsToCo0.range ⊓ icosianCentralizer=leechCentralSigns := by
  ext g
  constructor
  · rintro ⟨⟨u,hu⟩,hg⟩
    obtain ⟨f,hf⟩ := icosianHermitianToCo0_surjective_centralizer ⟨g,hg⟩
    change icosianHermitianToCo0 f = g at hf
    have he := icosianHermitian_eq_scalar_of_Co0 f u (hf.trans hu.symm)
    rcases icosianHermitian_eq_sign_of_scalar f u he with h | h
    · rw [← hf,h,map_one]
      exact leechCentralSigns.one_mem
    · rw [← hf,h,icosianHermitianToCo0_sign]
      exact (leechCentralSigns_mem _).mpr (Or.inr rfl)
  · intro hg
    rcases (leechCentralSigns_mem g).mp hg with rfl | rfl
    · exact ⟨⟨1,map_one _⟩,icosianCentralizer.one_mem⟩
    · refine ⟨⟨icosianNormOneMinusOne,icosianScalarsToCo0_minusOne⟩,?_⟩
      rw [← icosianHermitianToCo0_sign]
      exact icosianHermitianToCo0_mem _

theorem icosianScalars_commute_Hermitian (u : icosianNormOneGroup)
    (g : icosianHermitianGroup) :
    Commute (icosianScalarsToCo0 u) (icosianHermitianToCo0 g) :=
  ((icosianCentralizer_mem _).mp (icosianHermitianToCo0_mem g) u).symm

/-- The actual commuting product before dividing its common central signs. -/
def icosianScalarCentralProduct :
    icosianNormOneGroup × icosianHermitianGroup →* LeechIsometryGroup :=
  icosianScalarsToCo0.noncommCoprod icosianHermitianToCo0 icosianScalars_commute_Hermitian

theorem icosianScalarCentralProduct_kernel_iff (u : icosianNormOneGroup)
    (g : icosianHermitianGroup) :
    (u,g)∈icosianScalarCentralProduct.ker ↔
      (u=1 ∧ g=1) ∨ (u=icosianNormOneMinusOne ∧ g=icosianCentralSign) := by
  change icosianScalarsToCo0 u*icosianHermitianToCo0 g=1 ↔ _
  constructor
  · intro h
    have he : icosianHermitianToCo0 g=icosianScalarsToCo0 u⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right h
    rcases icosianHermitian_eq_sign_of_scalar g u⁻¹
      (icosianHermitian_eq_scalar_of_Co0 g u⁻¹ he) with hg | hg
    · left
      refine ⟨?_,hg⟩
      apply icosianScalarsToCo0_injective
      simpa only [hg,map_one,mul_one] using h
    · right
      refine ⟨?_,hg⟩
      rw [hg,icosianHermitianToCo0_sign] at h
      have hu := eq_inv_of_mul_eq_one_left h
      have hn : negationIsometry⁻¹=negationIsometry :=
        inv_eq_of_mul_eq_one_right negationIsometry_sq
      rw [hn] at hu
      exact icosianScalarsToCo0_injective (hu.trans icosianScalarsToCo0_minusOne.symm)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp only [map_one,mul_one]
    · rw [icosianScalarsToCo0_minusOne,icosianHermitianToCo0_sign,negationIsometry_sq]

/-- The actual central product, identifying precisely the two diagonal signs. -/
abbrev IcosianCentralProductModel :=
  (icosianNormOneGroup × icosianHermitianGroup) ⧸ icosianScalarCentralProduct.ker

def icosianCentralProductToCo0 : IcosianCentralProductModel →* LeechIsometryGroup :=
  QuotientGroup.kerLift icosianScalarCentralProduct

theorem icosianCentralProductToCo0_injective : Function.Injective icosianCentralProductToCo0 :=
  QuotientGroup.kerLift_injective _

end Atlas.Conway
