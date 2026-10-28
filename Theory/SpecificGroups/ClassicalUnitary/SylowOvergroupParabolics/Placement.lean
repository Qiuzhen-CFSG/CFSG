module

public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.Placement.Coordinates

/-!
# Reduction of unitary Sylow-overgroup placement to concrete flag geometry

The abstract Bruhat product argument enlarges a proper overgroup of the
distinguished Sylow subgroup to a proper Borel overgroup. Geometric Borel
placement then supplies an invariant isotropic subspace. Sylow conjugacy
and the exact SU-to-PSU stabilizer formulas extend this to every Sylow
subgroup, for the original arbitrary Hermitian form.

The concrete flag/Bruhat construction and classification of geometric Borel
overgroups remain explicit inputs here. This module does not yet assert
unconditional higher-dimensional placement. Its output has exactly the
placement signature used by `HigherUnitary.properSylowFittingBound_of_isotropic_placement`.

Source: GLS3, Theorems 2.6.5(b) and 2.6.7, with the classical interpretation
in §2.7; Aschbacher--Smith B.1.13, printed p.74 (PDF p.85).
-/

public section

open BenderSuzuki.MatrixGroups Subgroup Theory.GroupTheory
open scoped Pointwise

namespace Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics

variable {F : Type*} [Field F] [Finite F] {d : ℕ} (J : HermitianForm d F)

/-- The Borel-overgroup theorem need only be proved for one actual complete
isotropic flag. Bruhat factorization and normal generation supply the passage
from Sylow containment; Sylow conjugacy supplies all other positions. -/
theorem isotropic_placement_of_bruhat_flag
    (f : IsotropicFlag J) (D : SylowBruhatData f.borel)
    (hBorel : ∀ P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      f.borel ≤ P → P ≠ ⊤ →
      ∃ W : Submodule F (Fin d → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        TotallyIsotropic J W ∧ P ≤ parabolic J W)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hSX : (S : Subgroup _) ≤ X) (hX : X ≠ ⊤) :
    ∃ W : Submodule F (Fin d → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      TotallyIsotropic J W ∧ X ≤ parabolic J W := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (ProjectiveSpecialUnitaryMatrixGroup J) D.sylow S
  obtain ⟨a, rfl⟩ := project_surjective J g
  let α := MulAut.conj (project J a)
  have hS : (D.sylow : Subgroup _).map α.toMonoidHom = (S : Subgroup _) := by
    have h := congrArg (fun T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) =>
      (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) hg
    exact (Sylow.coe_subgroup_smul (g := project J a) (P := D.sylow)).symm.trans h
  let Q := X.comap α.toMonoidHom
  have hUQ : (D.sylow : Subgroup _) ≤ Q := by
    apply Subgroup.map_le_iff_le_comap.mp
    exact hS.le.trans hSX
  have hQ : Q ≠ ⊤ := by
    intro htop
    apply hX
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := α.surjective x
    have hy : y ∈ Q := htop ▸ (show y ∈ (⊤ : Subgroup _) from trivial)
    exact hy
  obtain ⟨P, hBP, hQP, hP⟩ := D.exists_proper_borel_overgroup Q hUQ hQ
  obtain ⟨W, hW, hWtop, hi, hWP⟩ := hBorel P hBP hP
  refine ⟨W.map (linearAction J a).toLinearMap, ?_, ?_,
    hi.map_linearAction J a, ?_⟩
  · exact Submodule.map_ne_bot_iff.mpr hW
  · exact Submodule.map_ne_top_iff.mpr hWtop
  · rw [parabolic_map_linearAction]
    have h := Subgroup.map_mono (f := α.toMonoidHom) (hQP.trans hWP)
    change (X.comap α.toMonoidHom).map α.toMonoidHom ≤ _ at h
    rw [Subgroup.map_comap_eq_self_of_surjective α.surjective] at h
    exact h

end Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
