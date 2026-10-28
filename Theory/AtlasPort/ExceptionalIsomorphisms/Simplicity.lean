module

/-
Adapted from Atlas/LinearGroups/PSLSimplicity.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
set_option warningAsError false

public section


/-! # The projective transvection subgroups and higher-dimensional simplicity -/

namespace Atlas
open Matrix Matrix.SpecialLinearGroup MulAction
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

theorem lineTransvections_abelian (p : ℙ F (ι → F)) :
    IsMulCommutative (lineStab p.submodule) := by
  rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
  exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero


theorem lineTransvections_conj (g : SpecialLinearGroup ι F) (p : ℙ F (ι → F)) :
    lineStab (g • p).submodule = MulAut.conj g • lineStab p.submodule := by
  rw [PSL.smul_submodule, lineStab_smul]


theorem projectiveTransvections_abelian (p : ℙ F (ι → F)) :
    IsMulCommutative (PSL.iwasawaT p) := by
  let := lineTransvections_abelian p
  exact Subgroup.map_isMulCommutative _ _

theorem projectiveTransvections_conj (g : ProjectiveSpecialLinearGroup ι F)
    (p : ℙ F (ι → F)) : PSL.iwasawaT (g • p) = MulAut.conj g • PSL.iwasawaT p := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
  change Subgroup.map _ _ = _
  rw [lineTransvections_conj, PSL.iwasawaT_map_conj]


theorem lineTransvections_generate [Nontrivial ι] :
    (⨆ p : ℙ F (ι → F), lineStab p.submodule) = ⊤ := by
  apply top_unique
  intro g _
  apply sl_elementary_induction (fun g ↦ g ∈ ⨆ p : ℙ F (ι → F), lineStab p.submodule) _
    (fun _ _ ↦ Subgroup.mul_mem _) g
  intro i j hij a
  let p := Projectivization.mk F (Pi.single i (1 : F) : ι → F)
    (Pi.single_ne_zero_iff.mpr one_ne_zero)
  exact (le_iSup (fun p : ℙ F (ι → F) ↦ lineStab p.submodule) p)
    (SL2Gen.transvection_mem_lineStab hij a)

theorem projectiveTransvections_generate [Nontrivial ι] :
    iSup (PSL.iwasawaT (F := F) (ι := ι)) = ⊤ := by
  have h : iSup (PSL.iwasawaT (F := F) (ι := ι)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup ι F)))
        (⨆ p : ℙ F (ι → F), lineStab p.submodule) := by
    rw [Subgroup.map_iSup]
  rw [h, lineTransvections_generate]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)


noncomputable def pslIwasawa [Nontrivial ι] :
    IwasawaStructure (ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) where
  T := PSL.iwasawaT
  is_comm := projectiveTransvections_abelian
  is_conj := projectiveTransvections_conj
  is_generator := projectiveTransvections_generate

theorem psl_nontrivial [Nontrivial ι] : Nontrivial (ProjectiveSpecialLinearGroup ι F) :=
  inferInstance

theorem psl_simple_high_rank (n : ℕ) (hn : 3 ≤ n) : IsSimpleGroup (PSL(n, F)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let := psl_perfect (F := F) n hn
  exact IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top pslIwasawa
    (inferInstance)


end Atlas
