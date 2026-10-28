module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.QuasisimpleApplication

/-!
# Excluding the actual natural-plus-dual branch

B.5.1(6) identifies the quotient of the pointwise centralizer of the
Sylow-fixed space with PSL₂(2) or PSL₃(2). In the original source action
that pointwise centralizer is exactly the source Sylow subgroup. It is
therefore a two-group and equals its own two-core, so its quotient is
trivial. Both specified projective groups are nontrivial.

This directly eliminates B.5.1(1iii) on its literal moved submodule;
no splitting or sufficient small-section structure is required.
Source: Aschbacher–Smith, B.5.1(6), p.99; 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
open TwoFactors.FFBranch TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- The source Sylow kernel cannot have either quotient required by B.5.1(6). -/
theorem no_sylowFixedCentralizer (h : Input d i j H U K) {m : ℕ}
    (hm : m = 4 ∨ m = 5) :
    let := h.module_properties.1
    ¬ (∀ T : Sylow 2 (sourceGroup h),
      Nonempty (SylowFixedCentralizer (sourceAction h) ⊤ m T)) := by
  let := h.module_properties.1
  dsimp only
  intro hall
  obtain ⟨S, hS⟩ := exists_offenderSylow h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1
  change Sylow 2 (sourceGroup h) at S
  obtain ⟨c⟩ := hall S
  have he : subspaceKernel (sourceAction h)
      (fixedSpace (sourceAction h) (S : Subgroup _)) ⊤ = (S : Subgroup _) :=
    offenderAction_sylow_fixedSpace_kernel h.placed.sylow (d.Z.subgroupOf H)
      h.seed_inputs.2.2.1 _ hS
  let C := subspaceKernel (sourceAction h)
    (fixedSpace (sourceAction h) (S : Subgroup _)) ⊤
  have hp : IsPGroup 2 C := by
    change IsPGroup 2 (subspaceKernel (sourceAction h)
      (fixedSpace (sourceAction h) (S : Subgroup _)) ⊤)
    rw [he]
    exact S.isPGroup'
  have hcore : pCore 2 C = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩
  let : Subsingleton (C ⧸ pCore 2 C) := by
    exact QuotientGroup.subsingleton_iff.mpr hcore
  let : Subsingleton (Matrix.ProjectiveSpecialLinearGroup (Fin (m - 2)) (ZMod 2)) :=
    c.quotientEquiv.symm.injective.subsingleton
  have hm2 : 2 ≤ m - 2 := by rcases hm with rfl | rfl <;> decide
  let : Nontrivial (Fin (m - 2)) := Fin.nontrivial_iff_two_le.mpr hm2
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance)
    (Atlas.psl_nontrivial (F := ZMod 2) (ι := Fin (m - 2)))

/-- The actual full source conclusion excludes its natural-plus-dual alternative. -/
theorem not_naturalDual (h : Input d i j H U K)
    (c : let := h.module_properties.1
      ProjectiveLine.QuasisimpleSourceConclusion (sourceAction h)
        (generalizedFitting (sourceGroup h))) {m : ℕ}
    (hm : m = 4 ∨ m = 5)
    (hwhole : generalizedFitting (sourceGroup h) = ⊤) :
    let := h.module_properties.1
    ¬ IsNaturalPlusDual
      (c.sectionData.space.toRepresentation.comp (generalizedFitting (sourceGroup h)).subtype) m := by
  let := h.module_properties.1
  dsimp only
  intro hn
  have hall := c.clause_six m hm hwhole hn
  rw [hwhole] at hall
  exact no_sylowFixedCentralizer h hm hall

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
