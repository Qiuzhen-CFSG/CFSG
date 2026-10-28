module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Endpoints
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleCore
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleResidual

/-!
# Marked Levi structure of the exterior-square parabolics

The four actual parabolics have quotient maps given by their literal diagonal
blocks, with kernel O₂. The endpoint parabolics are perfect, and the source
hyperplane radical O₂(L₆T) is exactly the last-column shear subgroup.

For the middle parabolics, the perfect kernels of the small SL₂ blocks are
their solvable residuals. Substituting these proved identities into the
independent flag-join calculation identifies O₂(LᵢT) and the residual images
with no additional hypotheses. The residual projection kernels are Lᵢ ∩ Rᵢ;
the quotient and image equivalences retain the literal large diagonal block.
Natural flag dimensions k = 2,3,1,4 correspond to source indices i = 1,3,4,6.

Source: Aschbacher–Smith, Lemma 12.5.2, printed p.817/PDF p.834.
-/

@[expose] public section

open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

@[simp] theorem parabolicResidualFlag_two :
    parabolicResidualFlag 2 = MiddleCore.twoFlag := by
  rw [parabolicResidualFlag, parabolicResidual_two]
  rfl

@[simp] theorem parabolicResidualFlag_three :
    parabolicResidualFlag 3 = MiddleCore.threeFlag := by
  rw [parabolicResidualFlag, parabolicResidual_three]
  rfl

/-- The source radical R₁ includes the small unitriangular block. -/
@[simp] theorem parabolicResidualTwoCore_two :
    parabolicResidualTwoCore 2 = MiddleCore.twoRadical :=
  MiddleCore.parabolicResidualTwoCore_two parabolicResidual_two

/-- The source radical R₃ in the opposite block orientation. -/
@[simp] theorem parabolicResidualTwoCore_three :
    parabolicResidualTwoCore 3 = MiddleCore.threeRadical :=
  MiddleCore.parabolicResidualTwoCore_three parabolicResidual_three

/-- Entrywise description of R₁; the upper-right rectangle is unrestricted. -/
theorem mem_parabolicResidualTwoCore_two (g : Group) :
    g ∈ parabolicResidualTwoCore 2 ↔
      (∀ i j : Fin 5, 2 ≤ i.val → j.val < 2 → g.val i j = 0) ∧
      (g.val 0 0 = 1 ∧ g.val 1 0 = 0 ∧ g.val 1 1 = 1) ∧
      (∀ i j : Fin 3, g.val ⟨2+i.val, by omega⟩ ⟨2+j.val, by omega⟩ =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) := by
  rw [parabolicResidualTwoCore_two]
  exact MiddleCore.mem_twoRadical_entries g

/-- Entrywise description of R₃ with identity first three-dimensional block. -/
theorem mem_parabolicResidualTwoCore_three (g : Group) :
    g ∈ parabolicResidualTwoCore 3 ↔
      (∀ i j : Fin 5, 3 ≤ i.val → j.val < 3 → g.val i j = 0) ∧
      (∀ i j : Fin 3, g.val (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) ∧
      (g.val 3 3 = 1 ∧ g.val 4 3 = 0 ∧ g.val 4 4 = 1) := by
  rw [parabolicResidualTwoCore_three]
  exact MiddleCore.mem_threeRadical_entries g

/-- The source quotient (L₁T)/O₂(L₁T), marked by its last three coordinates. -/
noncomputable def parabolicTwoResidualFlagQuotientEquiv :
    (parabolicResidualFlag 2 ⧸ pCore 2 (parabolicResidualFlag 2)) ≃* SL(3, ZMod 2) :=
  MiddleCore.sourceTwoFlagQuotientEquiv parabolicResidual_two

/-- The source quotient (L₃T)/O₂(L₃T), marked by its first three coordinates. -/
noncomputable def parabolicThreeResidualFlagQuotientEquiv :
    (parabolicResidualFlag 3 ⧸ pCore 2 (parabolicResidualFlag 3)) ≃* SL(3, ZMod 2) :=
  MiddleCore.sourceThreeFlagQuotientEquiv parabolicResidual_three

@[simp] theorem parabolicTwoResidualFlagQuotientEquiv_mk (g : parabolicResidualFlag 2) :
    parabolicTwoResidualFlagQuotientEquiv (QuotientGroup.mk' _ g) =
      (parabolicLeviHom 2 (by decide)
        (Subgroup.inclusion (parabolicResidualFlag_le 2 (by decide)) g)).2 := rfl

@[simp] theorem parabolicThreeResidualFlagQuotientEquiv_mk (g : parabolicResidualFlag 3) :
    parabolicThreeResidualFlagQuotientEquiv (QuotientGroup.mk' _ g) =
      (parabolicLeviHom 3 (by decide)
        (Subgroup.inclusion (parabolicResidualFlag_le 3 (by decide)) g)).1 := rfl

/-- The actual residual L₁ fills the quotient of L₁T by R₁. -/
theorem parabolicTwoResidualImage_surjective :
    Function.Surjective (MiddleCore.residualImageHom 2) :=
  MiddleCore.residualImageHom_two_surjective parabolicResidual_two

/-- The same assertion for L₃ in its actual flag quotient. -/
theorem parabolicThreeResidualImage_surjective :
    Function.Surjective (MiddleCore.residualImageHom 3) :=
  MiddleCore.residualImageHom_three_surjective parabolicResidual_three

theorem parabolicTwoResidualImage_range : (MiddleCore.residualImageHom 2).range = ⊤ :=
  MiddleCore.residualImageHom_two_range parabolicResidual_two

theorem parabolicThreeResidualImage_range : (MiddleCore.residualImageHom 3).range = ⊤ :=
  MiddleCore.residualImageHom_three_range parabolicResidual_three

/-- The projection kernel embedded in SL₅ is the intersection Lᵢ ∩ Rᵢ. -/
theorem parabolicResidualImage_ker_map (k : ℕ) :
    (MiddleCore.residualImageHom k).ker.map (parabolicResidual k).subtype =
      parabolicResidual k ⊓ parabolicResidualTwoCore k := by
  rw [MiddleCore.residualImageHom_ker, Subgroup.subgroupOf_map_subtype, inf_comm]

/-- The genuine image of L₁ in (L₁T)/R₁ is SL₃(2). -/
noncomputable def parabolicTwoResidualImageEquiv :
    (MiddleCore.residualImageHom 2).range ≃* SL(3, ZMod 2) :=
  MiddleCore.sourceTwoImageEquiv parabolicResidual_two

/-- The genuine image of L₃ in (L₃T)/R₃ is SL₃(2). -/
noncomputable def parabolicThreeResidualImageEquiv :
    (MiddleCore.residualImageHom 3).range ≃* SL(3, ZMod 2) :=
  MiddleCore.sourceThreeImageEquiv parabolicResidual_three

theorem parabolicTwoResidualImageEquiv_entry (g : parabolicResidual 2) (i j : Fin 3) :
    (parabolicTwoResidualImageEquiv ((MiddleCore.residualImageHom 2).rangeRestrict g)).val i j =
      g.val.val ⟨2+i.val, by omega⟩ ⟨2+j.val, by omega⟩ :=
  MiddleCore.sourceTwoImageEquiv_entry parabolicResidual_two g i j

theorem parabolicThreeResidualImageEquiv_entry (g : parabolicResidual 3) (i j : Fin 3) :
    (parabolicThreeResidualImageEquiv ((MiddleCore.residualImageHom 3).rangeRestrict g)).val i j =
      g.val.val (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) :=
  MiddleCore.sourceThreeImageEquiv_entry parabolicResidual_three g i j

/-- The source L₁/(L₁ ∩ R₁), without assuming R₁ ≤ L₁. -/
noncomputable def parabolicTwoResidualQuotientEquiv :
    (parabolicResidual 2 ⧸ (parabolicResidualTwoCore 2).subgroupOf (parabolicResidual 2)) ≃*
      SL(3, ZMod 2) :=
  MiddleCore.sourceTwoResidualQuotientEquiv parabolicResidual_two

/-- The source L₃/(L₃ ∩ R₃), in the opposite block orientation. -/
noncomputable def parabolicThreeResidualQuotientEquiv :
    (parabolicResidual 3 ⧸ (parabolicResidualTwoCore 3).subgroupOf (parabolicResidual 3)) ≃*
      SL(3, ZMod 2) :=
  MiddleCore.sourceThreeResidualQuotientEquiv parabolicResidual_three

@[simp] theorem parabolicTwoResidualQuotientEquiv_mk (g : parabolicResidual 2) :
    parabolicTwoResidualQuotientEquiv (QuotientGroup.mk' _ g) =
      (parabolicLeviHom 2 (by decide) (Subgroup.inclusion (parabolicResidual_le 2) g)).2 := rfl

@[simp] theorem parabolicThreeResidualQuotientEquiv_mk (g : parabolicResidual 3) :
    parabolicThreeResidualQuotientEquiv (QuotientGroup.mk' _ g) =
      (parabolicLeviHom 3 (by decide) (Subgroup.inclusion (parabolicResidual_le 3) g)).1 := rfl

end Representation.SL5ExteriorSquare
