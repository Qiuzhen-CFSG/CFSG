module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.NaturalFour
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.ThreeDuality

/-!
# Residual quotients and their marked natural projections

Perfection identifies each endpoint residual with its parabolic and its flag
join. The first isomorphism theorem then identifies Lᵢ/(Lᵢ ∩ Rᵢ) with the
literal SL₄ diagonal block. On the three-space parabolic we compose the proved
SL₃ residual quotient with inverse transpose, as required by complementary
wedge coordinates. All projection identities are checked on representatives.

The equality R₆ = shearSubgroup transports the quotient-to-shear isomorphism
to the source radical, retaining its conjugation identity in the ambient SL₅.
Natural flag dimensions 1,4,3 correspond here to source indices 4,6,3.
Source: Aschbacher–Smith, Lemma 12.5.2(2–4), printed p.817/PDF p.834.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The source (L₄T)/R₄, via the equality L₄T = M₄ and its lower block. -/
def parabolicOneResidualFlagQuotientEquiv :
    (parabolicResidualFlag 1 ⧸ pCore 2 (parabolicResidualFlag 1)) ≃* SL(4, ZMod 2) :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr parabolicResidualFlag_one)
    (pCore_map_iso 2 (MulEquiv.subgroupCongr parabolicResidualFlag_one))).trans
    parabolicOneQuotientEquiv

/-- The source (L₆T)/R₆, via the equality L₆T = M₆ and its upper block. -/
def parabolicFourResidualFlagQuotientEquiv :
    (parabolicResidualFlag 4 ⧸ pCore 2 (parabolicResidualFlag 4)) ≃* SL(4, ZMod 2) :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr parabolicResidualFlag_four)
    (pCore_map_iso 2 (MulEquiv.subgroupCongr parabolicResidualFlag_four))).trans
    parabolicFourQuotientEquiv

private theorem endpoint_residualImage_surjective (k : ℕ)
    (h : parabolicResidualFlag k = parabolicResidual k) :
    Function.Surjective (MiddleCore.residualImageHom k) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (parabolicResidualFlag k)) q
  exact ⟨⟨g.val, h ▸ g.property⟩, rfl⟩

/-- The actual L₄/(L₄ ∩ R₄), marked by its lower SL₄ block. -/
def parabolicOneResidualQuotientEquiv :
    (parabolicResidual 1 ⧸ (parabolicResidualTwoCore 1).subgroupOf (parabolicResidual 1)) ≃*
      SL(4, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (MiddleCore.residualImageHom_ker 1).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (MiddleCore.residualImageHom 1)
      (by
        exact endpoint_residualImage_surjective 1
          (by rw [parabolicResidualFlag_one, parabolicResidual_one]))).trans
      parabolicOneResidualFlagQuotientEquiv)

/-- The actual L₆/(L₆ ∩ R₆), marked by its upper SL₄ block. -/
def parabolicFourResidualQuotientEquiv :
    (parabolicResidual 4 ⧸ (parabolicResidualTwoCore 4).subgroupOf (parabolicResidual 4)) ≃*
      SL(4, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (MiddleCore.residualImageHom_ker 4).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (MiddleCore.residualImageHom 4)
      (by
        exact endpoint_residualImage_surjective 4
          (by rw [parabolicResidualFlag_four, parabolicResidual_four]))).trans
      parabolicFourResidualFlagQuotientEquiv)

/-- Compatibility with the literal block projection on representatives. -/
@[simp] theorem parabolicOneResidualQuotientEquiv_mk (g : parabolicResidual 1) :
    parabolicOneResidualQuotientEquiv (QuotientGroup.mk' _ g) =
      lowerFourProjection (Subgroup.inclusion (parabolicResidual_le 1) g) := by
  apply Subtype.ext
  ext i j
  change (parabolicLeviHom 1 (by decide)
    (Subgroup.inclusion (parabolicResidual_le 1) g)).2.val i j = _
  rw [parabolicLeviHom_snd_entry]
  change g.val.val ⟨1+i.val, _⟩ ⟨1+j.val, _⟩ = g.val.val i.succ j.succ
  have hi : (⟨1+i.val, by omega⟩ : Fin 5) = i.succ := Fin.ext (by simp [Nat.add_comm])
  have hj : (⟨1+j.val, by omega⟩ : Fin 5) = j.succ := Fin.ext (by simp [Nat.add_comm])
  rw [hi, hj]

/-- Compatibility with the literal block projection on representatives. -/
@[simp] theorem parabolicFourResidualQuotientEquiv_mk (g : parabolicResidual 4) :
    parabolicFourResidualQuotientEquiv (QuotientGroup.mk' _ g) =
      upperFourProjection (Subgroup.inclusion (parabolicResidual_le 4) g) := by
  apply Subtype.ext
  ext i j
  change (parabolicLeviHom 4 (by decide)
    (Subgroup.inclusion (parabolicResidual_le 4) g)).1.val i j = _
  rw [parabolicLeviHom_fst_entry]
  rfl

/-- The natural V₃ actor: the actual residual quotient followed by inverse transpose. -/
def parabolicThreeResidualNaturalEquiv :
    (parabolicResidual 3 ⧸ (parabolicResidualTwoCore 3).subgroupOf (parabolicResidual 3)) ≃*
      SL(3, ZMod 2) := parabolicThreeResidualQuotientEquiv.trans threeInverseTranspose

/-- Compatibility with the literal block projection on representatives. -/
@[simp] theorem parabolicThreeResidualNaturalEquiv_mk (g : parabolicResidual 3) :
    parabolicThreeResidualNaturalEquiv (QuotientGroup.mk' _ g) =
      threeNaturalProjection (Subgroup.inclusion (parabolicResidual_le 3) g) := by
  change threeInverseTranspose (parabolicThreeResidualQuotientEquiv (QuotientGroup.mk' _ g)) =
    threeInverseTranspose (upperThreeProjection (Subgroup.inclusion (parabolicResidual_le 3) g))
  congr 1
  rw [parabolicThreeResidualQuotientEquiv_mk]
  apply Subtype.ext
  ext i j
  rw [parabolicLeviHom_fst_entry]
  rfl

/-- The actual quotient V/V₆ is isomorphic to R₆ = O₂(L₆T). -/
def quotientSixRadicalEquiv : Multiplicative (V ⧸ V₆) ≃* parabolicResidualTwoCore 4 :=
  quotientSixShearEquiv.trans (MulEquiv.subgroupCongr parabolicResidualTwoCore_four.symm)

/-- This isomorphism intertwines the full parabolic action with actual conjugation. -/
theorem quotientSixRadicalEquiv_action (g : parabolic 4) (v : V ⧸ V₆) :
    (quotientSixRadicalEquiv (Multiplicative.ofAdd (quotientSixAction g v)) : Group) =
      g.val * (quotientSixRadicalEquiv (Multiplicative.ofAdd v) : Group) * g.val⁻¹ :=
  quotientSixShearEquiv_action g v

/-- At the line endpoint, perfection puts the source radical inside the residual. -/
theorem parabolicResidualTwoCore_one_le_residual :
    parabolicResidualTwoCore 1 ≤ parabolicResidual 1 := by
  simpa only [parabolicResidualFlag_one, parabolicResidual_one] using
    parabolicResidualTwoCore_le 1

/-- At the hyperplane endpoint, the source R₆ is contained in L₆. -/
theorem parabolicResidualTwoCore_four_le_residual :
    parabolicResidualTwoCore 4 ≤ parabolicResidual 4 := by
  simpa only [parabolicResidualFlag_four, parabolicResidual_four] using
    parabolicResidualTwoCore_le 4

end Representation.SL5ExteriorSquare
