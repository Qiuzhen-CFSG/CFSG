module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.TensorComparison
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SourceComparisons

/-!
# Equivariance of the corrected second-axis tensor comparison

Collected even words act on the first and third natural factors through their
actual, different halfspace actions. Combining these actions with the two
signed second-axis modules gives formulas 29.7.3 and 29.7.4. Their coordinate
signs prove that the published corrected tensor comparison intertwines the
actual NPlus representations. The marked signed tensors span, so the formula
extends to every vector.

Source: Aschbacher, *Sporadic Groups*, 29.7(1), printed p. 156 (PDF page 84).
The book's right product psi1(d) psi2(e) psi1(alpha) is reversed under left
function composition: psiAut1N alpha * psi2N e * psi1N d.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC TrialitySpin SpinActions SignedModules
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction


/-- A collected even word, in left function-composition order. -/
def evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) : NPlus :=
  ⟨(normalForm d e α).val, (normalForm_mem_NPlus_iff d e α).mpr hα⟩

theorem evenWord_surjective (g : NPlus) :
    ∃ d e α hα, evenWord d e α hα = g := by
  obtain ⟨⟨d,e,α⟩,hw⟩ := normalForm_bijective.surjective (HalfActions.inclusion g)
  have hv : (normalForm d e α).val = g.val := congrArg Subtype.val hw
  exact ⟨d,e,α,(normalForm_mem_NPlus_iff d e α).mp (hv.symm ▸ g.prop),Subtype.ext hv⟩

theorem evenWord_third_halfspace (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (ε : ParkerBit) :
    HalfActions.permutations (evenWord d e α hα) '' Natural.halfspace 2 (x,ε) =
      Natural.halfspace 2 ((parkerStandardProjection α).val x,
        ε + d.1.val x + e.1.val x) := by
  change ((psiAut1 α.val ∘ psi2 e) ∘ psi1 d) '' Natural.halfspace 2 (x,ε) = _
  have h1 := Natural.psi_other_halfspace 0 2 (by decide) d x ε
  have h2 := Natural.psi_other_halfspace 1 2 (by decide) e x (ε + d.1.val x)
  change psi1 d '' Natural.halfspace 2 (x,ε) = _ at h1
  change psi2 e '' Natural.halfspace 2 (x,ε + d.1.val x) = _ at h2
  rw [Set.image_comp, h1, Set.image_comp, h2]
  exact Natural.standard_even_halfspace 0 2 α hα x _

theorem preserves_third_halfspaces (g : NPlus) :
    Natural.Carries 2 2 (HalfActions.permutations g) := by
  obtain ⟨d,e,α,hα,rfl⟩ := evenWord_surjective g
  rintro ⟨x,ε⟩
  exact ⟨_,evenWord_third_halfspace d e α hα x ε⟩

/-- This is the third-axis halfspace action, not the first action on the same carrier. -/
def thirdNatural : Representation ℝ NPlus Natural.B3_24 :=
  Natural.representation HalfActions.permutations preserves_third_halfspaces

def firstTensor : Representation ℝ NPlus (Natural.B1_24 ⊗[ℝ] B1A2) :=
  Representation.tprod (NaturalAction.representation.comp HalfActions.inclusion)
    HalfActions.secondRepresentation

def thirdTensor : Representation ℝ NPlus (Natural.B3_24 ⊗[ℝ] B3A2) :=
  thirdNatural.tprod HalfActions.thirdSecondRepresentation

theorem thirdNatural_evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (ε : ParkerBit) :
    thirdNatural (evenWord d e α hα) (Natural.L 2 ε x) =
      Natural.L 2 (ε + d.1.val x + e.1.val x) ((parkerStandardProjection α).val x) := by
  rw [thirdNatural, Natural.representation_L,
    Natural.labelEquiv_of_image _ _ _ _ (evenWord_third_halfspace d e α hα x ε)]

theorem second_evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    HalfActions.secondRepresentation (evenWord d e α hα) (delta2 b) =
      delta2 (α.val (loopSandwich e (parkerLoopMultiply d b))) :=
  induced_delta2 HalfActions.permutations HalfActions.preserves_axis2
    HalfActions.commutes_k1 HalfActions.commutes_z1 _ b _
    (normalForm_axis2_even d e α hα b)

theorem thirdSecond_evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    HalfActions.thirdSecondRepresentation (evenWord d e α hα) (B3Axis2.delta b) =
      B3Axis2.delta (α.val (loopSandwich e (parkerLoopMultiply d b))) :=
  B3Axis2.inducedRepresentation_delta HalfActions.permutations HalfActions.preserves_axis2
    HalfActions.commutes_k3 HalfActions.commutes_z3 _ b _
    (normalForm_axis2_even d e α hα b)

private theorem bit_cases (s : ParkerBit) : s = 0 ∨ s = 1 := by revert s; decide

theorem first_sign_transfer (s : ParkerBit) (x : Omega) (b : ParkerLoop) :
    Natural.L 0 (1+s) x ⊗ₜ[ℝ] delta2 b =
      Natural.L 0 1 x ⊗ₜ[ℝ] delta2 (parkerSign s b) := by
  rcases bit_cases s with rfl | rfl
  · rw [add_zero, parkerSign_zero]
  · rw [Natural.L_add_one, delta2_sign, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

theorem third_sign_transfer (s : ParkerBit) (x : Omega) (b : ParkerLoop) :
    Natural.L 2 (1+s) x ⊗ₜ[ℝ] B3Axis2.delta b =
      Natural.L 2 1 x ⊗ₜ[ℝ] B3Axis2.delta (parkerSign s b) := by
  rcases bit_cases s with rfl | rfl
  · rw [add_zero, parkerSign_zero]
  · rw [Natural.L_add_one, B3Axis2.delta_sign, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

/-- Formula 29.7.3 with the book's right product reversed. -/
theorem firstTensor_evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (b : ParkerLoop) :
    firstTensor (evenWord d e α hα) (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b) =
      Natural.L 0 1 ((parkerStandardProjection α).val x) ⊗ₜ[ℝ]
        delta2 (parkerSign (e.1.val x + golayQuarterWeight e.1 +
          golayHalfOverlap (parkerLoopMultiply d b).1 e.1) (α.val (parkerLoopMultiply d b))) := by
  change NaturalAction.representation (normalForm d e α) (Natural.L 0 1 x) ⊗ₜ[ℝ]
    HalfActions.secondRepresentation (evenWord d e α hα) (delta2 b) = _
  rw [NaturalAction.representation_normalForm_L, second_evenWord, first_sign_transfer]
  rw [loopSandwich, normalForm_sandwich, parkerStandard_preserves_sign, parkerSign_add]
  congr 3
  rw [golayHalfOverlap_symmetric]
  abel

/-- Formula 29.7.4 for the genuine third natural action. -/
theorem thirdTensor_evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (b : ParkerLoop) :
    thirdTensor (evenWord d e α hα) (Natural.L 2 1 x ⊗ₜ[ℝ] B3Axis2.delta b) =
      Natural.L 2 1 ((parkerStandardProjection α).val x) ⊗ₜ[ℝ]
        B3Axis2.delta (parkerSign ((d.1.val x + e.1.val x) + golayQuarterWeight e.1 +
          golayHalfOverlap (parkerLoopMultiply d b).1 e.1) (α.val (parkerLoopMultiply d b))) := by
  change thirdNatural (evenWord d e α hα) (Natural.L 2 1 x) ⊗ₜ[ℝ]
    HalfActions.thirdSecondRepresentation (evenWord d e α hα) (B3Axis2.delta b) = _
  rw [thirdNatural_evenWord, thirdSecond_evenWord, add_assoc (1 : ParkerBit), third_sign_transfer]
  rw [loopSandwich, normalForm_sandwich, parkerStandard_preserves_sign, parkerSign_add]
  congr 3
  rw [golayHalfOverlap_symmetric]
  abel

theorem standard_coordinate_at (α : ParkerStandardGroup) (x : Omega) (b : ParkerLoop) :
    (α.val b).1.val ((parkerStandardProjection α).val x) = b.1.val x := by
  rw [Natural.standard_coordinates]
  change b.1.val ((parkerStandardProjection α).val.symm ((parkerStandardProjection α).val x)) = _
  rw [Equiv.symm_apply_apply]

theorem sourceTensorComparison_evenWord (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (b : ParkerLoop) :
    sourceTensorComparison
      (firstTensor (evenWord d e α hα) (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b)) =
    thirdTensor (evenWord d e α hα)
      (sourceTensorComparison (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b)) := by
  rw [firstTensor_evenWord, sourceTensorComparison_delta, sourceTensorComparison_delta,
    thirdTensor_evenWord]
  rw [parkerLoopMultiply_sign_right, parkerStandard_preserves_sign]
  simp only [parkerSign_add]
  rw [show (parkerSign (e.1.val x + golayQuarterWeight e.1 +
      golayHalfOverlap (parkerLoopMultiply d b).1 e.1) (α.val (parkerLoopMultiply d b))).1.val
      ((parkerStandardProjection α).val x) = d.1.val x + b.1.val x from
    standard_coordinate_at α x (parkerLoopMultiply d b)]
  change Natural.L 2 1 _ ⊗ₜ[ℝ] B3Axis2.delta (parkerSign _ (α.val (parkerLoopMultiply d b))) =
    Natural.L 2 1 _ ⊗ₜ[ℝ] B3Axis2.delta (parkerSign _ (α.val (parkerLoopMultiply d b)))
  congr 3
  abel

private theorem firstTensor_ext {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (f g : (Natural.B1_24 ⊗[ℝ] B1A2) →ₗ[ℝ] M)
    (h : ∀ x b, f (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b) =
      g (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b)) : f = g := by
  apply TensorProduct.ext
  apply (Natural.basis 0).ext
  intro x
  apply firstSecond.geometry.vector_ext
  intro a
  obtain ⟨b,rfl⟩ := axis2Equiv.surjective a
  change f (Natural.basis 0 x ⊗ₜ[ℝ] delta2 b) = g (Natural.basis 0 x ⊗ₜ[ℝ] delta2 b)
  rw [Natural.basis_eq_L]
  exact h x b

private theorem intertwines_of_vectors
    (e : Natural.B1_24 ⊗[ℝ] B1A2 ≃ₗ[ℝ] Natural.B3_24 ⊗[ℝ] B3A2)
    (r : Module.End ℝ (Natural.B1_24 ⊗[ℝ] B1A2))
    (s : Module.End ℝ (Natural.B3_24 ⊗[ℝ] B3A2))
    (h : ∀ x b, e (r (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b)) =
      s (e (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b))) (v : Natural.B1_24 ⊗[ℝ] B1A2) :
    e (r v) = s (e v) := by
  have he := firstTensor_ext (e.toLinearMap.comp r) (s.comp e.toLinearMap) h
  exact LinearMap.congr_fun he v

/-- The corrected comparison intertwines the two actual NPlus tensor actions. -/
theorem sourceTensorComparison_equivariant (g : NPlus)
    (v : Natural.B1_24 ⊗[ℝ] B1A2) :
    sourceTensorComparison (firstTensor g v) = thirdTensor g (sourceTensorComparison v) := by
  obtain ⟨d,e,α,hα,rfl⟩ := evenWord_surjective g
  have hp := sourceTensorComparison_evenWord d e α hα
  generalize hc : sourceTensorComparison = c at hp ⊢
  exact intertwines_of_vectors c (firstTensor (evenWord d e α hα))
    (thirdTensor (evenWord d e α hα)) hp v



end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction
