import Submission.ZStar.BlockPrimitivity

/-!
# Collapsing a nonzero central-idempotent factor

A nonzero central idempotent factor of a centrally primitive idempotent is the
whole idempotent.  The specialized endpoint records the exact remaining input
that would upgrade the proved local-factor identity to equality with the
involution Brauer selector.
-/

noncomputable section

namespace Submission.ZStar

namespace CentralPrimitiveFactor

/-- A nonzero central idempotent left factor of a centrally primitive
idempotent equals that idempotent. -/
theorem eq_of_mul_eq_left_of_right_isCentrallyPrimitive
    {A : Type*} [Ring A]
    {eLocal eBrauer : A}
    (hLocalCenter : eLocal ∈ Set.center A)
    (hLocalIdempotent : IsIdempotentElem eLocal)
    (hfactor : eLocal * eBrauer = eLocal)
    (hLocalNe : eLocal ≠ 0)
    (hBrauerPrimitive : BlockPrimitivity.IsCentrallyPrimitive eBrauer) :
    eLocal = eBrauer :=
  hBrauerPrimitive.2.2.2 eLocal hLocalCenter hLocalIdempotent hfactor hLocalNe

/-- Two centrally primitive idempotents with nonzero intersection are equal.
This is the symmetric minimal algebraic bridge: no pre-existing factor
identity is needed. -/
theorem eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
    {A : Type*} [Ring A]
    {e f : A}
    (he : BlockPrimitivity.IsCentrallyPrimitive e)
    (hf : BlockPrimitivity.IsCentrallyPrimitive f)
    (hefne : e * f ≠ 0) :
    e = f := by
  have hcomm : f * e = e * f :=
    Semigroup.mem_center_iff.mp he.1 f
  have hcenter : e * f ∈ Set.center A :=
    Set.mul_mem_center he.1 hf.1
  have hidem : IsIdempotentElem (e * f) :=
    IsIdempotentElem.mul_of_commute hcomm.symm he.2.1 hf.2.1
  have hfactorE : (e * f) * e = e * f := by
    calc
      (e * f) * e = e * (f * e) := mul_assoc _ _ _
      _ = e * (e * f) := by rw [hcomm]
      _ = (e * e) * f := (mul_assoc _ _ _).symm
      _ = e * f := by rw [he.2.1.eq]
  have hfactorF : (e * f) * f = e * f := by
    calc
      (e * f) * f = e * (f * f) := mul_assoc _ _ _
      _ = e * f := by rw [hf.2.1.eq]
  have hprodE : e * f = e :=
    he.2.2.2 (e * f) hcenter hidem hfactorE hefne
  have hprodF : e * f = f :=
    hf.2.2.2 (e * f) hcenter hidem hfactorF hefne
  exact hprodE.symm.trans hprodF

/-- If the involution Brauer selector is centrally primitive, then the proved
local factor identity upgrades to equality of the two selectors. -/
theorem localPrincipalBlockElementInAmbientResidue_eq_involutionBrauer_of_primitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (hBrauerPrimitive : BlockPrimitivity.IsCentrallyPrimitive
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z)) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z := by
  apply eq_of_mul_eq_left_of_right_isCentrallyPrimitive
  · exact CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_mem_center
      d _
  · exact CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d _
  · exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  · intro hzero
    apply CompatibleBrauerBlock.localPrincipalBlockElement_mul_involutionBrauer_ne_zero
      d z hz
    rw [hzero, zero_mul]
  · exact hBrauerPrimitive

/-- Central primitivity of the involution Brauer selector is sufficient for
the full principal-Brauer equality.  The local selector's primitivity and the
nonzero overlap are already available unconditionally. -/
theorem involutionPrincipalBrauerEquality_of_brauer_isCentrallyPrimitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (hBrauerPrimitive : BlockPrimitivity.IsCentrallyPrimitive
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z)) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  change CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G)) =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  exact eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
    (BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
      d (Subgroup.centralizer ({z} : Set G)))
    hBrauerPrimitive
    (CompatibleBrauerBlock.localPrincipalBlockElement_mul_involutionBrauer_ne_zero
      d z hz)

end CentralPrimitiveFactor

end Submission.ZStar
