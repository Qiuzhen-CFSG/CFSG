module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.Centralizer
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Reduction of the binary matrix normalizer to its perfect core quotient

Conjugation by a normalizing matrix restricts to the genuine derived
subgroup and descends to its quotient by the center. If that subgroup is
perfect, the quotient action determines the restricted automorphism.
If the original matrix group realizes all quotient automorphisms, a
normalizing matrix differs from a member of the group by an element of
the derived subgroup's matrix centralizer. The latter is already bounded
by the kernel-checked calculation in `Centralizer`.

Perfectness and full quotient-automorphism coverage remain explicit inputs;
this reduction asserts no recognition of the ATLAS model as a cover of M₂₂.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- Include the original matrix group in the normalizer of its commutator subgroup. -/
def toDerivedNormalizer : actionGroup →*
    Subgroup.normalizer (derivedGroup : Set Matrix12ˣ) :=
  Subgroup.inclusion (actionGroup.le_normalizer.trans
    normalizer_actionGroup_le_normalizer_derivedGroup)

/-- The actual conjugation action on the commutator subgroup. -/
def derivedConjugation : actionGroup →* MulAut derivedGroup :=
  derivedGroup.normalizerMonoidHom.comp toDerivedNormalizer

/-- Conjugation descends to the actual quotient by the center of the core. -/
def derivedQuotientConjugation : actionGroup →*
    MulAut (derivedGroup ⧸ Subgroup.center derivedGroup) :=
  (Subgroup.quotientAut (Subgroup.center derivedGroup)).comp derivedConjugation

theorem derivedConjugation_apply (h : actionGroup) (k : derivedGroup) :
    ((derivedConjugation h k : derivedGroup) : Matrix12ˣ) =
      (h : Matrix12ˣ) * (k : Matrix12ˣ) * (h : Matrix12ˣ)⁻¹ := rfl

/-- A proved centralizer calculation reduces self-normalization to perfect-core data. -/
theorem actionGroup_selfNormalizer_of_perfect_quotient_coverage
    [Group.IsPerfect derivedGroup]
    (hcover : Function.Surjective derivedQuotientConjugation) :
    Subgroup.normalizer (actionGroup : Set Matrix12ˣ) ≤ actionGroup := by
  intro g hg
  let n : Subgroup.normalizer (derivedGroup : Set Matrix12ˣ) :=
    ⟨g, normalizer_actionGroup_le_normalizer_derivedGroup hg⟩
  obtain ⟨h, hh⟩ := hcover
    (Subgroup.quotientAut (Subgroup.center derivedGroup) (derivedGroup.normalizerMonoidHom n))
  have heq : derivedConjugation h = derivedGroup.normalizerMonoidHom n :=
    MulAut.quotient_center_injective hh
  have hker : (toDerivedNormalizer h)⁻¹ * n ∈ derivedGroup.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (derivedConjugation h)⁻¹ * derivedGroup.normalizerMonoidHom n = 1
    rw [heq, inv_mul_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  have hc : (h : Matrix12ˣ)⁻¹ * g ∈ actionGroup := centralizer_derivedGroup_le hker
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using actionGroup.mul_mem h.property hc

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
