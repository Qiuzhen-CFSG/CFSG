module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore.Normalization
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore

/-!
# The integral normalization bound for the literal HS core displacements

Apply the integral cocycle calculation to the errors of the given section in
the actual central kernel. The corrected section leaves only one involution,
so the intersection of the core displacement subgroup with the kernel has
order at most two. The literal action certificate remains the sole additional
input and is constructed independently.

Source: the integral module step for Aschbacher–Smith I.1.3(1), p.407,
and the normalizer in I.2.2(5), p.412; GLS3 Table 5.3m.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Sporadic.LeechRelated.HS BlockNormalizer

/-- The actual displacement-kernel bound, conditional only on the published
integral action certificate beyond the central cover and its core section. -/
theorem card_coreDisplacements_inf_ker_le_of_integralActionData
    (h : IntegralActionData) {D : Type*} [Group D] [Finite D]
    (g : D →* baseNormalizer) (hg : Function.Surjective g)
    (hk : g.ker ≤ center D) (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype) :
    Nat.card (coreDisplacements g ⊓ g.ker : Subgroup D) ≤ 2 :=
  card_coreDisplacements_inf_ker_le_of_cyclic_error g hg hk s hs
    (CoreCrossedHom.hasCyclicError h (sectionCrossedHom g hg hk s hs))

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
