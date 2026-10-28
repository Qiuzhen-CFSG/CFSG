module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar.LowRank
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar.HigherSymplectic.Reduction

/-!
# Higher symplectic fixer assembly through maximal Sylow overgroups

The full automorphism fixer is a two-group once the actual projective carrier
has the proper Sylow-overgroup Fitting bound and two distinct maximal
subgroups containing a common Sylow two-subgroup. The imported reduction
proves normalization under arbitrary pointwise fixers, the full displacement
kernel bound, and generation by those maximal subgroups.

This module transports that conditional conclusion across an actual PSp
isomorphism and applies it to the literal central quotient of a component.
The higher symplectic family is not yet discharged: both the Fitting-bound
producer and the geometric parabolic-pair producer remain required, including
rank three over the two-element field. Simplicity and perfectness are inherited
from the source component, rather than proved again for each carrier.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 of `refs/quasithin.pdf`;
GLS3 §2.6–2.7 for symplectic parabolics and the projective convention.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupAction.NormalizerGeneratingFixer
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar

/-- An actual symplectic model transports the conditional full-fixer bound.
Both remaining geometric and local-structure premises are explicit. -/
theorem higherSymplectic_equiv_fixer_of_overgroups {X : Type*}
    [Group X] [Finite X] [IsSimpleGroup X] [Group.IsPerfect X]
    (r : ℕ) (F : Type*) [Field F] [Finite F]
    (e : X ≃* ClassicalGroup.PSp r F)
    (hfit : ProperSylowFittingBound (ClassicalGroup.PSp r F))
    (hgeom : HasTwoMaximalOvergroups 2 (ClassicalGroup.PSp r F)) :
    SylowFixerIsTwoGroup X := by
  let : IsSimpleGroup (ClassicalGroup.PSp r F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ClassicalGroup.PSp r F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact fixer_of_equiv e (fixer_of_properFitting_of_two_maximals hfit hgeom)

/-- The conditional symplectic calculation discharges precisely the full fixer
premise in the literal component-central-quotient application of B.1.13. -/
theorem higherSymplectic_le_component_of_overgroups {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥)
    (r : ℕ) (F : Type*) [Field F] [Finite F]
    (e : (L ⧸ center L) ≃* ClassicalGroup.PSp r F)
    (hfit : ProperSylowFittingBound (ClassicalGroup.PSp r F))
    (hgeom : HasTwoMaximalOvergroups 2 (ClassicalGroup.PSp r F)) : K ≤ L := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (higherSymplectic_equiv_fixer_of_overgroups r F e hfit hgeom) hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar
