module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.Consequences
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.Residual
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.ModelExclusions
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.Models

/-!
# The dihedral Sylow branch of the M₂₂ shadow

For T_C = ⟨z⟩ and R = ⟨r⟩, the earlier local stability and generation
statements give T⁺ = T_L⁺, a dihedral Sylow subgroup of M⁺ of order eight.
The local two-residual has image A₅. The fixed-line argument is also proved,
conditional on normality of this residual image in M⁺. Concrete order
exclusions eliminate the proper PSL₂ and J₁ models and every candidate
whose order is divisible by sixteen.

The branch still requires the source component placement, the complete
A.3.14 sieve, and the marked A₇ representation recognition. In particular
this module does not assert the source contradiction or take it as an input.
The faithful image is the range of the actual shadowAction, whose quotient
and relative centralizer kernel are identified in Setup.

Source: Aschbacher–Smith, proof of Lemma 16.4.7, final paragraph,
printed p.1187 (PDF p.1204).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase

variable {G : Type*} [Group G] [Finite G]

/-- The Sylow conclusion in the actual T_C = ⟨z⟩ branch. The generation
and T_L-stability inputs are preceding local geometry, not Sylow-image
or dihedral-recognition assumptions. -/
theorem sylow_of_commutingSylow_eq_zpowers (L R : Subgroup G) (g r z : G)
    (T : Sylow 2 G) [IsMulCommutative (shadowSpace L r z)]
    (hTL : componentSylow T L ≤ normalizer (shadowSpace L r z : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hgen : (T : Subgroup G) = (componentSylow T L ⊔ commutingSylow T L) ⊔ R)
    (hTC : commutingSylow T L = zpowers z) (hR : R = zpowers r)
    (e : imageSubgroup L g r z (localNormalizer L r z) ≃* Equiv.Perm (Fin 5)) :
    ∃ S : Sylow 2 (Image L g r z),
      (S : Subgroup (Image L g r z)) = imageSubgroup L g r z T ∧
      imageSubgroup L g r z T = imageSubgroup L g r z (componentSylow T L) ∧
      Nonempty (S ≃* DihedralGroup 4) := by
  apply sylow_dihedral L g r z T hTL hTN _ e
  simpa only [hTC, hR, sup_assoc] using hgen

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
