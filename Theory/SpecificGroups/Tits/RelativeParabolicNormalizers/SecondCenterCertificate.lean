module

public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoCenterCertificate

/-!
# Generator actions on two Sylow words

The second parabolic reflection interchanges r5 and s1*s2*s3². Each
Sylow generator fixes the latter word, except s8, which multiplies it
by r5. These permutation identities are checked on all 1600 points
by the Lean kernel. They certify the normal two-subgroup used by the
local-core argument; GAP diagnostics are not premises.

Source: Parrott (1972), p.683, in the checked Atlas generator conventions.
-/

@[expose] public section

namespace Tits.RelativeParabolicNormalizers.SecondCenterCertificate
open Atlas1600ParrottData Atlas1600SylowTwoCertificate
set_option maxRecDepth 20000

def x : Equiv.Perm (Fin 1600) := s1Perm * s5Perm ^ 2
def y : Equiv.Perm (Fin 1600) := s1Perm * s2Perm * s3Perm ^ 2

set_option maxHeartbeats 1600000 in
theorem reflection_x : r8Perm * x * r8Perm⁻¹ = y := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
theorem reflection_y : r8Perm * y * r8Perm⁻¹ = x := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
theorem sylow_y (i : Fin 8) :
    Atlas1600SylowTwoCenterCertificate.generator i * y *
      (Atlas1600SylowTwoCenterCertificate.generator i)⁻¹ =
    if i = 7 then x * y else y := by
  apply Equiv.ext
  revert i
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel
end Tits.RelativeParabolicNormalizers.SecondCenterCertificate

end
