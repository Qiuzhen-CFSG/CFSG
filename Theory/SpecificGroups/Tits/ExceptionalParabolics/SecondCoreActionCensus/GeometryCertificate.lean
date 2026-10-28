module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Images
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondCenterCertificate

/-!
# Point certificates for the center of the second Tits core

Commutation with the two known second-center words puts a three-coset normal
form among the first 1024 Sylow words. Commutation with s3 and s7 leaves only
indices 0, 11, 65, 74. These are necessary point tests, checked by the kernel;
the symbolic consumer separately proves membership and sufficiency.

Source: Parrott (1972), §5, p.683, in the existing Atlas1600 marking; used for
Aschbacher--Smith F.1.12 and14.2.21, printed pp.263 and988--989.
-/

@[expose] public section
open Tits Tits.AmalgamRigidity.SecondExtension
namespace Tits.ExceptionalParabolics.SecondCoreAction.GeometryCertificate
private def cx : Equiv.Perm (Fin 1600) := packedGen 1 * packedGen 5 ^ 2
private def cy : Equiv.Perm (Fin 1600) := packedGen 1 * packedGen 2 * packedGen 3 ^ 2
def commutesZero (w g : Equiv.Perm (Fin 1600)) : Bool := w (g 0) == g (w 0)
set_option maxRecDepth 20000 in
private theorem packed_centralizer_candidates (n : Fin 2048) (i : Fin 3) :
    commutesZero (word packedGen n * rep packedGen i) cx = true →
    commutesZero (word packedGen n * rep packedGen i) cy = true →
    n.val < 1024 ∧ i = 0 := by
  revert n i
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel
theorem centralizer_candidates (n : Fin 2048) (i : Fin 3) :
    commutesZero (word packedGen n * rep packedGen i)
      RelativeParabolicNormalizers.SecondCenterCertificate.x = true →
    commutesZero (word packedGen n * rep packedGen i)
      RelativeParabolicNormalizers.SecondCenterCertificate.y = true →
    n.val < 1024 ∧ i = 0 := by
  have hx : cx = RelativeParabolicNormalizers.SecondCenterCertificate.x := by
    simp only [cx, packedGen, OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
      OuterOddSubgroups.OverlapCentralizers.Packed.generator,
      RelativeParabolicNormalizers.SecondCenterCertificate.x]
    rfl
  have hy : cy = RelativeParabolicNormalizers.SecondCenterCertificate.y := by
    simp only [cy, packedGen, OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
      OuterOddSubgroups.OverlapCentralizers.Packed.generator,
      RelativeParabolicNormalizers.SecondCenterCertificate.y]
    rfl
  simpa only [hx, hy] using packed_centralizer_candidates n i

set_option maxRecDepth 20000 in
theorem center_candidates (n : Fin 2048) :
    commutesZero (word packedGen n) (packedGen 3) = true →
    commutesZero (word packedGen n) (packedGen 7) = true →
    n = 0 ∨ n = 11 ∨ n = 65 ∨ n = 74 := by
  revert n
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
end Tits.ExceptionalParabolics.SecondCoreAction.GeometryCertificate
