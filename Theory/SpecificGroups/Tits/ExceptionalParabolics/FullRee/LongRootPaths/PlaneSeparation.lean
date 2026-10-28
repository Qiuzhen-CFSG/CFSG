module
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
/-!
# Separation of the two noncentral marks inside the first endpoint

For every certified derived first-parabolic normal form, its conjugate of
s1 differs from s5² already on Atlas point zero. The full endpoint proof
corrects the outside derived coset by q, which commutes with both marks.
The representative 256-by-5 block measured 21.69s and 1.87GiB including
import preparation; this single certificate reuses the existing packed maps.
Source: the normalizer action needed for the direct J.4.10 parabolic graph.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.PlaneSeparation
open Tits.OuterOddSubgroups.OverlapCentralizers
private def nf (n : Nat) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n % 2) * Packed.perm 3 ^ (n / 2 % 2) *
  Packed.perm 4 ^ (n / 4 % 4) * Packed.perm 5 ^ (n / 16 % 2) *
  Packed.perm 6 ^ (n / 32 % 4) * Packed.perm 7 ^ (n / 128 % 2) *
  Packed.perm 8 ^ (n / 256 % 4) * Packed.perm 9 ^ (n / 1024 % 2)
set_option maxRecDepth 20000 in
private theorem separation : ∀ (n : Fin 2048) (k : Fin 5),
    (nf n.val * (Packed.perm 2 * Packed.perm 0)^k.val * Packed.perm 2) 0 ≠
      (Packed.perm 6^2 * (nf n.val * (Packed.perm 2 * Packed.perm 0)^k.val)) 0 := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

/-- No first-parabolic Sylow word times a rotation power sends s1 to s5². -/
theorem normalForm_no_switch (n : Fin 2048) (k : Fin 5)
    (h : Atlas1600SylowTwoCertificate.normalForm n *
      (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm)^k.val *
      Atlas1600ParrottData.s1Perm = Atlas1600ParrottData.s5Perm^2 *
      (Atlas1600SylowTwoCertificate.normalForm n *
        (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm)^k.val)) : False := by
  apply separation n k
  have hp := congrArg (fun f : Equiv.Perm (Fin 1600) => f 0) h
  simpa only [nf, Packed.perm_eq, Packed.generator,
    Atlas1600SylowTwoCertificate.normalForm, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] using hp
end Tits.ExceptionalParabolics.FullRee.LongRootPaths.PlaneSeparation
