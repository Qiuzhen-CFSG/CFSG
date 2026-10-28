module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
/-!
# One-point separation for the five-normalizer

In the derived Sylow normal form, normalizing the literal rotation s₁r₁
forces all coordinates except s₁ and s₅ to vanish. Equality on Atlas point
zero already proves the restriction; no subgroup-lattice enumeration is used.
The full-group calculation subsequently corrects the outer coset by the
specified relative-root element. Source: Aschbacher--Smith J.4.7, p.442.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.NormalizerCertificate
open Tits.OuterOddSubgroups.OverlapCentralizers
private def nf (n : Nat) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n % 2) * Packed.perm 3 ^ (n / 2 % 2) *
  Packed.perm 4 ^ (n / 4 % 4) * Packed.perm 5 ^ (n / 16 % 2) *
  Packed.perm 6 ^ (n / 32 % 4) * Packed.perm 7 ^ (n / 128 % 2) *
  Packed.perm 8 ^ (n / 256 % 4) * Packed.perm 9 ^ (n / 1024 % 2)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem separation : ∀ (n : Fin 2048) (k : Fin 5),
    (nf n.val * (Packed.perm 2 * Packed.perm 0)) 0 =
      ((Packed.perm 2 * Packed.perm 0)^k.val * nf n.val) 0 →
    n.val = n.val % 2 + 32 * (n.val / 32 % 4) := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

/-- The actual Sylow word of a normalizer has only the s₁ and s₅ coordinates. -/
theorem normalForm_coordinates (n : Fin 2048) (k : Fin 5)
    (h : Atlas1600SylowTwoCertificate.normalForm n *
        (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm) =
      (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm)^k.val *
        Atlas1600SylowTwoCertificate.normalForm n) :
    n.val = n.val % 2 + 32 * (n.val / 32 % 4) := by
  apply separation n k
  have hp := congrArg (fun f : Equiv.Perm (Fin 1600) => f 0) h
  simpa only [nf, Packed.perm_eq, Packed.generator,
    Atlas1600SylowTwoCertificate.normalForm, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] using hp

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.NormalizerCertificate
