module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions.Coverage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions.Transport
/-!
# Large fixed spaces force an elementary Mathieu image

Every element of the actual star Sylow either squares to one or is conjugate
to one of 35 checked representatives fixing at most sixteen kernel masks.
Consequently any subgroup fixing more than sixteen masks has exponent two,
and hence is elementary abelian. No normality is assumed. This is the local
fixed-space sieve for the large-center radical rows of An--O'Brien--Wilson
(2003), Section 4 and Table 1, using the literal ATLAS max1 action.
-/
public section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
open SylowCore SylowCore.FiniteBoundCertificate
open SylowCore.FiniteBoundCertificate.NormalWeights
open Simplicity.Max1Fusion.QuotientInvolutions

private theorem representative_fixed_bound (k : Fin 35) :
    Nat.card {m : Fin 2048 // starMask (element (representatives k)).val m.val = m.val} ≤ 16 := by
  change Nat.card {m : Fin 2048 // Cardinality.QuotientCount.Image.maskImage
    (rows (representatives k)) m.val = m.val} ≤ 16
  rw [cachedRows_valid]
  exact representative_bounds k

/-- A non-involutory member bounds the entire subgroup's fixed masks by sixteen. -/
theorem fixed_bound_of_square_ne_one (B : Subgroup sylowCandidate) (x : B)
    (hne : x ^ 2 ≠ 1) : Nat.card (FixedMasks B) ≤ 16 := by
  obtain ⟨i,hi⟩ := element_bijective.surjective x.val
  rcases coverage i with hs | hc
  · exfalso
    apply hne
    apply Subtype.ext
    change x.val ^ 2 = 1
    rw [← hi]
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    exact hs
  · exact (fixed_le_single B i (hi.symm ▸ x.property)).trans
      ((single_fixed_conjugates i _ _ hc).trans_le (representative_fixed_bound _))

/-- The fixed-space threshold forces exponent two without a normality hypothesis. -/
theorem elementary_of_large_fixed (B : Subgroup sylowCandidate)
    (hlarge : 16 < Nat.card (FixedMasks B)) : IsElementaryAbelian 2 B := by
  have hs (x : B) : x ^ 2 = 1 := by
    by_contra hn
    exact (not_le_of_gt hlarge) (fixed_bound_of_square_ne_one B x hn)
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hs c)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
