module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.TensorRank.Prefix
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.TensorRank.PeriodicCount

/-!
# Periodic exceptional-tensor involution ranks

Let `n = 2*m+1` and let `s > 0` divide `n`. If the dimensions of the
actual exceptional factors repeat under shift `2*s`, at least one is at
least 26, and every factor of dimension at least 26 has cyclic fixed
codimension at least 10, then the actual exceptional tensor has fixed
codimension at least `10*26^(n/s-1)`. Consequently `10*n` is at most `s`
times its cyclic fixed codimension.

The rank calculation uses `Representation.tprod` and the existing
`tensorPrefix` in its original order. Only the numerical factor count is
reindexed. The three factor premises are explicit: their producers are
tensor classification/Frobenius periodicity, the basic minimum, and the
basic-involution calculation. The unconditional Ree estimate must discharge
those premises separately. The argument also covers `m = 0` and `s = n`.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Corollary
2.11(a), internal p.10, and Lemma 8.8; GLS3, Corollary 2.8.6(b) and
Remark 2.8.8 for the exceptional tensor order and Frobenius periods.
-/

public section

open Module Representation
open Representation.BinaryOffender.NaturalTensor
open Representation.TensorInvolutionDisplacement
open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor

namespace ReeF4.FixedSpaceEstimate

universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The exponential estimate for the literal exceptional tensor and cyclic fixed space. -/
theorem exceptionalTensor_cyclicFixedCodim_ge_pow {m : ℕ}
    (ι : SplitGroup m →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (t : Model m) (ht : t ^ 2 = 1) {s : ℕ} (hs : 0 < s) (hsn : s ∣ 2 * m + 1)
    (hlarge : ∃ i, 26 ≤ finrank F (B i).Space)
    (hshift : ∀ i, finrank F (B (i + 2 * (s : ZMod (2 * m + 1)))).Space =
      finrank F (B i).Space)
    (hrank : ∀ i, 26 ≤ finrank F (B i).Space →
      10 ≤ finrank F ((exceptionalFactor ι B i) ⧸
        invariants ((exceptionalFactor ι B i).ρ.comp (Subgroup.zpowers t).subtype))) :
    10 * 26 ^ ((2 * m + 1) / s - 1) ≤
      finrank F ((exceptionalTensor ι B) ⧸
        invariants ((exceptionalTensor ι B).ρ.comp (Subgroup.zpowers t).subtype)) := by
  let V : ℕ → FDRep F (Model m) := fun i => exceptionalFactor ι B (i : ZMod (2 * m + 1))
  have hcount : (2 * m + 1) / s ≤ largeFactorCount V 26 (2 * m + 1) :=
    periodic_large_count_ge m s 26 hs hsn (fun i => finrank F (B i).Space) hlarge hshift
  have hq : 0 < (2 * m + 1) / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsn) hs
  have hp : ∀ i, 0 < finrank F (V i) := fun i => (B (i : ZMod (2 * m + 1))).finrank_pos
  have hr : ∀ i, 26 ≤ finrank F (V i) → 10 ≤ operatorFixedCodim ((V i).ρ t) := by
    intro i hi
    rw [operatorFixedCodim_eq_cyclicFixedCodim]
    exact hrank _ hi
  have hb := tensorPrefix_displacement_ge_pow V t ht 26 10 hp hr (2 * m + 1)
    (hq.trans_le hcount)
  rw [operatorFixedCodim_eq_cyclicFixedCodim] at hb
  exact (Nat.mul_le_mul_left 10
    (Nat.pow_le_pow_right (by decide : 0 < 26) (Nat.sub_le_sub_right hcount 1))).trans hb

/-- The period-scaled Ree tensor estimate, conditional on the three factor premises. -/
theorem exceptionalTensor_periodic_fixedCodim_bound {m : ℕ}
    (ι : SplitGroup m →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (t : Model m) (ht : t ^ 2 = 1) {s : ℕ} (hs : 0 < s) (hsn : s ∣ 2 * m + 1)
    (hlarge : ∃ i, 26 ≤ finrank F (B i).Space)
    (hshift : ∀ i, finrank F (B (i + 2 * (s : ZMod (2 * m + 1)))).Space =
      finrank F (B i).Space)
    (hrank : ∀ i, 26 ≤ finrank F (B i).Space →
      10 ≤ finrank F ((exceptionalFactor ι B i) ⧸
        invariants ((exceptionalFactor ι B i).ρ.comp (Subgroup.zpowers t).subtype))) :
    10 * (2 * m + 1) ≤ s *
      finrank F ((exceptionalTensor ι B) ⧸
        invariants ((exceptionalTensor ι B).ρ.comp (Subgroup.zpowers t).subtype)) := by
  have hq : 0 < (2 * m + 1) / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsn) hs
  have hbound := exceptionalTensor_cyclicFixedCodim_ge_pow ι B t ht hs hsn hlarge hshift hrank
  have hl := (Nat.mul_le_mul_left 10 (le_pow_pred (by decide : 2 ≤ 26) hq)).trans hbound
  calc
    10 * (2 * m + 1) = s * (10 * ((2 * m + 1) / s)) := by
      rw [mul_left_comm s 10, Nat.mul_div_cancel' hsn]
    _ ≤ _ := Nat.mul_le_mul_left s hl

end ReeF4.FixedSpaceEstimate
