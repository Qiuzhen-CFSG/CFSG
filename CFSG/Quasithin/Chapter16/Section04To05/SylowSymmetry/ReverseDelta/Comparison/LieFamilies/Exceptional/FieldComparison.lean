module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.Arithmetic
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.Rows
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Residual

/-!
# Excluding the exceptional field-involution rows

For G₂(2^f), an outer involution forces f = 2m and has residual G₂(2^m)′.
Its odd divisor (2^m)^6-1 is larger than the inner centralizer's odd bound
(2^f)^2-1. The known G₂ order and its proved two-residual identity supply
this divisor, including the proper derived group when m = 1.

For genuine triality the same argument uses the explicitly supplied divisor
(q^8+q^4+1)(q^6-1), which is larger than q^12-1. Only the consumed local
table rows and that precise smaller-model divisor remain inputs. Both
arguments pass through central two-kernels, including the G₂(4) covers.

Source: Aschbacher--Smith, 16.1.2--4, printed pp.1170--1171, and the
comparison in 16.4.11(2), p.1193, combined manuscript (1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory LiePreliminaries Exceptional

private theorem binary_lower_bound {m : ℕ} (hm : 0 < m) : 2 ≤ 2 ^ m := by
  have h : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  simpa using h

private theorem positive_odd_bound {q : ℕ} (hq : 2 ≤ q) {k : ℕ} (hk : 0 < k) :
    0 < q ^ k - 1 := by
  have h : q ^ 0 < q ^ k := Nat.pow_lt_pow_right (by omega) hk
  simpa using Nat.sub_pos_of_lt h

private theorem g2_derived_odd_divisor {m : ℕ} (hm : 0 < m) :
    (2 ^ m) ^ 6 - 1 ∣ Nat.card (commutator (Atlas.G2.Model (GaloisField 2 m))) := by
  rw [← Atlas.G2.EvenFieldFixedResidual.twoResidual_eq_commutator]
  apply (odd_dvd_residual_iff (binary_power_sub_one_odd hm (by decide))).mpr
  rw [Atlas.G2.card_Model, GaloisField.card 2 m (Nat.ne_of_gt hm)]
  refine ⟨(2 ^ m) ^ 6 * ((2 ^ m) ^ 2 - 1), ?_⟩
  ring

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The G₂ comparison retains arbitrary source central two-covers. -/
theorem not_g2_model (d : Contrary T z L g R r)
    {F : Type*} [Field F] [Finite F] {f : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model F) (rows : G2InvolutionRows F f) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨_, _, _, hi⟩ := rows.inner_root (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  obtain ⟨m, hm, hfm, _, ⟨eo⟩⟩ := rows.outer_field (outerAction d c)
    (outerAction_order d c) (outerAction_outer d c)
  have hp : 2 ^ f = (2 ^ m) ^ 2 := by rw [hfm, Nat.mul_comm, pow_mul]
  have hi' : ∃ k : ℕ, Nat.card (innerAction d c).fixedSubgroup ∣
      2 ^ k * ((2 ^ m) ^ 4 - 1) := by
    simpa only [hp, ← pow_mul, Nat.mul_assoc, Nat.reduceMul] using hi
  apply false_of_odd_bound d c (binary_power_sub_one_odd hm (by decide))
    (positive_odd_bound (binary_lower_bound hm) (by decide))
    (g2_odd_bound (binary_lower_bound hm)) hi'
  rw [Nat.card_congr eo.toEquiv]
  exact g2_derived_odd_divisor hm

/-- The exact G₂ constructor of Theorem C, with its field witness preserved. -/
theorem not_g2_quotient (d : Contrary T z L g R r) (table : G2InvolutionTable)
    {f : ℕ} (hf : 2 ≤ f)
    (h : ClassificationModels.IsG2At (L ⧸ pCore 2 L) (2 ^ f)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  exact not_g2_model d e (table F f hf hcard)

/-- Triality uses the genuine D₄ graph-field carrier, including f = 1.
Its outer row itself forces an even positive field exponent. -/
theorem not_triality_model (d : Contrary T z L g R r) {f : ℕ} (hf : 0 < f)
    (e : (L ⧸ pCore 2 L) ≃* Triality.Standard.BinaryCarrier f hf)
    (rows : TrialityInvolutionRows f hf) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨_, _, _, hi⟩ := rows.inner_root (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  obtain ⟨m, hm, hfm, _, ⟨eo⟩⟩ := rows.outer_field (outerAction d c)
    (outerAction_order d c) (outerAction_outer d c)
  have hp : 2 ^ f = (2 ^ m) ^ 2 := by rw [hfm, Nat.mul_comm, pow_mul]
  have hi' : ∃ k : ℕ, Nat.card (innerAction d c).fixedSubgroup ∣
      2 ^ k * ((2 ^ m) ^ 12 - 1) := by
    simpa only [hp, ← pow_mul, Nat.mul_assoc, Nat.reduceMul] using hi
  have he : Even (2 ^ m) := even_two.pow_of_ne_zero (Nat.ne_of_gt hm)
  have hsum : Odd ((2 ^ m) ^ 8 + (2 ^ m) ^ 4 + 1) :=
    ((he.pow_of_ne_zero (by decide)).add (he.pow_of_ne_zero (by decide))).add_one
  apply false_of_odd_bound d c
    (hsum.mul (binary_power_sub_one_odd hm (by decide)))
    (positive_odd_bound (binary_lower_bound hm) (by decide))
    (triality_odd_bound (binary_lower_bound hm)) hi'
  rw [Nat.card_congr eo.toEquiv]
  exact rows.smaller_odd_divisor m hm hfm

/-- The standard triality family predicate is transported by its proved
binary specialization, never by the auxiliary matrix construction. -/
theorem not_triality_quotient (d : Contrary T z L g R r)
    (table : TrialityInvolutionTable) {f : ℕ} (hf : 1 ≤ f)
    (h : Triality.Standard.IsTrialityGroupAt (2 ^ f) (L ⧸ pCore 2 L)) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp h
  exact not_triality_model d hf e (table f hf)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
