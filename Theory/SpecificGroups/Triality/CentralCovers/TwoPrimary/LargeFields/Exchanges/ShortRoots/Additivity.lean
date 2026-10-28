module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.LongRoots

/-!
# Additivity of the triality polynomial conjugation words

The trace exchanges supply the polar terms of the quadratic trace in the
short0/short1 word. For short0/long0, collecting two candidate words supplies
the polar terms of sF(s) and N(s); the remaining highest-root trace cancels
in characteristic two. These are identities in the extension using the
explicit commuting and earlier exchange relations, without assuming that
projection is injective.

Source: the polynomial coefficients of GLS3 §2.4.5(b)(4),(5), used in the
central-cover argument of §6.1 and Aschbacher–Smith I.1.3.
-/

set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section
namespace Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
open Parabolics RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn
local notation "F" => fieldFrobenius P
local notation "T" => cubicTrace P

theorem short_add (L : RootSections n hn f) (i : Fin 3) (s t : ExtensionField P) :
    L.shortValue i (s+t) = L.shortValue i s * L.shortValue i t := (L.shortRoot i).map_mul _ _
theorem long_add (L : RootSections n hn f) (i : Fin 3) (s t : fixedField P) :
    L.longValue i (s+t) = L.longValue i s * L.longValue i t := (L.longRoot i).map_mul _ _
theorem short_inv (L : RootSections n hn f) (i : Fin 3) (s : ExtensionField P) :
    (L.shortValue i s)⁻¹ = L.shortValue i s := by
  change (L.shortRoot i (.ofAdd s))⁻¹ = _
  rw [← map_inv]; exact congrArg (L.shortRoot i) (congrArg Multiplicative.ofAdd (CharTwo.neg_eq s))
theorem long_inv (L : RootSections n hn f) (i : Fin 3) (s : fixedField P) :
    (L.longValue i s)⁻¹ = L.longValue i s := by
  change (L.longRoot i (.ofAdd s))⁻¹ = _
  rw [← map_inv]; exact congrArg (L.longRoot i) (congrArg Multiplicative.ofAdd (CharTwo.neg_eq s))
theorem append_relation {a b c : E} (h : a*b = c) (z : E) :
    a*(b*z) = c*z := by rw [← mul_assoc, h]
theorem join_short (L : RootSections n hn f) (i : Fin 3) (s t : ExtensionField P) (z : E) :
    L.shortValue i s*(L.shortValue i t*z) = L.shortValue i (s+t)*z := by
  rw [← mul_assoc, ← short_add]
theorem join_long (L : RootSections n hn f) (i : Fin 3) (s t : fixedField P) (z : E) :
    L.longValue i s*(L.longValue i t*z) = L.longValue i (s+t)*z := by
  rw [← mul_assoc, ← long_add]
theorem reverse_trace (L : RootSections n hn f) (i j : Fin 3)
    (h : ∀ s t, L.shortValue i s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue i s * L.longValue j (T (F (F s)*t))) (s t : ExtensionField P) :
    L.shortValue 2 t * L.shortValue i s =
      L.shortValue i s * L.shortValue 2 t * L.longValue j (T (F (F s)*t)) := by
  have he := (eq_mul_inv_iff_mul_eq.mpr (h s t).symm)
  simpa only [long_inv] using he

theorem candidate01_add (L : RootSections n hn f) (hC : L.CommutingRelations)
    (h02 : ∀ s t, L.shortValue 0 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 0 s * L.longValue 1 (T (F (F s)*t)))
    (t s u : ExtensionField P) :
    L.shortValue 0 (s+u) * L.shortValue 2 (higherCoefficient P (s+u) t) *
      L.longValue 1 (T ((s+u)*F (s+u)*F (F t))) *
      L.longValue 2 (T ((s+u)*F t*F (F t))) =
    (L.shortValue 0 s * L.shortValue 2 (higherCoefficient P s t) *
      L.longValue 1 (T (s*F s*F (F t))) * L.longValue 2 (T (s*F t*F (F t)))) *
    (L.shortValue 0 u * L.shortValue 2 (higherCoefficient P u t) *
      L.longValue 1 (T (u*F u*F (F t))) * L.longValue 2 (T (u*F t*F (F t)))) := by
  simp only [mul_assoc, append_relation (hC.short0_long1 _ _).symm.eq,
    append_relation (hC.short0_long2 _ _).symm.eq,
    append_relation (hC.short2_long1 _ _).symm.eq,
    append_relation (hC.short2_long2 _ _).symm.eq,
    append_relation (hC.long1_long2 _ _).symm.eq,
    append_relation (reverse_trace L 0 1 h02 _ _), join_short, join_long, ← long_add]
  repeat' first
    | apply congrArg₂ (fun a b : E => a*b)
    | apply congrArg (L.shortValue _)
    | apply congrArg (L.longValue _)
  all_goals first
    | rfl
    | (apply Subtype.ext
       simp only [higherCoefficient, cubicTrace_coe, Subfield.coe_add, map_add, map_mul,
         fieldFrobenius_three]
       ring)
    | (simp only [higherCoefficient, map_add, map_mul]; ring)

theorem reverse01 (L : RootSections n hn f) (hC : L.CommutingRelations)
    (h01 : ∀ s t, L.shortValue 0 s * L.shortValue 1 t =
      L.shortValue 1 t * L.shortValue 0 s * L.shortValue 2 (higherCoefficient P s t) *
        L.longValue 1 (T (s*F s*F (F t))) * L.longValue 2 (T (s*F t*F (F t))))
    (s t : ExtensionField P) :
    L.shortValue 1 t * L.shortValue 0 s =
      L.shortValue 0 s * L.shortValue 1 t * L.shortValue 2 (higherCoefficient P s t) *
        L.longValue 1 (T (s*F s*F (F t))) * L.longValue 2 (T (s*F t*F (F t))) := by
  have he : L.shortValue 0 s * L.shortValue 1 t =
      (L.shortValue 1 t * L.shortValue 0 s) *
      (L.shortValue 2 (higherCoefficient P s t) * L.longValue 1 (T (s*F s*F (F t))) *
        L.longValue 2 (T (s*F t*F (F t)))) := by simpa only [mul_assoc] using h01 s t
  have hi := eq_mul_inv_iff_mul_eq.mpr he.symm
  simp only [mul_inv_rev, short_inv, long_inv] at hi
  rw [(hC.short2_long1 _ _).symm.eq, (hC.short2_long2 _ _).symm.left_comm,
    (hC.long1_long2 _ _).symm.eq] at hi
  simpa only [mul_assoc] using hi

theorem candidate00_add (L : RootSections n hn f) (hC : L.CommutingRelations)
    (h02 : ∀ s t, L.shortValue 0 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 0 s * L.longValue 1 (T (F (F s)*t)))
    (h12 : ∀ s t, L.shortValue 1 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 1 s * L.longValue 2 (T (F (F s)*t)))
    (h01 : ∀ s t, L.shortValue 0 s * L.shortValue 1 t =
      L.shortValue 1 t * L.shortValue 0 s * L.shortValue 2 (higherCoefficient P s t) *
        L.longValue 1 (T (s*F s*F (F t))) * L.longValue 2 (T (s*F t*F (F t))))
    (t : fixedField P) (s u : ExtensionField P) :
    L.shortValue 0 (s+u) * L.shortValue 1 ((s+u)*t.val) *
      L.shortValue 2 ((s+u)*F (s+u)*t.val) * L.longValue 1 (cubicNorm P (s+u)*t) =
    (L.shortValue 0 s * L.shortValue 1 (s*t.val) *
      L.shortValue 2 (s*F s*t.val) * L.longValue 1 (cubicNorm P s*t)) *
    (L.shortValue 0 u * L.shortValue 1 (u*t.val) *
      L.shortValue 2 (u*F u*t.val) * L.longValue 1 (cubicNorm P u*t)) := by
  have ht : F t.val = t.val := t.property
  simp only [mul_assoc, append_relation (hC.short0_long1 _ _).symm.eq,
    append_relation (hC.short0_long2 _ _).symm.eq,
    append_relation (hC.short1_long1 _ _).symm.eq,
    append_relation (hC.short1_long2 _ _).symm.eq,
    append_relation (hC.short2_long1 _ _).symm.eq,
    append_relation (hC.short2_long2 _ _).symm.eq,
    append_relation (hC.long1_long2 _ _).symm.eq,
    append_relation (reverse_trace L 0 1 h02 _ _),
    append_relation (reverse_trace L 1 2 h12 _ _),
    append_relation (reverse01 L hC h01 _ _), join_short, join_long, ← long_add]
  rw [(hC.long1_long2 _ _).symm.eq]
  simp only [← mul_assoc, ← long_add]
  have hz : T (F (F (u*t.val))*higherCoefficient P u (s*t.val)) +
      (T (u*(F (s*t.val)*F (F (s*t.val)))) + T (F (F (u*t.val))*(s*(F s*t.val)))) = 0 := by
    apply Subtype.ext
    simp only [higherCoefficient, cubicTrace_coe, Subfield.coe_add, Subfield.coe_zero,
      map_add, map_mul, ht, fieldFrobenius_three]
    ring_nf
    have htwo : (2 : ExtensionField P) = 0 := CharTwo.two_eq_zero
    simp only [htwo, mul_zero, add_zero]
  simp only [← mul_assoc] at hz
  rw [hz]
  rw [show L.longValue 2 0 = 1 from (L.longRoot 2).map_one, mul_one]
  change L.shortValue 0 (s+u) * L.shortValue 1 ((s+u)*t.val) *
      L.shortValue 2 ((s+u)*F (s+u)*t.val) * L.longValue 1 (cubicNorm P (s+u)*t) = _
  repeat' first
    | apply congrArg₂ (fun a b : E => a*b)
    | apply congrArg (L.shortValue _)
    | apply congrArg (L.longValue _)
  all_goals first
    | rfl
    | (apply Subtype.ext
       simp only [higherCoefficient, cubicNorm, cubicTrace_coe, Subfield.coe_add,
         Subfield.coe_mul, map_add, map_mul, ht, fieldFrobenius_three]
       ring)
    | (try simp only [higherCoefficient, map_add, map_mul, ht]
       ring)
end Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
