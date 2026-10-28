module
public import Theory.Representation.BinaryPairedTransvections.Exchange
public import Theory.Representation.BinaryPairedTransvections.Extraspecial
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Order of the paired binary transvection group

On a space of dimension `s+2`, the full center-root group has order
`2^(s+1)`. A quadratic summand exchange identifies it with the full
axis-root group. The two groups normalize one another and intersect in
the marked central subgroup of order two. The normalized-product formula
therefore gives order `2^(2*s+1)` for their join.

This is the order calculation in Aschbacher--Smith, *The Classification
of Quasithin Groups*, original Lemma 15.3.56(6--7), printed p. 1148
(combined manuscript, 1 March 2004); in dimension three the order is eight.
-/

public section
namespace BinaryPairedTransvections
open Subgroup
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The two full transvection groups have normalized product of order
`2^(2*s+1)` on a space of dimension `s+2`. -/
theorem pairGroup_card_of_exchange [FiniteDimensional (ZMod 2) E]
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0)
    (hdc : d c = 0) (t : BinaryLinear.GL (PairedSpace E))
    (hq : ∀ u, BinaryNaturalDual.quadratic (t u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (htd : t (0,d) = (c,0))
    (s : ℕ) (hdim : Module.finrank (ZMod 2) E = s+2) :
    Nat.card (pairGroup c d) = 2^(2*s+1) := by
  let : Finite E := Module.finite_of_finite (ZMod 2)
  have he := centerGroup_conjugate_eq_axisGroup c hc d hd t hq hE hD htd
  have haxis : Nat.card (axisGroup d) = Nat.card (centerGroup c) := by
    rw [← card_map_of_injective (f := pairedAction) pairedAction_injective,
      ← he, card_map_of_injective (MulAut.conj t⁻¹).injective,
      card_map_of_injective pairedAction_injective]
  have hinf : Nat.card (centerGroup c ⊓ axisGroup d : Subgroup (BinaryLinear.GL E)) = 2 := by
    rw [← center_pairGroup_eq_inf c hc d hd hdc,
      card_map_of_injective (pairGroup c d).subtype_injective,
      center_pairGroup_card c hc d hd hdc]
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes (centerGroup c) (axisGroup d)
    (axisGroup_normalizes_centerGroup c d hdc)
  rw [haxis, centerGroup_card c hc s hdim, hinf] at hp
  have hpow : 2^(s+1)*2^(s+1) = 2*2^(2*s+1) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  change 2^(s+1)*2^(s+1) = 2*Nat.card (pairGroup c d) at hp
  omega

end BinaryPairedTransvections
