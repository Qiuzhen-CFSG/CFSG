module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.CoreData

/-!
# The source normal closure and its natural binary quotient

In Aschbacher–Smith, Proposition 6.2.13, printed pp.686–688 (PDF pp.703–705),
`U = ⟨Z_S^H⟩` is formed inside the actual involution centralizer `H`. After
excluding the symmetric-six and symmetric-seven cases, the invocation of
G.6.4(2) on p.687 makes `U/Z` the natural two-dimensional binary module for
`H* ≃ S₃`. `NaturalFourOrbit` records just its order and its transitivity on
nonidentity vectors, using the actual quotient and actual conjugation.
Its producer is the preceding argument owned by `qt-6-02-m22-branch`.

These action consequences do not assert that `U` is elementary. We prove
that here: a noncentral element of the elementary four `Z_S` has square one;
transitivity gives the same square for every noncentral coset, since changing
a representative by a central involution preserves its square. The order of
`U` follows from the kernel and image orders. All normality is relative to
`H`, which can subsequently be instantiated by a subgroup of the ambient `G`.
The ambient natural-module extension is retained separately; this module does
not identify its quotient with an unrelated abstract group or assume splitting.
-/

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension

open Subgroup

variable {H : Type*} [Group H]

/-- The literal source subgroup `⟨Z_S^H⟩`, with conjugation inside `H`. -/
@[expose] public def sourceEight (S : Subgroup H) : Subgroup H :=
  normalClosure (S : Set H)

public instance sourceEight_normal (S : Subgroup H) : (sourceEight S).Normal :=
  normalClosure_normal

/-- The center of the actual extraspecial core, viewed in `H`. -/
@[expose] public def coreCenter (P : Subgroup H) : Subgroup H :=
  (center P).map P.subtype

public instance coreCenter_normal (P : Subgroup H) [P.Normal] :
    (coreCenter P).Normal :=
  ConjAct.normal_of_characteristic_of_normal

/-- The two precise consequences of the source natural `S₃` action on `U/Z`.
No exponent, centralizer order, or sixteen-subgroup is included. -/
public structure NaturalFourOrbit (P S : Subgroup H) [P.Normal] : Prop where
  quotient_card : Nat.card ((sourceEight S).map (QuotientGroup.mk' (coreCenter P))) = 4
  transitive : ∀ u ∈ sourceEight S, ∀ v ∈ sourceEight S,
    u ∉ coreCenter P → v ∉ coreCenter P →
      ∃ h : H, QuotientGroup.mk' (coreCenter P) (h * u * h⁻¹) =
        QuotientGroup.mk' (coreCenter P) v

public theorem sourceEight_contains (S : Subgroup H) : S ≤ sourceEight S :=
  le_normalClosure

public theorem sourceEight_le_core (P S : Subgroup H) [P.Normal] (hSP : S ≤ P) :
    sourceEight S ≤ P :=
  normalClosure_le_normal hSP

variable [Finite H] {P S : Subgroup H} [P.Normal]

public theorem coreCenter_card (h : CoreData P) : Nat.card (coreCenter P) = 2 := by
  rw [coreCenter, card_map_of_injective P.subtype_injective]
  obtain ⟨d⟩ := h.plusType
  exact d.center_card

private theorem coreCenter_square (h : CoreData P) (z : H) (hz : z ∈ coreCenter P) :
    z ^ 2 = 1 := by
  have hs := pow_card_eq_one' (x := (⟨z, hz⟩ : coreCenter P))
  rw [coreCenter_card h] at hs
  exact congrArg Subtype.val hs

/-- Equality modulo the central involution preserves squares in the actual group. -/
public theorem square_eq_of_coreCenter_quotient_eq (h : CoreData P) (u v : H)
    (huv : QuotientGroup.mk' (coreCenter P) u = QuotientGroup.mk' (coreCenter P) v) :
    u ^ 2 = v ^ 2 := by
  have hm : u⁻¹ * v ∈ coreCenter P := QuotientGroup.eq.mp huv
  have hc : Commute u (u⁻¹ * v) := mem_center_iff.mp (h.center_le hm) u
  have hs := coreCenter_square h (u⁻¹ * v) hm
  simpa only [mul_inv_cancel_left, hs, mul_one] using (hc.mul_pow 2).symm

/-- Transitivity on the three nonzero quotient vectors forces exponent two. -/
public theorem sourceEight_square (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (u : H) (hu : u ∈ sourceEight S) : u ^ 2 = 1 := by
  classical
  by_cases huz : u ∈ coreCenter P
  · exact coreCenter_square h u huz
  have hn : ¬ S ≤ coreCenter P := by
    intro hs
    have hc := card_le_of_le hs
    rw [hS, coreCenter_card h] at hc
    omega
  obtain ⟨s, hs, hsz⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨g, hg⟩ := ha.transitive s (sourceEight_contains S hs) u hu hsz huz
  rw [← square_eq_of_coreCenter_quotient_eq h _ _ hg]
  have hs2 : s ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian s hs
  simpa only [map_pow, MulAut.conj_apply, map_one] using
    congrArg (MulAut.conj g) hs2

/-- The elementary structure is proved from the orbit input, not assumed. -/
public theorem sourceEight_elementary (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4) :
    IsElementaryAbelian 2 (sourceEight S) := by
  have hs (x : sourceEight S) : x ^ 2 = 1 :=
    Subtype.ext (sourceEight_square h ha hS x x.property)
  have hi (x : sourceEight S) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hs x
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- The kernel of `U → H/Z` is `Z`, so the source normal closure has order eight. -/
public theorem sourceEight_card (h : CoreData P) (ha : NaturalFourOrbit P S)
    (hZS : coreCenter P ≤ S) : Nat.card (sourceEight S) = 8 := by
  have hZU := hZS.trans (sourceEight_contains S)
  have hi : (coreCenter P).relIndex (sourceEight S) = 4 := by
    have hk : (QuotientGroup.mk' (coreCenter P)).ker = coreCenter P :=
      QuotientGroup.ker_mk' _
    rw [← hk, relIndex_ker]
    exact ha.quotient_card
  have hc := relIndex_mul_relIndex (⊥ : Subgroup H) (coreCenter P)
    (sourceEight S) bot_le hZU
  rw [relIndex_bot_left, relIndex_bot_left, coreCenter_card h, hi] at hc
  exact hc.symm

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
