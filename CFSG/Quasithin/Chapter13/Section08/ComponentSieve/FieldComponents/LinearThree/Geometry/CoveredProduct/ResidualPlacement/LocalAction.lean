module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.ResidualDirections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSeed

/-!
# The marked covered local residual action

The natural setup retains the actual hexacode triple cover, the conjugation
map onto the natural A₆ section, and its compatible Sylow-stable flag. The
quotient marks are induced by the literal subgroup inclusions. The concrete
cover calculation supplies their cubic orders; multiplication of the marks
identifies L₁/O₂(L₁) with their direct product. The commutator defining X
forces an element of T∩L to invert its cubic quotient, while centralizing
the L₀ quotient. The two marks are precisely the T-invariant cubic lines.
The natural flag calculation also gives X ≤ N_G(V₃) and V₃ ≤ [X,V₃]V₁,
while the earlier central-preimage centralizer fact gives [L₀,V₃] ≤ V₁.

Every local model and action premise is discharged from `NaturalSetup`.
The factorization L₁ = XL₀ remains the explicitly identified earlier
input 13.2.2(3), as permitted for this conditional local calculation.
Ambient component placement and the full 13.2.2 are separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.876–877;
13.8.16, pp.952–953, and the covered case of 13.8.21(1), p.957.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup

variable {G : Type*} [Group G] [Finite G]
  {L T V V₁ V₃ : Subgroup G} (d : NaturalSetup L T V V₁ V₃)
  (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)

/-- The actual marked product equivalence, with its cubic-order premise
discharged by the covered natural model. -/
def markedProductEquiv :
    ((zero L ⧸ pCore 2 (zero L)) ×
      (plus L T V₁ ⧸ pCore 2 (plus L T V₁))) ≃*
        (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
  LocalAction.markedProductEquiv L T V₁ d.normalizes_L d.line_stable hfactor
    (d.plus_core_card hfactor)

/-- This equivalence multiplies the two inclusion-induced quotient maps. -/
theorem markedProductEquiv_apply
    (z : zero L ⧸ pCore 2 (zero L)) (x : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :
    d.markedProductEquiv hfactor (z, x) =
      zeroCoreMap L T V₁ d.normalizes_L hfactor z * plusCoreMap L T V₁ d.line_stable x :=
  LocalAction.markedProductEquiv_apply L T V₁ d.normalizes_L d.line_stable hfactor
    (d.plus_core_card hfactor) z x

/-- The first factor retains the source L₀ mark. -/
theorem markedProductEquiv_zero (z : zero L ⧸ pCore 2 (zero L)) :
    d.markedProductEquiv hfactor (z, 1) = zeroCoreMap L T V₁ d.normalizes_L hfactor z := by
  rw [d.markedProductEquiv_apply, map_one, mul_one]

/-- The second factor retains the source X mark. -/
theorem markedProductEquiv_plus (x : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :
    d.markedProductEquiv hfactor (1, x) = plusCoreMap L T V₁ d.line_stable x := by
  rw [d.markedProductEquiv_apply, map_one, one_mul]

/-- Both literal quotient images have order three. -/
theorem marks_card_three :
    Nat.card (zeroCoreMap L T V₁ d.normalizes_L hfactor).range = 3 ∧
      Nat.card (plusCoreMap L T V₁ d.line_stable).range = 3 :=
  LocalAction.marks_card_three L T V₁ d.normalizes_L d.line_stable hfactor
    d.zero_core_card (d.plus_core_card hfactor)

/-- The two source directions have trivial intersection in the local quotient. -/
theorem marks_disjoint :
    Disjoint (zeroCoreMap L T V₁ d.normalizes_L hfactor).range
      (plusCoreMap L T V₁ d.line_stable).range :=
  LocalAction.marks_disjoint L T V₁ d.normalizes_L d.line_stable hfactor
    (d.plus_core_card hfactor)

include d hfactor in
/-- The local quotient has order nine, derived from the marked cubic factors. -/
theorem one_quotient_card : Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 9 :=
  LocalAction.one_quotient_card L T V₁ d.normalizes_L d.line_stable hfactor
    d.zero_core_card (d.plus_core_card hfactor)

include d hfactor in
/-- Commutativity of the actual order-nine quotient. -/
theorem one_quotient_commutative : IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
  LocalAction.one_quotient_commutative L T V₁ d.normalizes_L d.line_stable hfactor
    d.zero_core_card (d.plus_core_card hfactor)

include d hfactor in
/-- Exponent three completes the elementary abelian order-nine calculation. -/
theorem one_quotient_cube (q : one L T V₁ ⧸ pCore 2 (one L T V₁)) : q ^ 3 = 1 :=
  LocalAction.one_quotient_cube L T V₁ d.normalizes_L d.line_stable hfactor
    d.zero_core_card (d.plus_core_card hfactor) q

include hfactor in
/-- The source element of T∩L simultaneously inverts X/O₂(X) and centralizes
L₀/O₂(L₀), through the actual conjugation actions. -/
theorem exists_plus_inverter :
    ∃ t : (T ⊓ L : Subgroup G),
      (∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁)
        ⟨t.val, T_normalizes_plus L T V₁ d.normalizes_L d.line_stable t.property.1⟩ x = x⁻¹) ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 :=
  LocalAction.exists_plus_inverter L T V₁ d.normalizes_L d.line_stable hfactor
    (d.plus_core_card hfactor)

/-- Equivariance retains T-invariance of the L₀ mark in the local quotient. -/
theorem zero_mark_stable (s : T)
    (q : one L T V₁ ⧸ pCore 2 (one L T V₁))
    (hq : q ∈ (zeroCoreMap L T V₁ d.normalizes_L hfactor).range) :
    coreAction (one L T V₁)
      ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ q ∈
        (zeroCoreMap L T V₁ d.normalizes_L hfactor).range := by
  obtain ⟨z, rfl⟩ := hq
  have hs := normalizer_le_zero_normalizer L (d.normalizes_L s.property)
  refine ⟨coreAction (zero L) ⟨s.val, hs⟩ z, ?_⟩
  exact localCoreMap_equivariant _ _ _ _ s.val hs _ z

/-- Equivariance retains T-invariance of the X mark in the local quotient. -/
theorem plus_mark_stable (s : T)
    (q : one L T V₁ ⧸ pCore 2 (one L T V₁))
    (hq : q ∈ (plusCoreMap L T V₁ d.line_stable).range) :
    coreAction (one L T V₁)
      ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ q ∈
        (plusCoreMap L T V₁ d.line_stable).range := by
  obtain ⟨x, rfl⟩ := hq
  have hs := T_normalizes_plus L T V₁ d.normalizes_L d.line_stable s.property
  refine ⟨coreAction (plus L T V₁) ⟨s.val, hs⟩ x, ?_⟩
  exact localCoreMap_equivariant _ _ _ _ s.val hs _ x

/-- Every T-invariant cubic line is one of the two source marks. No quotient
order, commutativity or inversion premise remains. -/
theorem invariant_marked_line
    (C : Subgroup (one L T V₁ ⧸ pCore 2 (one L T V₁)))
    (hC : Nat.card C = 3)
    (hstable : ∀ s : T, ∀ x ∈ C,
      coreAction (one L T V₁)
        ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ x ∈ C) :
    C = (zeroCoreMap L T V₁ d.normalizes_L hfactor).range ∨
      C = (plusCoreMap L T V₁ d.line_stable).range :=
  LocalAction.invariant_marked_line_of_cubic_orders L T V₁ d.normalizes_L d.line_stable
    hfactor d.zero_core_card (d.plus_core_card hfactor) C hC hstable

/-- The two marked cubic subgroups are exactly the T-invariant lines of the
elementary abelian local quotient. -/
theorem invariant_marked_line_iff
    (C : Subgroup (one L T V₁ ⧸ pCore 2 (one L T V₁))) :
    (Nat.card C = 3 ∧ ∀ s : T, ∀ x ∈ C,
      coreAction (one L T V₁)
        ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ x ∈ C) ↔
    C = (zeroCoreMap L T V₁ d.normalizes_L hfactor).range ∨
      C = (plusCoreMap L T V₁ d.line_stable).range := by
  constructor
  · rintro ⟨hC, hstable⟩
    exact d.invariant_marked_line hfactor C hC hstable
  · rintro (rfl | rfl)
    · exact ⟨(d.marks_card_three hfactor).1, d.zero_mark_stable hfactor⟩
    · exact ⟨(d.marks_card_three hfactor).2, d.plus_mark_stable⟩

include d hfactor in
/-- The three source seed assertions, all on the same natural flag. -/
theorem seed_facts :
    plus L T V₁ ≤ normalizer (V₃ : Set G) ∧
      V₃ ≤ ⁅plus L T V₁, V₃⁆ ⊔ V₁ ∧ ⁅zero L, V₃⁆ ≤ V₁ :=
  ⟨d.plus_normalizes_seed, d.seed_le_plus_commutator_sup hfactor, d.zero_seed_commutator⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
