module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CentralizerConsequences
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2

/-!
# Concrete alternatives in the field-centralizer argument

These definitions publish the exact target alternatives for the last paragraph
of Aschbacher--Smith 15.3.38, printed p.1137 (1 March 2004 manuscript).
The simple central quotients are given by actual multiplicative equivalences
to PSL₃(4), the sourced J₂ permutation carrier, or PSL₃(7). The exceptional
covers are SL₃(4) and SL₃(7), after quotienting by the two-core.

The odd center is embedded through both subgroup inclusions. The unique-order-
three clause concerns subgroups of the relative centralizer `C_H(K)`, not
ambient normal subgroups. No classification or recognition is proved by these
definitions. The final elementary exclusions consume the alternative only.
`SourceObstruction` rules out the printed order-27 construction;
`JointCentralizer` instead constructs an E₉ from the earlier local data,
which suffices for `order_nine_not_le_component_centralizer`.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
open Subgroup
variable {G : Type*} [Group G]

/-- The three actual central-quotient models retained in the source. -/
@[expose] def FieldComponentQuotient (K : Subgroup G) : Prop :=
  Nonempty ((K ⧸ center K) ≃* Matrix.PSL3Four.PSL) ∨
  Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
  Nonempty ((K ⧸ center K) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7))

/-- The source's two central extensions, with the two-core quotient. -/
@[expose] def ExceptionalFieldCover (K : Subgroup G) : Prop :=
  Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.SL) ∨
  Nonempty ((K ⧸ pCore 2 K) ≃*
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 7))

/-- `O(Z(K))`, embedded in the ambient group. -/
@[expose] def oddCenterIn (K : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 (center K)).map (K.subtype.comp (center K).subtype)

/-- The full centralizer alternative, including the actual cover models
and the unique subgroup of order three in the relative centralizer. -/
@[expose] def FieldComponentCentralizerAlternative (H K : Subgroup G) : Prop :=
  Nat.Coprime 3 (Nat.card ↥(H ⊓ centralizer (K : Set G))) ∨
  (ExceptionalFieldCover K ∧ Nat.card (oddCenterIn K) = 3 ∧
    oddCenterIn K ≤ H ⊓ centralizer (K : Set G) ∧
    ∀ P : Subgroup G, P ≤ H ⊓ centralizer (K : Set G) → Nat.card P = 3 →
      P = oddCenterIn K)

/-- The order-27 obstruction applied to the genuine centralizer alternative.
This does not construct such a group or prove the alternative. -/
theorem not_le_component_centralizer [Finite G] (H K B : Subgroup G)
    (hB : Nat.card B = 27) (hexp : ∀ b : B, b ^ 3 = 1)
    (hH : B ≤ H) (hC : FieldComponentCentralizerAlternative H K) :
    ¬ B ≤ centralizer (K : Set G) := by
  apply fun h => exponent_three_order_27_not_le B
    (H ⊓ centralizer (K : Set G)) (oddCenterIn K) hB hexp ?_ (le_inf hH h)
  rcases hC with h | ⟨_, hc, _, hu⟩
  · exact Or.inl h
  · exact Or.inr ⟨hc, hu⟩

/-- The elementary exclusion also works for the order-nine group obtained
from the joint centralizer. No extraspecial order-27 input is required. -/
theorem order_nine_not_le_component_centralizer [Finite G] (H K B : Subgroup G)
    (hB : Nat.card B = 9) (hexp : ∀ b : B, b ^ 3 = 1)
    (hH : B ≤ H) (hC : FieldComponentCentralizerAlternative H K) :
    ¬ B ≤ centralizer (K : Set G) := by
  apply fun h => exponent_three_not_le B
    (H ⊓ centralizer (K : Set G)) (oddCenterIn K) (by omega) (by omega)
      hexp ?_ (le_inf hH h)
  rcases hC with h | ⟨_, hc, _, hu⟩
  · exact Or.inl h
  · exact Or.inr ⟨hc, hu⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
