module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition.Inputs

/-!
# Returning recognized coordinates to the original source action

Natural quotient coordinates for the binary matrix action give the marking
used in 11.3.7. Compatibility of the two matrix identifications preserves
the original quotient map from K. The movement hypothesis forces positive
multiplicity, and the coordinate kernel is exactly C_{V_H}(K).

This adapter consumes the recognition output; it does not assert G.1.6.
Its input theorem `source_fixedSpaceHypotheses` supplies the original G.1.6
hypotheses independently of that recognition output.

Source: Aschbacher--Smith, 11.3.7, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL2SylowFixedRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace NaturalRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H : Subgroup G}
  [IsElementaryAbelian 2 (omegaClosure T H)]

theorem binaryAction_moves {F : Type*} [Field F]
    (e : residualStar T H ≃* SL(2,F))
    (hTH : (T : Subgroup G) ≤ H) (hm : ⁅omegaCenter T, H⁆ ≠ ⊥) :
    ∃ g v, binaryAction T H e g v ≠ v := by
  by_contra hn
  push Not at hn
  apply residualAction_nontrivial T H hTH hm
  apply top_unique
  intro k _
  apply MulEquiv.ext
  intro v
  have he := congrArg Additive.toMul
    (hn (e (residualProjection T H k)) (Additive.ofMul v))
  rw [binaryAction_residual] at he
  exact he

/-- The concrete coordinate adapter, including positivity from source movement.
The only recognition input is an actual equivariant linear quotient map. -/
theorem marking_of_coordinates {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (s : Hypothesis1131At D S U₁ H)
    (e : (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃* SL(2,S.field.Carrier))
    (eStar : residualStar T H ≃* SL(2,S.field.Carrier))
    (he : ∀ k : outsideResidual H, eStar (residualProjection T H k) =
      e (QuotientGroup.mk' _ k))
    (c : QuotientCoordinates (binaryAction T H eStar)) :
    Nonempty (NaturalQuotientMarking T H S.field) := by
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra _ 2
  let q : omegaClosure T H →*
      Multiplicative (Fin c.multiplicity → Fin 2 → S.field.Carrier) :=
    { toFun v := Multiplicative.ofAdd (c.coordinates (Additive.ofMul v))
      map_one' := c.coordinates.map_zero
      map_mul' a b := c.coordinates.map_add (Additive.ofMul a) (Additive.ofMul b) }
  refine ⟨⟨c.multiplicity,c.positive_of_movement
    (binaryAction_moves eStar s.outside.1.1.2 s.moves_omega_center),e,q,?_,?_,?_⟩⟩
  · intro w
    obtain ⟨v,hv⟩ := c.surjective w.toAdd
    exact ⟨v.toMul,hv⟩
  · ext v
    change c.coordinates (Additive.ofMul v) = 0 ↔ _
    change Additive.ofMul v ∈ LinearMap.ker c.coordinates ↔ _
    rw [c.kernel,binaryAction_global_fixed]
    rfl
  · intro k v i
    have hc := c.intertwines (eStar (residualProjection T H k)) (Additive.ofMul v) i
    rw [he] at hc
    have ha : binaryAction T H eStar (e (QuotientGroup.mk' _ k)) (Additive.ofMul v) =
        Additive.ofMul (residualAction T H k v) := by
      rw [← he]
      exact congrArg Additive.ofMul (binaryAction_residual T H eStar k _)
    rw [ha] at hc
    exact hc

end NaturalRecognition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
