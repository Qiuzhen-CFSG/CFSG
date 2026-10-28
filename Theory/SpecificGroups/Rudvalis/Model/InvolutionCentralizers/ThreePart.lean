module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives

/-!
# The three-part of every literal Rudvalis involution centralizer

The checked order of C(a) and the existing marked max6 order combine with
actual involution conjugacy coverage. The equivalence is of the full
centralizer of the specified element, so no abstract class tag is substituted.
Source: Aschbacher–Smith, Quasithin 16.1.5(11), used in E.6.18 and E.6.23.
-/

namespace Rudvalis.InvolutionCentralizers

/-- The full centralizer of any involution has order indivisible by nine. -/
public theorem centralizer_not_nine (t : Model) (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (Centralizer t) := by
  rcases centralizer_representatives t ht with h | h
  · rw [first_centralizer_card h.1]
    decide
  · obtain ⟨f⟩ := h.2
    rw [Nat.card_congr f.toEquiv]
    exact second_centralizer_not_nine

/-- Actual conjugacy to the second marker transports its full centralizer order. -/
public theorem second_class_centralizer_card {t : Model} (ht : IsConj t a) :
    Nat.card (Centralizer t) = 116480 :=
  (Nat.card_congr (centralizerEquivOfIsConj ht).toEquiv).trans second_centralizer_card
end Rudvalis.InvolutionCentralizers
