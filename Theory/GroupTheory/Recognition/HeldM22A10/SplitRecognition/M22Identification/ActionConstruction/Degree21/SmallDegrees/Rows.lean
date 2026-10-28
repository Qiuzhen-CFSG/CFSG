module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData

/-!
# All possible exceptional rows of degree at most 21

Unit multiplicities, the Sylow-two restriction congruence, degree divisibility,
nonnegative E16 fixed multiplicity, and faithfulness leave exactly two rows
at degree 20 and two rows at degree 21. The finite check ranges over all
243 unit rows, independently of any selected signed family. It does not
exclude degree 20 or prove uniqueness at degree 21.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Sections 6--7. This is an intermediate exhaustion for the assertions on p.16.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
open CharacterOrder
private def decoded (c : Fin 5 → Fin 3) (i : Fin 5) : ℤ := (c i : ℤ) - 1
private def smallAlternatives (n : ℕ) (c : Fin 5 → ℤ) : Prop :=
  (n = 20 ∧ (c = ![0, 0, -1, 1, -1] ∨ c = ![1, 0, 0, 0, -1])) ∨
  (n = 21 ∧ (c = ![0, 0, 0, 1, -1] ∨ c = ![1, 0, 1, 0, -1]))
private instance (n : ℕ) (c : Fin 5 → ℤ) : Decidable (smallAlternatives n c) :=
  inferInstanceAs (Decidable ((_ ∧ (_ ∨ _)) ∨ (_ ∧ (_ ∨ _))))
private theorem finite_small : ∀ n : Fin 22, ∀ c : Fin 5 → Fin 3,
    0 < n.val → n.val ∣ 443520 →
    0 ≤ (n.val : ℤ) + 15 * columnValue (decoded c) 0 →
    columnValue (decoded c) 0 < (n.val : ℤ) →
    (128 : ℤ) ∣ (n.val : ℤ) + 153 * decoded c 0 - 202 * decoded c 1 +
      127 * decoded c 2 + 280 * decoded c 3 + 45 * decoded c 4 →
    smallAlternatives n.val (decoded c) := by
  decide +kernel

/-- Exhaustion of every possible row of degree at most 21 under the local constraints. -/
public theorem small_rows (n : ℕ) (c : Fin 5 → ℤ)
    (hpos : 0 < n) (hdvd : n ∣ 443520) (hn : n ≤ 21)
    (hu : ∀ i, c i = 0 ∨ c i = 1 ∨ c i = -1)
    (hfix : 0 ≤ (n : ℤ) + 15 * columnValue c 0)
    (hlt : columnValue c 0 < (n : ℤ))
    (hres : (128 : ℤ) ∣ (n : ℤ) + 153 * c 0 - 202 * c 1 +
      127 * c 2 + 280 * c 3 + 45 * c 4) :
    (n = 20 ∧ (c = ![0, 0, -1, 1, -1] ∨ c = ![1, 0, 0, 0, -1])) ∨
    (n = 21 ∧ (c = ![0, 0, 0, 1, -1] ∨ c = ![1, 0, 1, 0, -1])) := by
  let f (i : Fin 5) : Fin 3 := ⟨(c i + 1).toNat, by have := hu i; omega⟩
  have hf : decoded f = c := by
    funext i
    dsimp [decoded, f]
    have := hu i
    omega
  have hh := finite_small ⟨n, by omega⟩ f
  rw [hf] at hh
  exact hh hpos hdvd hfix hlt hres
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
