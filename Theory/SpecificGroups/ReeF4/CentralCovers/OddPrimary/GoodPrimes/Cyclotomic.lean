module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.TorusTransfer
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.FixedModel
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.WeylAction
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The two cyclotomic Ree torus branches

The coordinate fixed groups have the required orders, and are embedded in the
actual algebraic F4 torus. The constructed algebraic Ree twist has Lang
surjectivity for `m ≥ 1`, and its fixed subgroup is proved equivalent to the
literal finite matrix model through the coefficient embedding. The proved
Weyl action equations for `s₀s₁` and `(s₀s₁s₂s₃)^6 s₀s₁` complete descent
over the algebraic closure of the coefficient field. Thus both cyclic tori
embed in `Model m` without additional geometric hypotheses.

The field-size convention is `q = 2^(2*m+1)` and `t = 2^(m+1)`, giving
`q²+q+1 ∓ t(q+1)`. At `m = 1` these are 37 and 109. The final applications
give the cyclic Sylow alternative from the parent calculation's independent
order and prime-to-p cofactor hypotheses.
Source: GLS3 §§2.1–2.4 and §4.10, `refs/KGroup/GLS3/chapter2.tex` and
`chapter4.tex`.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic
open Theory.AlgebraicGroup
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Assemble both literal finite Ree embeddings from the specified geometric inputs. -/
theorem embeddings_of_algebraic_descent [CharP F 2] (m : ℕ)
    (σ : AlgebraicPoints F →* AlgebraicPoints F)
    (e : algebraicFixed σ ≃* Model m)
    (gMinus gPlus : AlgebraicPoints F)
    (hgMinus : gMinus * (σ gMinus)⁻¹ = weylMinus)
    (hgPlus : gPlus * (σ gPlus)⁻¹ = weylPlus)
    (hMinus : ∀ u, weylMinus * σ (diagonal u) * weylMinus⁻¹ =
      diagonal (twistedAction ((2:ℤ)^m) u))
    (hPlus : ∀ u, weylPlus * σ (diagonal u) * weylPlus⁻¹ =
      diagonal (twistedAction (-((2:ℤ)^m)) u)) :
    Nonempty (CyclicTorusEmbedding m (minusOrder m)) ∧
      Nonempty (CyclicTorusEmbedding m (plusOrder m)) := by
  constructor
  · rw [minusOrder_eq]
    exact ⟨cyclicEmbeddingOfDescent ((2:ℤ)^m) σ weylMinus gMinus hgMinus hMinus e⟩
  · rw [plusOrder_eq]
    exact ⟨cyclicEmbeddingOfDescent (-((2:ℤ)^m)) σ weylPlus gPlus hgPlus hPlus e⟩
/-- Lang solvability and comparison with the finite model are discharged;
only the two literal Weyl action calculations remain. -/
theorem embeddings_of_weyl_actions [CharP F 2] (m : ℕ) (hm : 1 ≤ m)
    (f : CoefficientField m →+* F)
    (hMinus : ∀ u : Fin 4 → Fˣ,
      weylMinus * (algebraicReeTwist m).onPoints (diagonal u) * weylMinus⁻¹ =
      diagonal (twistedAction ((2:ℤ)^m) u))
    (hPlus : ∀ u : Fin 4 → Fˣ,
      weylPlus * (algebraicReeTwist m).onPoints (diagonal u) * weylPlus⁻¹ =
      diagonal (twistedAction (-((2:ℤ)^m)) u)) :
    Nonempty (CyclicTorusEmbedding m (minusOrder m)) ∧
      Nonempty (CyclicTorusEmbedding m (plusOrder m)) := by
  obtain ⟨gMinus, hgMinus⟩ := algebraicReeTwist_lang (F := F) m hm weylMinus
  obtain ⟨gPlus, hgPlus⟩ := algebraicReeTwist_lang (F := F) m hm weylPlus
  exact embeddings_of_algebraic_descent m (algebraicReeTwist m).onPoints
    (fixedModelEquiv f) gMinus gPlus hgMinus hgPlus hMinus hPlus

/-- Both cyclotomic tori embed in the actual Ree model for every field size at least eight. -/
theorem embeddings (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (CyclicTorusEmbedding m (minusOrder m)) ∧
      Nonempty (CyclicTorusEmbedding m (plusOrder m)) := by
  exact embeddings_of_weyl_actions m hm
    (algebraMap (CoefficientField m) (AlgebraicClosure (CoefficientField m)))
    (weylMinus_algebraicReeTwist m) (weylPlus_algebraicReeTwist m)

/-- The cyclic torus of order `q²+q+1-t(q+1)` in the literal finite Ree group. -/
theorem minus_embedding (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (CyclicTorusEmbedding m (minusOrder m)) :=
  (embeddings m hm).1

/-- The cyclic torus of order `q²+q+1+t(q+1)` in the literal finite Ree group. -/
theorem plus_embedding (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (CyclicTorusEmbedding m (plusOrder m)) :=
  (embeddings m hm).2

/-- The minus torus discharges the cyclic embedding premise of the Sylow transfer.
The ambient order and its prime-to-p cofactor remain the independent arithmetic inputs. -/
theorem goodPrimeGeometry_of_minus {m c p : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (horder : Nat.card (Model m) = minusOrder m * c) (hc : ¬ p ∣ c) :
    GoodPrimeGeometry m p := by
  obtain ⟨T⟩ := minus_embedding m hm
  exact T.goodPrimeGeometry (minusOrder_pos m) horder hc

/-- The plus torus discharges the cyclic embedding premise of the Sylow transfer.
The ambient order and its prime-to-p cofactor remain the independent arithmetic inputs. -/
theorem goodPrimeGeometry_of_plus {m c p : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (horder : Nat.card (Model m) = plusOrder m * c) (hc : ¬ p ∣ c) :
    GoodPrimeGeometry m p := by
  obtain ⟨T⟩ := plus_embedding m hm
  exact T.goodPrimeGeometry (plusOrder_pos m) horder hc

end
end ReeF4.CentralCovers.OddPrimary.Cyclotomic
