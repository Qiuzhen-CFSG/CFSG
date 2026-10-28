module
public import CFSG.Quasithin.Chapter8.Section03.Fusion
public import CFSG.Quasithin.ChapterE.Section03.Parameters

/-!
# Hyperplane movement below the global fixed-space parameter

For a corank-i subgroup A of a conjugate of V, a hyperplane B has corank
(i+1). Below s(G,V), E.3.7 says C_V(B) centralizes the entire conjugate.
Consequently a nonzero commutator [C_V(B),A] is impossible. Applying this
to every moving generator shows that W_i(S,V) centralizes V.

The original tensor radical supplies these hyperplanes in the Chapter 10
consumer, giving the W₁(S,V) bound used in 8.3.3 and 8.3.5.
Source: Aschbacher--Smith E.3.7 and 8.3.3--5, printed pp.231--232,723--724.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter8.Section03
open ChapterE

/-- Hyperplane movement contradicts the fixed-space equality below s. -/
theorem weakClosure_centralizes_of_moving_hyperplanes
    {G : Type*} [Group G] [Finite G] (V S : Subgroup G) [IsElementaryAbelian 2 V]
    (hSN : S ≤ normalizer (V : Set G)) {i : ℕ}
    (hs : ((i + 1 : ℕ) : ℕ∞) < globalS V)
    (hh : ∀ A ∈ gamma V S i, ¬ A ≤ centralizer (V : Set G) →
      ∃ B ≤ A, B.relIndex A = 2 ∧ ⁅V ⊓ centralizer (B : Set G),A⁆ ≠ ⊥) :
    indexedWeakClosure V S i ≤ centralizer (V : Set G) := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  by_contra hmove
  obtain ⟨B,hBA,hidx,hcomm⟩ := hh A hA hmove
  obtain ⟨⟨g,hAg,hi⟩,hAS⟩ := hA
  have hb := corank_hyperplane_of_relIndex hBA hAg hidx hi
  have hc := lemma_E_3_7 g (le_inf (hBA.trans hAg) (hBA.trans (hAS.trans hSN)))
    (by rwa [hb])
  apply hcomm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [hc]
  exact inf_le_right.trans (centralizer_le hAg)

end CFSG.Quasithin.Chapter8.Section03
