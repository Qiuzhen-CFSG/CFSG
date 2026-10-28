module

public import Theory.Mathieu.M11.Properties.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the M₁₁ quotient in the Bender inspection

The native M₁₁ Sylow presentation supplies the noncommuting returning pair.
Applying the marked quotient adapter excludes every actual component with
L/O₂(L) isomorphic to M₁₁ under the original source hypotheses. The final
application uses the literal involution centralizer and its selected Sylow.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). Source component selection
and the original inner action come from 1.1.5; no model pair, fusion, lift,
center-order or multiplier premise remains in this family conclusion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The M₁₁ quotient alternative in source row (f) is impossible, including
every central two-kernel permitted by the original source configuration. -/
theorem LocalControlWitness.false_of_inner_m11_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  intro R v _ hv _
  exact Sporadic.Mathieu.m11_sylow_noncommuting_conjugates R v hv

/-- Application to the literal bad-centralizer component of Proposition
2.2.2. The selected Sylow maps and the original distinguished z are retained. -/
theorem LocalControlWitness.false_of_inner_m11_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_m11_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
