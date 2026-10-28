module

public import Theory.SpecificGroups.Janko4.Model.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the J₄ quotient in the Bender inspection

The concrete model theorem supplies two noncommuting returning conjugates
of the actual two-central quotient marker. The central two-quotient adapter
lifts this pair and contradicts the abelian strong closure of U. The literal
centralizer application retains the original z and the chosen Sylow maps.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). The original component,
odd-core and inner-action inputs remain explicit. No fusion, pair, lift,
covering-kernel order or involution-table premise is added.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The J₄ quotient alternative in source row (f) is incompatible with
the original strongly closed subgroup and distinguished inner action. -/
theorem LocalControlWitness.false_of_inner_j4_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Janko4.Model)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact Janko4.sylow_noncommuting_conjugates

/-- The actual bad-centralizer component application, with the literal
quotient and original source subtype inclusions unchanged. -/
theorem LocalControlWitness.false_of_inner_j4_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Janko4.Model)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_j4_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
