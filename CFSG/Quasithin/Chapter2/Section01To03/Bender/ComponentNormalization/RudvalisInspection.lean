module

public import Theory.SpecificGroups.Rudvalis.Model.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the Rudvalis quotient in the Bender inspection

The actual two-central Ru marker has noncommuting returning conjugates in
its supplied Sylow. The central two-quotient adapter lifts this pair to the
original component and contradicts the abelian strong closure of U. It
derives the central two-kernel from O(H)=1, with no restriction on its order.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and Proposition 2.2.2,
pp.519--520, combined 1 March 2004 manuscript. The actual quotient,
component, centralizer, original z and Sylow subtype maps are retained.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The Ru quotient alternative in source row (f) contradicts the original
strong closure and distinguished inner action, for every central two-kernel. -/
theorem LocalControlWitness.false_of_inner_rudvalis_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Rudvalis.Model)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact Rudvalis.MarkedStrongClosure.sylow_noncommuting_conjugates

/-- The literal bad-centralizer component application, preserving the source
quotient and the original inclusions through the selected Sylow subgroup. -/
theorem LocalControlWitness.false_of_inner_rudvalis_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Rudvalis.Model)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_rudvalis_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
