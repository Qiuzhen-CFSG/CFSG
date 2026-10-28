module

public import Theory.Mathieu.M12.Properties.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the M₁₂ quotient in the Bender inspection

The actual two-central quotient marker has noncommuting returning conjugates,
proved through the genuine M₁₁ embedding and M₁₂ involution-square fusion.
The source quotient adapter lifts only those conjugates and contradicts the
abelian strong closure of U. The final application retains the literal
centralizer C_G(u), selected Sylow maps and original distinguished z.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). The component selection and
original inner action remain the preceding source inputs. No involution table,
fusion, pair, lift, center-order or multiplier premise is added.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The M₁₂ quotient alternative of source row (f) is impossible for every
central two-kernel permitted by the original Bender configuration. -/
theorem LocalControlWitness.false_of_inner_m12_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M12)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact Sporadic.Mathieu.m12_sylow_noncommuting_conjugates

/-- Application to the literal bad-centralizer component in Proposition
2.2.2, with the original Sylow inclusions and marked action unchanged. -/
theorem LocalControlWitness.false_of_inner_m12_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M12)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_m12_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
