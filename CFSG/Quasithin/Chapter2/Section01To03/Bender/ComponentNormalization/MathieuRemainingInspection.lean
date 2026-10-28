module

public import Theory.Mathieu.RemainingMarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the remaining Mathieu quotients in the Bender inspection

The actual marked quotient involution has noncommuting returning conjugates
in M₂₂, M₂₃ and M₂₄. The model theorem supplies these pairs from the genuine
PSL₃(4) embedding, identifying the M₂₄ marker and pair specifically as 2A.
The central two-quotient adapter lifts the pair and contradicts the abelian
strong closure of U, retaining the original distinguished z and Sylow maps.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). The source component choice,
odd-core condition and original inner action remain explicit. No pair,
fusion, class-table, lift, covering-kernel order or multiplier premise is added.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The M22 quotient alternative of source row (f) is impossible for every
central two-kernel permitted by the original Bender configuration. -/
theorem LocalControlWitness.false_of_inner_m22_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact fun R v _ ho _ => Sporadic.Mathieu.m22_sylow_noncommuting_conjugates R v ho

/-- Application to the literal bad-centralizer component in Proposition
2.2.2, with the original Sylow inclusions and marked action unchanged. -/
theorem LocalControlWitness.false_of_inner_m22_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_m22_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

/-- The M23 quotient alternative of source row (f) is impossible for every
central two-kernel permitted by the original Bender configuration. -/
theorem LocalControlWitness.false_of_inner_m23_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M23)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact fun R v _ ho _ => Sporadic.Mathieu.m23_sylow_noncommuting_conjugates R v ho

/-- Application to the literal bad-centralizer component in Proposition
2.2.2, with the original Sylow inclusions and marked action unchanged. -/
theorem LocalControlWitness.false_of_inner_m23_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M23)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_m23_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

/-- The M24 quotient alternative of source row (f) is impossible for every
central two-kernel permitted by the original Bender configuration. -/
theorem LocalControlWitness.false_of_inner_m24_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M24)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact Sporadic.Mathieu.m24_sylow_noncommuting_conjugates

/-- Application to the literal bad-centralizer component in Proposition
2.2.2, with the original Sylow inclusions and marked action unchanged. -/
theorem LocalControlWitness.false_of_inner_m24_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M24)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_m24_twoCore_component (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
