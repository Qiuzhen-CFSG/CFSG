module

public import Theory.SpecificGroups.Tits.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the Tits component in the Bender inspection

The existing quotient adapter derives the actual component Sylow, central
two-kernel and nontrivial quotient marker from the original Bender witness.
The Tits two-central root marking and two internal Parrott words supply a
noncommuting returning pair. Abelian strong closure gives the contradiction.

The simple component and actual C_G(u) consumers keep the original Sylow
maps and inner action of z. The model is the simple derived binary Ree group
ParrottGroup, never the full fixed group ²F₄(2). No full involution coverage,
covering-group classification, or local block-generation premise is required.

Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, and Proposition 2.2.2,
pp.519--520, combined 1 March 2004 manuscript.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- A literal Tits quotient contradicts the returning-conjugate consequence
of strong closure, with no restriction on the central two-kernel's order. -/
theorem LocalControlWitness.false_of_inner_tits_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* Tits.ParrottGroup)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact Tits.MarkedStrongClosure.sylow_noncommuting_conjugates

/-- Exclude the simple Tits occurrence of source 1.1.5(3)(a). The actual
model's proved simplicity removes the component's two-core. -/
theorem LocalControlWitness.false_of_inner_tits_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : L ≃* Tits.ParrottGroup)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := e.isSimpleGroup
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hO : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* Tits.ParrottGroup :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e
  exact w.false_of_inner_tits_twoCore_component H S hUS hST hcore L hL hLM e' hinner

/-- Apply the source exclusion to the actual bad-centralizer component of
Proposition 2.2.2, retaining its selected Sylow and the original z. -/
theorem LocalControlWitness.false_of_inner_tits_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : L ≃* Tits.ParrottGroup)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_tits_component (centralizer ({u} : Set G)) S hUS hST hcore
    L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
