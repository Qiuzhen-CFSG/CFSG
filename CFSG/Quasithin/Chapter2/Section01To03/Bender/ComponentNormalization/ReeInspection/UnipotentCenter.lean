module

public import Theory.SpecificGroups.ReeF4.MarkedStrongClosure.UnipotentCenter
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.ReeInspection

/-!
# Unconditional large Ree source exclusions

The standard positive-center theorem discharges the sole model-local premise
of the checked Ree inspection. These companions retain the original quotient,
simple component, actual carrier predicate and C_G(u) source applications,
including the original z-action and selected Sylow maps. The existing
conditional statements remain available unchanged.

The large family has field order 2^(2m+1), m ≥ 1. The full binary group is
not substituted for the separately treated derived binary/Tits group.
Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, Proposition 2.2.2,
pp.519--520, and the standard Ree center in 16.1.6 and 16.5.13.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The genuine central-two quotient is excluded without a remaining
standard-center or involution-classification premise. -/
theorem LocalControlWitness.false_of_inner_ree_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (m : ℕ) (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* _root_.ReeF4.Model m)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_ree_twoCore_component_of_central_involutions
    H S hUS hST hcore L hL hLM m hm
    (_root_.ReeF4.MarkedStrongClosure.standardCentralInvolutions m hm) e hinner

/-- Source simplicity is sufficient to pass from the component to its
central-two quotient and apply the completed large Ree pair. -/
theorem LocalControlWitness.false_of_inner_ree_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) (m : ℕ) (hm : 1 ≤ m)
    (e : L ≃* _root_.ReeF4.Model m)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_ree_component_of_central_involutions
    H S hUS hST hcore L hL hLM hsimple m hm
    (_root_.ReeF4.MarkedStrongClosure.standardCentralInvolutions m hm) e hinner

/-- The literal large Ree carrier predicate now has no extra mathematical
premise beyond the original Bender source assumptions. -/
theorem LocalControlWitness.false_of_inner_ree_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) (hmodel : _root_.ReeF4.IsReeF4Model L)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_ree_model_of_central_involutions
    H S hUS hST hcore L hL hLM hsimple hmodel
    _root_.ReeF4.MarkedStrongClosure.standardCentralInvolutions hinner

/-- The actual bad-centralizer application retains its original Sylow
subtype maps and inner z-action and has no outstanding Ree premise. -/
theorem LocalControlWitness.false_of_inner_ree_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (hsimple : IsSimpleGroup L)
    (hmodel : _root_.ReeF4.IsReeF4Model L)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_ree_centralizer_component_of_central_involutions
    u S hUS hST hcore L hL hLM hsimple hmodel
    _root_.ReeF4.MarkedStrongClosure.standardCentralInvolutions hinner

end CFSG.Quasithin.Chapter2.BenderFusion
