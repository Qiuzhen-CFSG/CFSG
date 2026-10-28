module

public import Theory.SpecificGroups.ReeF4.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Large Ree components in the Bender inspection

The actual central-two quotient carries a nonidentity involution centralizing
its Sylow. Once the standard-unipotent center identifies that marker with a
nonzero highest-root element, the internal Weyl pair contradicts marked
abelian strong closure. The only remaining model premise is this exact
identification, owned by the independent Ree UnipotentCenter development.

The simple-component consumer uses the source's simplicity to pass from L
to L/O₂(L). The model and C_G(u) consumers retain the genuine field convention
q = 2^(2m+1), m ≥ 1, the source subgroup maps, and the original z-action.
The binary derived/Tits case has its own separate exclusion.

Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, and Proposition 2.2.2,
pp.519--520, combined 1 March 2004 manuscript.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- Retain the original central two-kernel and the precise independent
standard-unipotent marker input. -/
theorem LocalControlWitness.false_of_inner_ree_twoCore_component_of_central_involutions
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (m : ℕ) (_hm : 1 ≤ m)
    (hcenter : _root_.ReeF4.MarkedStrongClosure.StandardCentralInvolutions m)
    (e : (L ⧸ pCore 2 L) ≃* _root_.ReeF4.Model m)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact _root_.ReeF4.MarkedStrongClosure.sylow_noncommuting_conjugates_of_central_involutions
    m hcenter

/-- Source 1.1.5(3)(a) supplies simplicity; no separate model simplicity
theorem or multiplier classification is required by this consumer. -/
theorem LocalControlWitness.false_of_inner_ree_component_of_central_involutions
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) (m : ℕ) (hm : 1 ≤ m)
    (hcenter : _root_.ReeF4.MarkedStrongClosure.StandardCentralInvolutions m)
    (e : L ≃* _root_.ReeF4.Model m)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := hsimple
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hO : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* _root_.ReeF4.Model m :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e
  exact w.false_of_inner_ree_twoCore_component_of_central_involutions
    H S hUS hST hcore L hL hLM m hm hcenter e' hinner

/-- The literal large Ree carrier predicate used by the source catalogue.
Its only family input is the independently owned standard-center theorem. -/
theorem LocalControlWitness.false_of_inner_ree_model_of_central_involutions
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) (hmodel : _root_.ReeF4.IsReeF4Model L)
    (hcenter : ∀ m, 1 ≤ m →
      _root_.ReeF4.MarkedStrongClosure.StandardCentralInvolutions m)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hmodel
  exact w.false_of_inner_ree_component_of_central_involutions
    H S hUS hST hcore L hL hLM hsimple m hm (hcenter m hm) e hinner

/-- Apply the same family to the original bad centralizer and selected
Sylow, preserving the original inner action of z. -/
theorem LocalControlWitness.false_of_inner_ree_centralizer_component_of_central_involutions
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
    (hcenter : ∀ m, 1 ≤ m →
      _root_.ReeF4.MarkedStrongClosure.StandardCentralInvolutions m)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_ree_model_of_central_involutions
    (centralizer ({u} : Set G)) S hUS hST hcore L hL hLM hsimple hmodel hcenter hinner

end CFSG.Quasithin.Chapter2.BenderFusion
