module

public import Theory.SpecificGroups.Triality.MarkedStrongClosure
public import Theory.SpecificGroups.Triality.Model.QTKE
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding genuine binary triality components in the Bender inspection

The actual quotient marker is a nonidentity involution centralizing its
Sylow. The genuine triality Sylow-center calculation and two internal Weyl
conjugations produce noncommuting returning conjugates in that same Sylow.
The existing marked-quotient adapter contradicts abelian strong closure.

The simple source consumer uses the simplicity supplied by 1.1.5(3)(a),
and converts L to L/O₂(L) without a model-certification premise. The last
consumer uses the original C_G(u), selected Sylow, and z-action. The binary
field predicate includes exponent one. No local block-generation hypothesis
or exhaustive involution classification is added.

Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, and Proposition 2.2.2,
pp.519--520, combined 1 March 2004 manuscript.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The quotient form retains every central two-kernel permitted by the
original source adapter. The marked pair is proved inside the actual model. -/
theorem LocalControlWitness.false_of_inner_triality_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (P : _root_.Triality.Standard.Parameters) (hp : P.prime = 2)
    (e : (L ⧸ pCore 2 L) ≃* _root_.Triality.Standard.Carrier P)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  exact _root_.Triality.Standard.MarkedStrongClosure.sylow_noncommuting_conjugates P hp

/-- Source 1.1.5(3)(a) supplies simplicity of L. The genuine triality model
therefore excludes this component, uniformly including q=2. -/
theorem LocalControlWitness.false_of_inner_triality_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L)
    (P : _root_.Triality.Standard.Parameters) (hp : P.prime = 2)
    (e : L ≃* _root_.Triality.Standard.Carrier P)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := hsimple
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hO : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* _root_.Triality.Standard.Carrier P :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e
  exact w.false_of_inner_triality_twoCore_component H S hUS hST hcore L hL hLM
    P hp e' hinner

/-- Consume the literal binary field-order predicate used by the source
Theorem C branch, rather than the legacy auxiliary triality construction. -/
theorem LocalControlWitness.false_of_inner_triality_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) (n : ℕ) (hn : 0 < n)
    (hm : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) L)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨e⟩ := (_root_.Triality.Standard.isTrialityGroupAt_binary_iff L n hn).mp hm
  exact w.false_of_inner_triality_component H S hUS hST hcore L hL hLM hsimple
    (_root_.Triality.Standard.binaryParameters n hn) rfl e hinner

/-- The actual bad-centralizer application keeps the source Sylow subtype
maps and original z, with no additional model-local premises. -/
theorem LocalControlWitness.false_of_inner_triality_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (hsimple : IsSimpleGroup L) (n : ℕ) (hn : 0 < n)
    (hm : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) L)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_triality_model (centralizer ({u} : Set G)) S hUS hST hcore
    L hL hLM hsimple n hn hm hinner

end CFSG.Quasithin.Chapter2.BenderFusion
