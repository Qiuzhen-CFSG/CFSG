module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS

/-!
# The exact local hypotheses for Higman--Sims recognition

The definition preceding I.4.8 uses an involution centralizer and the full
normalizer of an elementary abelian subgroup of order eight. Their cores are
the intrinsic generalized Fitting subgroups. The first core is the central
product (Q₈ * Q₈) * C₄, specified by actual commuting embedded factors; the
second is C₄³. The quotients are S₅ and L₃(2), respectively.

No simplicity, order, action, or recognition conclusion is part of these
hypotheses. `Recognition` names the universal implication still to be proved;
it is not an axiom or a proof of I.4.8. Its consumer is the nonextraspecial
branch in Chapter14/Section04/CaseOneHS.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, printed p.418,
definition of type HS and Lemma I.4.8.
-/

@[expose] public section
namespace CFSG.Quasithin.HigmanSims
open Subgroup Theory.GroupTheory

/-- The actual central product (Q₈ * Q₈) * C₄. -/
def CoreShape (Q : Type*) [Group Q] : Prop :=
  ∃ B D : Subgroup Q, Nonempty (QuaternionCentralProductData B) ∧
    Nonempty (D ≃* Multiplicative (ZMod 4)) ∧
    Nat.card (B ⊓ D : Subgroup Q) = 2 ∧
    (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧ B ⊔ D = ⊤

/-- Transport preserves the factor embeddings and their common involution. -/
theorem CoreShape.of_equiv {Q R : Type*} [Group Q] [Group R]
    (h : CoreShape Q) (e : Q ≃* R) : CoreShape R := by
  obtain ⟨B, D, ⟨hB⟩, hD, hi, hc, hs⟩ := h
  refine ⟨B.map e.toMonoidHom, D.map e.toMonoidHom,
    ⟨hB.map (e.subgroupMap B)⟩,
    hD.map (fun f => (e.subgroupMap D).symm.trans f), ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
    exact hi
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    change e b * e d = e d * e b
    simpa only [← map_mul] using congrArg e (hc b hb d hd)
  · rw [← Subgroup.map_sup, hs, Subgroup.map_top_of_surjective _ e.surjective]

abbrev involutionCentralizer {G : Type*} [Group G] (z : G) : Subgroup G :=
  centralizer ({z} : Set G)

abbrev localCore {G : Type*} [Group G] (z : G) : Subgroup (involutionCentralizer z) :=
  generalizedFitting (involutionCentralizer z)

/-- All clauses HS1 and HS2, on the literal centralizer and normalizer. -/
structure TypeAt {G : Type*} [Group G] [Finite G] (z : G) (V : Subgroup G) : Prop where
  involution : orderOf z = 2
  elementary : IsElementaryAbelian 2 V
  seed_card : Nat.card V = 8
  centralizer_core : CoreShape (localCore z)
  centralizer_quotient : Nonempty
    ((involutionCentralizer z ⧸ localCore z) ≃* Equiv.Perm (Fin 5))
  seed_le_core : V ≤ (localCore z).map (involutionCentralizer z).subtype
  normalizer_core : Nonempty
    (generalizedFitting (normalizer (V : Set G)) ≃* (Fin 3 → Multiplicative (ZMod 4)))
  normalizer_quotient : ClassicalGroup.IsPSL
    (normalizer (V : Set G) ⧸ generalizedFitting (normalizer (V : Set G))) 3 2

/-- Precisely the source's type-HS hypothesis. -/
def IsType (G : Type*) [Group G] [Finite G] : Prop :=
  ∃ (z : G) (V : Subgroup G), TypeAt z V

/-- The outstanding universal I.4.8 implication, retained as an explicit
premise until its independent producer proves it. -/
def Recognition.{u} : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsType G →
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier)

end CFSG.Quasithin.HigmanSims
