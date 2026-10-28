module
public import Theory.GroupAction.NormalizerFrattiniTransport

/-!
# Restricting an irreducible normalizer action to an overgroup

An irreducible action on P/Φ(P) by S remains irreducible under the full
normalizer of P inside an overgroup M containing both P and S. The proof
uses the literal subgroup inclusion and its induced Frattini equivalence.
This is used for the Sylow complement of Ξ_p(L) in the original 13.1.12
component sieve, Aschbacher–Smith, printed p.875.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- The normalizer inside an overgroup contains the supplied irreducible actor. -/
theorem normalizerFrattiniIrreducible_subgroupOf (P S M : Subgroup G)
    (hPM : P ≤ M) (hSM : S ≤ M) (hn : S ≤ normalizer (P : Set G))
    (hirr : ∀ A : Subgroup (P ⧸ frattini P),
      (∀ s : S, ∀ a ∈ A, frattiniConjugationHom S P hn s a ∈ A) →
        A = ⊥ ∨ A = ⊤) : IsNormalizerFrattiniIrreducible (P.subgroupOf M) := by
  let Pm := P.subgroupOf M
  let ep : P ≃* Pm := (subgroupOfEquivOfLe hPM).symm
  let e : (P ⧸ frattini P) ≃* (Pm ⧸ frattini Pm) :=
    QuotientGroup.congr _ _ ep (frattini_map_mulEquiv ep)
  let sm (s : S) : normalizer (Pm : Set M) :=
    ⟨⟨s,hSM s.property⟩,P.le_normalizer_comap M.subtype (hn s.property)⟩
  have he (s : S) (a : P ⧸ frattini P) :
      e (frattiniConjugationHom S P hn s a) =
        frattiniConjugationHom (normalizer (Pm : Set M)) Pm le_rfl (sm s) (e a) := by
    induction a using QuotientGroup.induction_on with | H a =>
      change e (frattiniConjugationHom S P hn s (QuotientGroup.mk' _ a)) =
        frattiniConjugationHom _ _ le_rfl (sm s) (QuotientGroup.mk' _ (ep a))
      simp only [frattiniConjugationHom,MonoidHom.comp_apply,quotientAut_apply_mk]
      rfl
  intro A hA
  have hh : ∀ s : S, ∀ a ∈ A.comap e.toMonoidHom,
      frattiniConjugationHom S P hn s a ∈ A.comap e.toMonoidHom := by
    intro s a ha
    change e (frattiniConjugationHom S P hn s a) ∈ A
    rw [he]
    exact hA (sm s) (e a) ha
  rcases hirr (A.comap e.toMonoidHom) hh with hb | ht
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) hb
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
end Subgroup
