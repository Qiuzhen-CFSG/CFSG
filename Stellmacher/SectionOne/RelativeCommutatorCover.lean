module
public import Stellmacher.SectionOne.OneARelativeAction
public import Stellmacher.SectionOne.LemmaOneSixBounded
public import Theory.GroupAction.ActorSubtypeCommutator

/-!
# The relative actor commutator lies in its odd residual module

For an elementary relative actor A of order at least four, measure two,
minimal measure on its nontrivial subgroups, and nonquadratic action,
[V,A] lies in [V,[O₂′(G),A]]. All commutators use the original module and
ambient action; no graph classification conclusion is assumed.

The exact relative Sylow setup transfers the measure and minimum through
subtype inclusion. The bounded (1.6) companion retains the commutator
containment from its exceptional local factor, while small and generic
alternatives are quadratic. Transporting the relative odd core back to G
gives precisely [O₂′(G),A] and the stated ambient containment.

This is the action containment used after Stellmacher (9.1)(7), Journal
of Algebra 190 (1997), printed p.47, refs/files/stellmacher-n-group.pdf,
to show that the elementary image fixes the odd-core fixed summand Y₀.
-/

namespace Stellmacher.SectionOne
universe u
public theorem relative_commutator_le_oddCore_of_m_two_nonquadratic
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hcard : 4 ≤ Nat.card A) (hm : m (V := V) A = 2)
    (hmin : ∀ Y : Subgroup G, Y ≤ A → Y ≠ ⊥ → m (V := V) A ≤ m (V := V) Y)
    (hnon : commutatorAction₂ A V ≠ ⊥) :
    commutatorAction A V ≤ commutatorAction (⁅oddCore G,A⁆ : Subgroup G) V := by
  let E : Subgroup G := ⁅oddCore G, A⁆ ⊔ A
  have hAE : A ≤ E := le_sup_right
  have hAne : A ≠ ⊥ := by
    intro hb
    simp only [hb, Subgroup.card_bot] at hcard
    omega
  let _ := hA
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨T,hTA,hE,hT,hcomm,hmap⟩ := elementary_relative_group_setup h S A hAS hA hAne
  have hTmap : (T : Subgroup E).map E.subtype = A := by
    rw [hTA, Subgroup.map_subgroupOf_eq_of_le hAE]
  have hTm : m (G := E) (V := V) (T : Subgroup E) = 2 := by
    rw [← m_map_subtype, hTmap]
    exact hm
  have hTmin : ∀ Y : Subgroup E, Y ≤ (T : Subgroup E) → Y ≠ ⊥ →
      m (G := E) (V := V) (T : Subgroup E) ≤ m (G := E) (V := V) Y := by
    intro Y hYT hYne
    rw [← m_map_subtype E (T : Subgroup E), ← m_map_subtype E Y, hTmap]
    apply hmin (Y.map E.subtype)
    · exact hTmap ▸ Subgroup.map_mono hYT
    · intro hbot
      apply hYne
      apply Subgroup.map_injective E.subtype_injective
      simpa only [Subgroup.map_bot] using hbot
  have hTnon : commutatorAction₂ (T : Subgroup E) V ≠ ⊥ := by
    rw [← commutatorAction₂_map_actor_subtype E (T : Subgroup E), hTmap]
    exact hnon
  have hcover := (lemma_one_six_of_m_le_two_with_commutator
    hE T hT hcomm hTmin hTm.le).2 hTnon
  rw [← commutatorAction_map_actor_subtype E (T : Subgroup E), hTmap,
    ← commutatorAction_map_actor_subtype E (oddCore E), hmap] at hcover
  exact hcover
end Stellmacher.SectionOne
