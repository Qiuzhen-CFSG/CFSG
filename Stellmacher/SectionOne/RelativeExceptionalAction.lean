module
public import Stellmacher.SectionOne.OneARelativeAction
public import Stellmacher.SectionOne.LemmaOneSixBounded
public import Theory.GroupAction.ActorSubtypeCommutator
/-!
# The relative exceptional action at measure two

Let A be an elementary abelian subgroup of a faithful Section One actor,
with order at least four, measure two, minimal measure on its nontrivial
subgroups, and a nonquadratic action. Then E=[O₂′(G),A]A is a product of
two copies of SL₂(2), and its odd-core commutator module has order sixteen,
expressed using the original ambient actor [O₂′(G),A].

The relative action setup supplies a Sylow T of E identified exactly with
A restricted to E, and identifies the image of O₂′(E) with [O₂′(G),A].
Subtype transport preserves subgroup cardinalities, measure, and both
action commutators. The bounded version of (1.6) therefore applies. Order
at least four excludes its small alternative; nonquadraticity excludes
both generic product alternatives, leaving the exceptional double-SL₂ case.
The result uses the original module and inherited action throughout.

Source: Stellmacher (9.1), relation (7), Journal of Algebra 190 (1997),
printed p.47, refs/files/stellmacher-n-group.pdf. The explicit measure-two
hypothesis is essential for the bounded (1.6) theorem used here.
-/

namespace Stellmacher.SectionOne
universe u
public theorem relative_doubleSL2_of_m_two_nonquadratic
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hcard : 4 ≤ Nat.card A) (hm : m (V := V) A = 2)
    (hmin : ∀ Y : Subgroup G, Y ≤ A → Y ≠ ⊥ → m (V := V) A ≤ m (V := V) Y)
    (hnon : commutatorAction₂ A V ≠ ⊥) :
    let E : Subgroup G := ⁅oddCore G, A⁆ ⊔ A
    Nonempty (E ≃* (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
      Nat.card (commutatorAction (⁅oddCore G,A⁆ : Subgroup G) V) = 16 := by
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
  have hTcard : Nat.card (T : Subgroup E) = Nat.card A := by
    exact (Subgroup.card_map_of_injective E.subtype_injective).symm.trans
      (congrArg (fun K : Subgroup G => Nat.card K) hTmap)
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
  have hout := lemma_one_six_of_m_le_two hE T hT hcomm hTmin hTm.le
  cases hout with
  | small hs _ => omega
  | doubleSL2 _ he hc _ =>
    refine ⟨he, ?_⟩
    rw [← commutatorAction_map_actor_subtype E (oddCore E), hmap] at hc
    exact hc
  | omegaProduct _ hq _ => exact (hTnon hq).elim
  | sl2Product _ hq _ => exact (hTnon hq).elim
end Stellmacher.SectionOne
