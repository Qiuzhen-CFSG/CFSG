module
public import Theory.GroupTheory.NormalizerActionEmbedding
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Full normalizer actions and centralizing supplements

A full normalizer action on K forces a larger centralizer of A whenever the
pointwise automorphism fixer of A is larger than A. A normalized supplement
also computes the normalizer index through its intersection with K.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem lt_centralizer_of_surjective_normalizer_action (K A : Subgroup G)
    (hAK : A ≤ K) (hAA : A ≤ centralizer (A : Set G))
    (hs : Function.Surjective K.normalizerMonoidHom)
    (hc : Nat.card A < Nat.card (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K))) :
    A < centralizer (A : Set G) := by
  apply lt_of_le_of_ne hAA
  intro he
  let j := normalizerCentralizerHom K A A (hAK.trans K.le_normalizer) hAA
  have hj : Function.Surjective j := by
    intro a
    obtain ⟨n, hn⟩ := hs (a : MulAut K)
    have hnC : (n : G) ∈ centralizer (A : Set G) := by
      intro x hx
      have hfix := a.property ⟨⟨x,hAK hx⟩,hx⟩
      change (a : MulAut K) ⟨x,hAK hx⟩ = ⟨x,hAK hx⟩ at hfix
      rw [← hn] at hfix
      have hp := congrArg Subtype.val hfix
      change (n : G) * x * (n : G)⁻¹ = x at hp
      exact (mul_inv_eq_iff_eq_mul.mp hp).symm
    have hnA : (n : G) ∈ A := he.symm ▸ hnC
    refine ⟨⟨n,hnA⟩,?_⟩
    apply Subtype.ext
    ext k
    change ((normalizerCentralizerHom K A A (hAK.trans K.le_normalizer) hAA
      ⟨n,hnA⟩ : MulAut K) k : G) = ((a : MulAut K) k : G)
    rw [normalizerCentralizerHom_apply]
    exact congrArg (fun b : MulAut K => (b k : G)) hn
  exact (not_le_of_gt hc) (Nat.card_le_card_of_surjective j hj)

theorem card_supplement_eq_inf_mul_relIndex (K D : Subgroup G)
    (hN : normalizer (K : Set G) = K ⊔ D) :
    Nat.card D = Nat.card (K ⊓ D : Subgroup G) * K.relIndex (normalizer (K : Set G)) := by
  have hDN : D ≤ normalizer (K : Set G) := by rw [hN]; exact le_sup_right
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes K D hDN
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) K (normalizer (K : Set G))
    bot_le K.le_normalizer
  simp only [relIndex_bot_left] at hi
  rw [← hN,←hi] at hp
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card K from Nat.card_pos)
  calc
    Nat.card K * Nat.card D = Nat.card (K ⊓ D : Subgroup G) *
      (Nat.card K * K.relIndex (normalizer (K : Set G))) := hp
    _ = Nat.card K * (Nat.card (K ⊓ D : Subgroup G) *
      K.relIndex (normalizer (K : Set G))) := by ac_rfl

end Subgroup
