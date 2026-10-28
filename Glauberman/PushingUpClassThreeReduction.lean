module
public import Theory.GroupTheory.ClassThreeInvariantQuotient
public import Theory.GroupTheory.SubgroupTransport.TwistedIteration

/-!
# The class-three reduction from the two chief-filtration layers

The earlier intersection diagram supplies literal shifted intervals and the
central layers N/V and Q/M. The two-block comparison proves that the second
power twist of the marked third commutator escapes the Sylow intersection.
Consequently the actual maximal invariant kernel preserves class three, and
its quotient satisfies the Main Hypothesis with the specified induced power
automorphism and original simple quotient.

This is the characteristic-two reduction in Niles, *Pushing-up in finite
groups* (1979), Lemmas 6.4–6.5, pp.53–54. The raw interval/central-layer
inputs come from Theorem 4.7 and Proposition 5.5; their source construction
is independent of this reduction. No terminal natural extension, reduced
parameter, or class-three contradiction is an input.
-/

public section
open Subgroup NilesRankOneKernel Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H : Type*} [Group H] [Finite H]

/-- The actual reduced quotient from the earlier chief-filtration and shifted
interval data. The quotient automorphism retains its power-twist marking. -/
theorem classThree_reduced_mainHypothesis
    (S : Sylow 2 H) (α : MulAut S) (g : H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K)) (hf : generalizedFitting H = pCore 2 H)
    (Z N Q V M : Subgroup H) [N.Normal] [Q.Normal]
    (hNQ : N ≤ Q)
    (hQpair : Q = (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom)
    (hZV : Z ≤ omegaCenterIn (pCore 2 H))
    (hclass : ((S : Subgroup H).map (MulAut.conj g).toMonoidHom).lowerCentralSeries 3 = ⊥)
    (hZthird : Z ≤ ((S : Subgroup H).map (MulAut.conj g).toMonoidHom).lowerCentralSeries 2)
    (hNV : ⁅(⊤ : Subgroup H), N⁆ ≤ V)
    (hQM : ⁅(⊤ : Subgroup H), Q⁆ ≤ M)
    (E₁ E₂ : ℕ → Subgroup H) (hE₁zero : E₁ 0 = ⊥) (hE₂zero : E₂ 0 = ⊥)
    (n : ℕ)
    (hE₁ : ∀ i ≤ n, E₁ i ≤ N)
    (hE₂ : ∀ i ≤ n, E₂ i ≤ Q)
    (hstep₁ : ∀ i < n,
      image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))) (E₁ i) ⊔ V ≤ E₁ (i + 1))
    (hstep₂ : ∀ i < n,
      image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))) (E₂ i) ⊔ M ≤ E₂ (i + 1))
    (hfinal₁ : image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))) (E₁ n) ≤ N)
    (hfinal₂ : image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))) (E₂ n) ≤ Q)
    (hZ : ∀ i ≤ n, (image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[i] Z ≤ N)
    (hB : ∀ i ≤ n, (image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[i]
      ((image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[n+1] Z) ≤ Q)
    (hN : ∀ i ≤ n+1, (image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[i] N ≤ Q)
    (hescape : ¬ (image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[n+1]
      ((image (α.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[n+1] Z) ≤ Q) :
    let L := (invariantNormalKernel (S : Subgroup H) (α ^ (n+1))).map (S : Subgroup H).subtype
    let q := QuotientGroup.mk' L
    L ≤ pCore 2 H ∧ L ≤ K ∧
      Nonempty (((H ⧸ L) ⧸ K.map q) ≃* (H ⧸ K)) ∧
      generalizedFitting (H ⧸ L) = pCore 2 (H ⧸ L) ∧
      Order.HasUniqueMaximalOver ((S : Subgroup H).map q) ⊤ ∧
      Group.nilpotencyClass (((S : Subgroup H).map (MulAut.conj g).toMonoidHom).map q) = 3 ∧
      ∃ γ : MulAut ((S : Subgroup H).map q),
        (∀ x : S, γ (q.subgroupMap (S : Subgroup H) x) =
          q.subgroupMap (S : Subgroup H) ((α ^ (n+1)) x)) ∧
        NoInvariantNormal ((S : Subgroup H).map q) γ := by
  have hQS : Q ≤ (S : Subgroup H) := hQpair.trans_le inf_le_left
  have hescape' := twice_power_twist_escape (S : Subgroup H) α g Z N Q V M
    hNQ hQS hNV hQM E₁ E₂ hE₁zero hE₂zero n hE₁ hE₂ hstep₁ hstep₂
    hfinal₁ hfinal₂ hZ hB hN hescape
  apply classThree_main_quotient_of_escape S (α ^ (n+1)) g hu K hK hf Z hZV hclass hZthird 2
  simpa only [← hQpair] using hescape'

end Glauberman
