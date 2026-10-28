module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.Pair
public import BenderSuzuki.Converse.Lift

/-!
# Even order of the residual two-point stabilizers

Product disconnection gives a proper subgroup containing an involution.
If it is not strongly embedded, one of its intersections with a distinct
conjugate contains an involution. Double transitivity makes all such
intersections have equal order, so they all have even order. The final
lemma transports this fact to the internal subgroup of `M`.

This is the evenness observation in GLS, Volume 4, Chapter 2, (12A),
used throughout Sections 12–17. Only the action conclusion is needed here;
no local model recognition or generation theorem is assumed.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFchapter1section1 PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Double transitivity makes the orders of all distinct two-point stabilizers equal. -/
public theorem residualPairStabilizer_card_eq
    (ha : ResidualAction Z M) {g t : G} (hg : g ∉ M) (ht : t ∉ M) :
    Nat.card (residualPairStabilizer M g) = Nat.card (residualPairStabilizer M t) := by
  let a : G ⧸ M := QuotientGroup.mk 1
  have hM : MulAction.stabilizer G a = M := MulAction.stabilizer_quotient M
  have hmem : ∀ x : G, x ∈ M ↔ x • a = a := by
    intro x
    simpa only [hM] using (MulAction.mem_stabilizer_iff (G := G) (a := a) (g := x))
  have hne : ∀ x : G, x ∉ M → x⁻¹ • a ≠ a := by
    intro x hx heq
    exact hx ((hmem x).mpr (inv_smul_eq_iff.mp heq).symm)
  have hpos : 0 < Nat.card (G ⧸ M) - 1 := by
    have hcardpos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
    have hcardne : Nat.card (G ⧸ M) ≠ 1 := by
      intro hc
      obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.mp hc
      exact hne t ht (hs.allEq _ _)
    omega
  have heq : ∀ x : G, residualPairStabilizer M x =
      MulAction.stabilizer G a ⊓ MulAction.stabilizer G (x⁻¹ • a) := by
    intro x
    rw [← rightConjugate_stabilizer, hM]
    rfl
  rw [heq g, heq t]
  exact Nat.eq_of_mul_eq_mul_right hpos
    ((Converse.card_stabilizer_eq_twoPoint_mul ha.two_transitive (hne g hg)).symm.trans
      (Converse.card_stabilizer_eq_twoPoint_mul ha.two_transitive (hne t ht)))

/-- If strong embedding fails, every distinct two-point stabilizer has even order. -/
public theorem two_dvd_card_residualPairStabilizer
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t ∉ M) :
    2 ∣ Nat.card (residualPairStabilizer M t) := by
  by_contra hnot
  apply hn
  refine ⟨h.proper, ?_, ?_⟩
  · obtain ⟨z, hz, hzM⟩ := h.nonempty
    exact ⟨z, hzM, h.involutions z hz⟩
  · intro g hg x hxM hxg hx
    let D := residualPairStabilizer M g
    have hxD : x ∈ D := ⟨hxM, hxg⟩
    have hxi : IsInvolution (⟨x, hxD⟩ : D) := BenderSuzuki.IsInvolution.subtype hx hxD
    have hdiv : 2 ∣ Nat.card D := by
      rw [← orderOf_eq_prime hxi.2 hxi.1]
      exact orderOf_dvd_natCard _
    exact hnot ((residualPairStabilizer_card_eq ha hg ht) ▸ hdiv)

/-- The same evenness statement in the internal copy of the two-point stabilizer. -/
public theorem residualPairIn_even
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t ∉ M) :
    2 ∣ Nat.card (residualPairIn M t) := by
  rw [Nat.card_congr (residualPairInEquiv M t).toEquiv]
  exact two_dvd_card_residualPairStabilizer h ha hn ht


end BenderSuzuki.ZD
