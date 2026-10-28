module

public import Stellmacher.OmegaOneCenterMap

/-!
# A small fixed hyperplane determines the Sylow omega center

Suppose an elementary abelian subgroup `A` of order at most four is normalized
by `S` and contains its omega center. If an index-two subgroup `N` of `A` is
normal in an overgroup `P` of `S`, and `P` does not centralize the omega center,
then `A` equals that omega center. No Sylow hypothesis on `S` is needed.

Index multiplicativity bounds the order of `N` by two. If `N` is trivial,
then `A` has order two, so its normalizer centralizes it; the exponent-two
condition puts all of `A` in the omega center of `S`. Otherwise `N` has order
two and is centralized by `P`, hence lies in the omega center. The index-two
condition makes every subgroup between `N` and `A` equal to an endpoint.
The smaller endpoint contradicts the assumed nonzero commutator with `P`.

This is the elementary small-module reduction in Stellmacher (6.3), journal
page 31, refs/latex/stellmacher-n-group.tex. Normality of the fixed hyperplane
is an explicit input, to be established by the source-specific consumer.
-/

namespace Stellmacher

private theorem normalizer_le_centralizer_of_card_two
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (hK : Nat.card K = 2) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hK
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  by_cases h1 : k = 1
  · simp [h1]
  have hkt : (⟨k, hk⟩ : K) = t := ht_unique ⟨k, hk⟩ (by
    intro he
    exact h1 (congrArg Subtype.val he))
  have hc : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hc1 : g * k * g⁻¹ ≠ 1 := by
    intro he
    have he' := congrArg (fun x : G => g⁻¹ * x * g) he
    exact h1 (by simpa [mul_assoc] using he')
  have hct : (⟨g * k * g⁻¹, hc⟩ : K) = t := ht_unique ⟨_, hc⟩ (by
    intro he
    exact hc1 (congrArg Subtype.val he))
  have he := congrArg (fun x : K => (x : G) * g) (hct.trans hkt.symm)
  simpa [mul_assoc] using he.symm

/-- A small normal fixed hyperplane forces the containing module to equal the omega center. -/
public theorem omega_eq_of_small_normal_fixed_hyperplane
    {G : Type*} [Group G] [Finite G] (S P A N : Subgroup G)
    [IsElementaryAbelian 2 A]
    (hSP : S ≤ P) (hAS : A ≤ S)
    (hSA : S ≤ Subgroup.normalizer (A : Set G))
    (hOmega : omegaOneCenterAmbient S ≤ A)
    (hcard : Nat.card A ≤ 4) (hNA : N ≤ A)
    (hNnormal : (N.subgroupOf P).Normal)
    (hidx : N.relIndex A = 2)
    (hcomm : ⁅P, omegaOneCenterAmbient S⁆ ≠ ⊥) :
    A = omegaOneCenterAmbient S := by
  have hcardmul := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) N A bot_le hNA
  simp only [Subgroup.relIndex_bot_left, hidx] at hcardmul
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hNsmall : Nat.card N = 1 ∨ Nat.card N = 2 := by omega
  rcases hNsmall with hN1 | hN2
  · have hA2 : Nat.card A = 2 := by omega
    have hSc : S ≤ Subgroup.centralizer (A : Set G) :=
      hSA.trans (normalizer_le_centralizer_of_card_two A hA2)
    apply le_antisymm ?_ hOmega
    intro a ha
    apply (mem_omegaOneCenterAmbient_iff S a).mpr
    refine ⟨hAS ha, elemPow_eq_one_of_isElementaryAbelian a ha, ?_⟩
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hSc hs) a ha).symm
  · have hPN : P ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hNA.trans (hAS.trans hSP))).mp hNnormal
    have hPc : P ≤ Subgroup.centralizer (N : Set G) :=
      hPN.trans (normalizer_le_centralizer_of_card_two N hN2)
    have hNO : N ≤ omegaOneCenterAmbient S := by
      intro n hn
      apply (mem_omegaOneCenterAmbient_iff S n).mpr
      refine ⟨hAS (hNA hn), elemPow_eq_one_of_isElementaryAbelian n (hNA hn), ?_⟩
      intro s hs
      exact (Subgroup.mem_centralizer_iff.mp (hPc (hSP hs)) n hn).symm
    have hmul := Subgroup.relIndex_mul_relIndex N (omegaOneCenterAmbient S) A hNO hOmega
    rw [hidx] at hmul
    have hor : N.relIndex (omegaOneCenterAmbient S) = 1 ∨
        (omegaOneCenterAmbient S).relIndex A = 1 := by
      have hdvd : N.relIndex (omegaOneCenterAmbient S) ∣ 2 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with he | he
      · exact Or.inl he
      · rw [he] at hmul
        exact Or.inr (by omega)
    rcases hor with he | he
    · have hON := Subgroup.relIndex_eq_one.mp he
      exfalso
      apply hcomm
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      exact Subgroup.mem_centralizer_iff.mp (hPc hp) o (hON ho)
    · exact le_antisymm (Subgroup.relIndex_eq_one.mp he) hOmega

end Stellmacher
