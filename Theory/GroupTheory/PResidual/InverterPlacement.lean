module

public import Theory.GroupTheory.PResidual.InnerInverter
public import Theory.GroupTheory.PCoreInRestriction

/-!
# A two-perfect actor contained in a normalized inverter subgroup

If X normalizes K and an element of K inverts X modulo O₂(X), the image
of X in N(K)/K is a two-group. Two-perfectness then forces X≤K.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Inversion modulo the full two-core by an element of a normalized
subgroup places the whole two-perfect actor in that subgroup. -/
theorem le_of_normalized_inverter (X K : Subgroup G)
    (hX : IsPPerfect 2 X) (hXN : X ≤ normalizer (K : Set G))
    (t : G) (ht : t ∈ K)
    (hinv : ∀ x ∈ X, t*x*t⁻¹*x ∈ X.pCoreIn 2) : X ≤ K := by
  let N := normalizer (K : Set G)
  let B := X.subgroupOf N
  let C := K.subgroupOf N
  let e : B ≃* X := subgroupOfEquivOfLe hXN
  have hB : IsPPerfect 2 B := hX.of_surjective e.symm.toMonoidHom e.symm.surjective
  let u : N := ⟨t,K.le_normalizer ht⟩
  have hc : B ≤ C := le_normal_of_inversion_mod_twoCore B ⊥ C hB
    IsPGroup.of_bot (by rw [normalizer_eq_top]; exact le_top) bot_le u 1 (one_mem _)
    (by simp only [inv_one,one_mul]; exact ht)
    (by
      intro x hx
      change u*x*u⁻¹*x ∈ (X.subgroupOf N).pCoreIn 2
      rw [pCoreIn_subgroupOf 2 X N hXN]
      exact hinv x hx)
  intro x hx
  exact hc (show (⟨x,hXN hx⟩ : N) ∈ B from hx)

end Subgroup
