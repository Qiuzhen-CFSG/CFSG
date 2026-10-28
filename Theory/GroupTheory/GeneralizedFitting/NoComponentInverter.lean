module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.CentralInverterNormalProduct

/-!
# The normal product in the component-free branch

The Fitting subgroup lies in O_p(G)O_{p'}(G), by its decomposition into
prime cores. If G has no components, this product contains F*(G), hence
contains its own centralizer. An element centralizing O_p(G) and inverting
O_{p'}(G) therefore generates a normal product with the two cores.

Source application: Aschbacher--Smith 2.5.3(4), printed p.553. This proves
the normality step from absence of components, without assuming a desired
Frattini factorization or a split product.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The full Fitting subgroup lies in the product of a prime core and
the complementary prime core. -/
theorem fitting_le_pCore_sup_pPrimeCore (p : ℕ) [Fact p.Prime] :
    fittingSubgroup G ≤ pCore p G ⊔ pPrimeCore p G := by
  rw [fitting_eq_sup_pCore G]
  apply iSup_le
  intro q
  by_cases hqp : q.1.1 = p
  · rw [hqp]
    exact le_sup_left
  · have hcop : Nat.Coprime p (Nat.card (pCore q.1.1 G)) := by
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.1.1) (G := G)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hqp)).pow_right n
    exact (le_sSup ⟨inferInstance, hcop⟩ : pCore q.1.1 G ≤ pPrimeCore p G).trans le_sup_right

/-- In the component-free case the prime-core product is self-centralizing. -/
theorem centralizer_core_product_le_of_no_components (p : ℕ) [Fact p.Prime]
    (hnc : ∀ K : Subgroup G, ¬ IsComponent G K) :
    centralizer ((pCore p G ⊔ pPrimeCore p G : Subgroup G) : Set G) ≤
      pCore p G ⊔ pPrimeCore p G := by
  have hE : componentLayer G = ⊥ := by
    apply bot_unique
    exact sSup_le (fun K hK => (hnc K hK).elim)
  have hF : generalizedFitting G ≤ pCore p G ⊔ pPrimeCore p G := by
    rw [generalizedFitting, hE, sup_bot_eq]
    exact fitting_le_pCore_sup_pPrimeCore p
  exact (centralizer_le hF).trans ((centralizer_generalizedFitting_le G).trans hF)

/-- The original no-component normality step for O_p(G)<z>O_{p'}(G). -/
theorem no_component_inverted_core_product_normal (p : ℕ) [Fact p.Prime]
    (hnc : ∀ K : Subgroup G, ¬ IsComponent G K) (z : G)
    (hfix : z ∈ centralizer (pCore p G : Set G))
    (hinv : ∀ y ∈ pPrimeCore p G, z * y * z⁻¹ = y⁻¹) :
    (pCore p G ⊔ zpowers z ⊔ pPrimeCore p G).Normal := by
  have hh := normal_sup_zpowers_of_centralizes_inverts (pCore p G) (pPrimeCore p G)
    z hfix hinv (centralizer_core_product_le_of_no_components p hnc)
  have he : pCore p G ⊔ pPrimeCore p G ⊔ zpowers z =
      pCore p G ⊔ zpowers z ⊔ pPrimeCore p G := by ac_rfl
  exact he ▸ hh

end Theory.GroupTheory
