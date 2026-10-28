module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products of a conjugacy class inside an abelian subgroup

The normalizer of an abelian subgroup permutes its intersection with any
ambient conjugacy class. It therefore centralizes the product of that
intersection. This avoids requiring the ambient group to be commutative.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined 1 March 2004 manuscript, the reduction preceding
13.6.8, printed p.928. There the intersection consists of three singular
vectors and their product is v.
-/

namespace Subgroup

open scoped BigOperators IsMulCommutative
variable {G : Type*} [Group G]

/-- The normalizer fixes the product of the conjugates of z inside V. -/
public theorem normalizer_le_centralizer_of_conjugacy_product
    (V : Subgroup G) [IsMulCommutative V] (z v : G) (s : Finset V)
    (hs : ∀ x : V, x ∈ s ↔ ∃ c : G, MulAut.conj c z = (x : G))
    (hprod : ((∏ x ∈ s, x : V) : G) = v) :
    normalizer (V : Set G) ≤ centralizer ({v} : Set G) := by
  intro g hg
  let f : MulAut V := V.normalizerMonoidHom ⟨g, hg⟩
  have hf (x : V) : (f x : G) = g * (x : G) * g⁻¹ := rfl
  have hmem (x : V) : x ∈ s ↔ f x ∈ s := by
    rw [hs, hs]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨g * c, ?_⟩
      rw [hf, ← hc]
      simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨c, hc⟩
      refine ⟨g⁻¹ * c, ?_⟩
      have he := congrArg (fun y : G => g⁻¹ * y * g) hc
      simpa [hf, MulAut.conj_apply, mul_assoc] using he
  have hfix : f (∏ x ∈ s, x) = ∏ x ∈ s, x := by
    rw [map_prod]
    exact Finset.prod_equiv f.toEquiv hmem (fun _ _ => rfl)
  have he := congrArg Subtype.val hfix
  change g * ((∏ x ∈ s, x : V) : G) * g⁻¹ = ((∏ x ∈ s, x : V) : G) at he
  rw [hprod] at he
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

end Subgroup
