module

public import Theory.GroupTheory.SubgroupConjugation

/-!
# Element fusion and conjugate-subgroup incidence

The normalizer of X controls fusion of x into X exactly when C_G(x) is
transitive on conjugates of X containing x. In either direction, multiply
the given transporter by one fixing the other coordinate of the incident
pair. No finiteness or prime-order assumption is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.1.7(1), printed p.21. Conjugation here is on the left.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- The exact element/subgroup incidence equivalence of A.1.7(1). -/
public theorem element_fusion_iff_centralizer_incidence (X : Subgroup G) (x : G) :
    (∀ y ∈ X, IsConj x y →
      ∃ n ∈ normalizer (X : Set G), MulAut.conj n x = y) ↔
    (∀ g : G, x ∈ X.conjBy g →
      ∃ c ∈ centralizer ({x} : Set G), X.conjBy c = X.conjBy g) := by
  constructor
  · intro hf g hg
    obtain ⟨y, hy, he⟩ := hg
    have hxy : IsConj x y := (isConj_iff.mpr ⟨g, he⟩).symm
    obtain ⟨n, hn, hnxy⟩ := hf y hy hxy
    refine ⟨g * n, ?_, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      change MulAut.conj (g * n) x = x
      calc
        _ = MulAut.conj g (MulAut.conj n x) := by simp [MulAut.conj_apply, mul_assoc]
        _ = x := by rw [hnxy]; exact he
    · rw [conjBy_mul, show X.conjBy n = X from mem_normalizer_iff_map_conj_eq.mp hn]
  · intro hc y hy hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    have hx : x ∈ X.conjBy g⁻¹ := by
      refine ⟨y, hy, ?_⟩
      rw [← hg]
      simp [mul_assoc]
    obtain ⟨c, hc, he⟩ := hc g⁻¹ hx
    refine ⟨g * c, mem_normalizer_iff_map_conj_eq.mpr ?_, ?_⟩
    · change X.conjBy (g * c) = X
      rw [conjBy_mul, he, conjBy_inv']
    · have hcx : MulAut.conj c x = x :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)
      calc
        _ = MulAut.conj g (MulAut.conj c x) := by simp [MulAut.conj_apply, mul_assoc]
        _ = y := by rw [hcx]; exact hg

end Subgroup
