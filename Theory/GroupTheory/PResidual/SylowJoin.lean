module
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Prime-residual joins of Sylow-normalized subgroups

The Sylow subgroup supplements the prime residual. If it normalizes R,
the whole group therefore normalizes Oᵖ(G)R. When R lies in the Sylow
subgroup, the intersection of this product with the Sylow subgroup is
(Oᵖ(G)∩T)R, with both original factors retained.

Source application: Aschbacher--Smith 14.3.22, printed p.999, for the
transfer quotient by O²(H)R.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow-normalized subgroup joined to the prime residual is normal. -/
theorem pResidual_sup_normal_of_sylow_normalizes {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (R : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G)) :
    (pResidual p G ⊔ R).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top T]
  refine sup_le (le_sup_left.trans (pResidual p G ⊔ R).le_normalizer) ?_
  exact hn.trans (normalizer_le_normalizer_sup_of_normalizer_le_right
    (show normalizer (R : Set G) ≤ normalizer (pResidual p G : Set G) from
      le_normalizer_of_normal))

omit [Finite G] in
/-- Joining a normalized subgroup of T to a normal residual preserves its
literal intersection with T. -/
theorem pResidual_sup_inf_sylow {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (R : Subgroup G) (hR : R ≤ (T : Subgroup G)) :
    (pResidual p G ⊔ R) ⊓ (T : Subgroup G) =
      (pResidual p G ⊓ (T : Subgroup G)) ⊔ R := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, r, hr, he⟩ := mem_sup_of_normal_left.mp hx.1
    have hyT : y ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem hx.2 ((T : Subgroup G).inv_mem (hR hr))
      simpa only [← he, mul_inv_cancel_right] using hh
    rw [← he]
    exact mul_mem_sup ⟨hy, hyT⟩ hr
  · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hR)
end Subgroup
