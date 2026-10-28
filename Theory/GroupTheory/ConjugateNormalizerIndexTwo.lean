module
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Mathlib.GroupTheory.IndexNormal

/-!
# Index-two factor stabilizers normalize the opposite factor

The stabilizer inside T is normal because it has index two. Its conjugation
by the chosen t therefore still normalizes L, which says that the original
stabilizer normalizes Lᵗ as well.

Source: the two-factor configuration in Aschbacher–Smith, D.3.6, p.196.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem normalizes_conjugate_of_index_two (L T : Subgroup G)
    (hi : (normalizer (L : Set G)).relIndex T = 2)
    {t : G} (ht : t ∈ T) :
    T ⊓ normalizer (L : Set G) ≤
      normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let S := (normalizer (L : Set G)).subgroupOf T
  let : S.Normal := normal_of_index_eq_two hi
  intro s hs
  have hm : t⁻¹ * s * t ∈ normalizer (L : Set G) := by
    have hh := (inferInstance : S.Normal).conj_mem ⟨s, hs.1⟩ hs.2 (⟨t, ht⟩ : T)⁻¹
    simpa only [S, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hh
  rw [←map_equiv_normalizer_eq L (MulAut.conj t)]
  refine ⟨t⁻¹ * s * t, hm, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
    mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Theory.GroupTheory
