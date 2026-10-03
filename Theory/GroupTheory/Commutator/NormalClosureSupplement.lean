module
public import Theory.GroupTheory.Commutator.NormalClosure
/-!
# Normal-closure commutators with a centralizing supplement

Let R be normal and suppose R together with S generates the whole group.
If S centralizes A, then [A^G,G] equals [A,R]. No finiteness or solvability
hypothesis is needed. This supplies the omega-center description of the
selected residual module in Stellmacher (6.1), Journal of Algebra 190
(1997), p.30, with A=Ω₁Z(B), R=O²(E), and S=B.

Every group element has the form rs. The commutator product formula and
centralization show [A,G]=[A,R]. The former subgroup is normal, so the
normal-closure commutator transfer gives [A^G,G]≤[A,G]; monotonicity gives
the reverse containment.
-/

open scoped commutatorElement
namespace Subgroup
public theorem normalClosure_commutator_eq_of_centralizing_supplement
    {G : Type*} [Group G] (A R S : Subgroup G) [R.Normal]
    (hgen : R ⊔ S = ⊤) (hAS : A ≤ centralizer (S : Set G)) :
    ⁅normalClosure (A : Set G), (⊤ : Subgroup G)⁆ = ⁅A,R⁆ := by
  have heq : ⁅A, (⊤ : Subgroup G)⁆ = ⁅A,R⁆ := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro a ha g hg
      have hg' : g ∈ R ⊔ S := by simp [hgen]
      obtain ⟨r, hr, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hg'
      have hcomm : ⁅a,s⁆ = 1 := by
        apply commutatorElement_eq_one_iff_mul_comm.mpr
        exact ((mem_centralizer_iff.mp (hAS ha)) s hs).symm
      rw [commutatorElement_mul_right_eq_mul_conj, hcomm]
      simpa using commutator_mem_commutator ha hr
    · exact commutator_mono le_rfl le_top
  let C := ⁅A, (⊤ : Subgroup G)⁆
  let _ : C.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (normalizer_commutator_ge_right A ⊤))
  apply le_antisymm
  · rw [← heq, commutator_comm]
    exact commutator_normalClosure_le_of_normal ⊤ A C (by rw [commutator_comm])
  · rw [← heq]
    exact commutator_mono le_normalClosure le_rfl
end Subgroup
