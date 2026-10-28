module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ElementarySylowFixers.Certificate
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure

/-!
# Pointwise Sylow fixers of HS

The intrinsic orbit certificate leaves only the identity and the marked
central involution in the graph-group centralizer of the three Sylow
generators. Every abstract automorphism is realized by that graph group.
Conjugating any Sylow to the certified subgroup therefore bounds its full
pointwise automorphism fixer by two.

Source: GLS3 Table 5.3m and the intrinsic action calculation used in
Aschbacher–Smith, proof of 13.6.6, printed p.927. The original ATLAS data
and their attribution are retained by the imported certificate.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.HS.ElementarySylowFixers
open EvenLocalCandidates NormalizerIndex

private theorem fixes_base_cases (α : MulAut Carrier)
    (hfix : ∀ x ∈ subgroup, α x = x) : α = 1 ∨ α = MulAut.conj e0 := by
  obtain ⟨p, rfl⟩ := normalizer_surjective_of_pointStabilizer_map pointStabilizer_map α
  have hc : ∀ i, Commute p.val (Certificate.gen i) := by
    intro i
    have hx := hfix (sylowGenerator i) (subset_closure ⟨i, rfl⟩)
    have he := congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100))) hx
    change p.val * (sylowGenerator i : Equiv.Perm (Fin 100)) * p.val⁻¹ =
      (sylowGenerator i : Equiv.Perm (Fin 100)) at he
    rw [← Certificate.gen_eq] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  obtain ⟨i, hi⟩ := Certificate.centralizer_cover p.val hc
  have hg := NormalizerIndex.normalizer_le_graphGroup p.property
  rw [hi] at hg
  rcases Certificate.candidate_graph_screen i ((mem_graphGroup_iff _).mp hg _ _) with h | h
  · left
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change p.val * x.val * p.val⁻¹ = x.val
    rw [hi.trans h]
    simp
  · right
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change p.val * x.val * p.val⁻¹ = e0.val * x.val * e0.val⁻¹
    rw [hi.trans h]

/-- The bound holds for the full fixer, with no order restriction on its automorphisms. -/
theorem sylow_fixer_card_le_two (P : Sylow 2 Carrier)
    (A : Subgroup (MulAut Carrier))
    (hfix : ∀ α ∈ A, ∀ x ∈ P, α x = x) : Nat.card A ≤ 2 := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier BlockNormalizer.baseSylow P
  let e : MulAut Carrier := MulAut.conj g
  have hfixed (α : A) (x : Carrier) (hx : x ∈ subgroup) :
      MulAut.congr e.symm α x = x := by
    have hmem : e x ∈ P := by
      rw [← hg]
      change e x ∈ subgroup.map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom hx
    change e.symm ((α : MulAut Carrier) (e x)) = x
    rw [hfix α α.property _ hmem, e.symm_apply_apply]
  let f : A → ({1, MulAut.conj e0} : Finset (MulAut Carrier)) := fun α =>
    ⟨MulAut.congr e.symm α, by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        fixes_base_cases _ (hfixed α)⟩
  have hf : Function.Injective f := by
    intro α β he
    apply Subtype.ext
    exact (MulAut.congr e.symm).injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective f hf).trans (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two)

end Sporadic.LeechRelated.HS.ElementarySylowFixers
