module

public import Theory.SpecificGroups.BinaryLinear.AffineThree.Heisenberg

/-!
# Quaternion factors and the affine swapping obstruction

The explicit two quaternion factors exhaust all quaternion subgroups of the
order-32 Heisenberg group. Any injective embedding admitting the coordinate
swap as conjugation therefore makes every quaternion subgroup nonnormal in
the overgroup. This is relative normality, as required by I.4.6 (p.417).
-/

@[expose] public section
open Subgroup
namespace BinaryLinear.Affine.ThreeCore

theorem factors_intersect : (quaternionEmbedding false).range ⊓
    (quaternionEmbedding true).range = Subgroup.center Q := by
  ext x
  rw [center_iff]
  change (∃ q, quaternionEmbedding false q = x) ∧
    (∃ q, quaternionEmbedding true q = x) ↔ _
  revert x
  decide +kernel

noncomputable def factors : QuaternionCentralProductData Q where
  left := (quaternionEmbedding false).range
  right := (quaternionEmbedding true).range
  left_model := ⟨(MonoidHom.ofInjective (quaternionEmbedding_injective false)).symm⟩
  right_model := ⟨(MonoidHom.ofInjective (quaternionEmbedding_injective true)).symm⟩
  intersection_card := by rw [factors_intersect]; exact center_card
  commute := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact quaternion_factors_commute a b
  span := by
    apply top_unique
    intro x _
    obtain ⟨⟨a,b⟩,rfl⟩ := quaternion_product_surjective x
    exact mul_mem (mem_sup_left ⟨a,rfl⟩) (mem_sup_right ⟨b,rfl⟩)

theorem swap_moves_factor (side : Bool) :
    swap (qi side) ∉ (quaternionEmbedding side).range := by
  change ¬ ∃ q, quaternionEmbedding side q = swap (qi side)
  cases side <;> decide +kernel

theorem qi_mem_factor (side : Bool) : qi side ∈ (quaternionEmbedding side).range := by
  change ∃ q, quaternionEmbedding side q = qi side
  cases side <;> decide +kernel

theorem quaternion_nonnormal_of_swap {K : Type*} [Group K]
    (f : Q →* K) (hf : Function.Injective f)
    (s : K) (hs : ∀ q, s * f q * s⁻¹ = f (swap q))
    (R : Subgroup Q) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    ¬ (R.map f).Normal := by
  intro hn
  have bad (side : Bool) (he : R = (quaternionEmbedding side).range) : False := by
    have hq : f (qi side) ∈ R.map f := mem_map_of_mem f (he ▸ qi_mem_factor side)
    have h := hn.conj_mem _ hq s
    rw [hs] at h
    obtain ⟨q,hq,heq⟩ := h
    apply swap_moves_factor side
    rw [← hf heq, ← he]
    exact hq
  rcases (factors.quaternion_subgroup_iff R).mp hR with hl | hr
  · exact bad false hl
  · exact bad true hr

end BinaryLinear.Affine.ThreeCore
