module

public import Mathlib.GroupTheory.Frattini

/-!
# Frattini subgroups in normal images

For a finite normal subgroup N of H, the image of Φ(N) lies in Φ(H).
A maximal subgroup supplemented by Φ(N) would intersect N in a supplement
to Φ(N), contradicting its nongenerating property. Factoring a homomorphism
through its range gives the corresponding normal-image statement.
This also applies after quotienting the domain by a subgroup of its kernel.

Source application: Aschbacher–Smith, 15.3.11(5i), printed pp.1123–1124.
-/

public section
open Subgroup
namespace Subgroup

/-- The Frattini subgroup of a finite normal subgroup lies in the ambient Frattini subgroup. -/
theorem frattini_map_subtype_le {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal] :
    (frattini N).map N.subtype ≤ frattini H := by
  let F := (frattini N).map N.subtype
  have hFN : F ≤ N := map_subtype_le _
  have hnorm : F.Normal := by infer_instance
  change F ≤ _
  simp only [frattini, Order.radical, le_iInf_iff]
  intro M hM
  by_contra hn
  have htop : M ⊔ F = ⊤ :=
    hM.2 _ (lt_of_le_of_ne le_sup_left (fun he => hn (le_sup_right.trans_eq he.symm)))
  have hgen : M.subgroupOf N ⊔ frattini N = ⊤ := by
    apply top_unique
    intro n hn
    have hn' : (n : H) ∈ M ⊔ F := htop ▸ mem_top _
    obtain ⟨m, hm, f, hf, hmf⟩ := mem_sup_of_normal_right.mp hn'
    have hmN : m ∈ N := by
      have he : m = (n : H) * f⁻¹ := by rw [← hmf]; group
      rw [he]
      exact N.mul_mem n.property (N.inv_mem (hFN hf))
    obtain ⟨f', hf', he⟩ := hf
    change (f' : H) = f at he
    have hnval : (⟨m, hmN⟩ : N) * f' = n := by
      apply Subtype.ext
      change m * (f' : H) = _
      rw [he]
      exact hmf
    rw [← hnval]
    exact mul_mem_sup hm hf'
  have hNM : N ≤ M := by
    have he := frattini_nongenerating hgen
    intro n hn
    exact (show (⟨n, hn⟩ : N) ∈ M.subgroupOf N from he ▸ mem_top _)
  exact hn (hFN.trans hNM)

/-- Frattini elements map into the ambient Frattini subgroup when the image is normal. -/
theorem frattini_map_le_of_normal_range {A B : Type*} [Group A] [Group B]
    [Finite B] (f : A →* B) [f.range.Normal] :
    (frattini A).map f ≤ frattini B := by
  have h := map_le_iff_le_comap.mpr
    (frattini_le_comap_frattini_of_surjective f.rangeRestrict_surjective)
  have hm := (map_mono (f := f.range.subtype) h).trans (frattini_map_subtype_le f.range)
  rw [map_map] at hm
  exact hm

/-- Removing a subgroup of the kernel retains the same normal image. -/
theorem frattini_quotient_lift_map_le {A B : Type*} [Group A] [Group B]
    [Finite B] (N : Subgroup A) [N.Normal] (f : A →* B)
    (hN : N ≤ f.ker) [f.range.Normal] :
    (frattini (A ⧸ N)).map (QuotientGroup.lift N f hN) ≤ frattini B := by
  have hr : (QuotientGroup.lift N f hN).range = f.range := by
    ext b
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N z
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk' N a, rfl⟩
  let : (QuotientGroup.lift N f hN).range.Normal := hr.symm ▸ inferInstance
  exact frattini_map_le_of_normal_range _

end Subgroup
end
