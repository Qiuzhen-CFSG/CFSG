module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Setup
public import Theory.GroupTheory.IndexTwoDihedralNormalizer

/-!
# The normalizer of the exchanged-factor stabilizer inside H

The index-two subgroup H₀ is the normalizer in H of the first exchanged
factor. Its image in the literal H/O₂(H) is the commuting product of the
two odd dihedral factors. Their Sylow two-subgroups are self-normalizing;
lifting through the two-group kernel gives the same property in H₀.
The index-two coset calculation then proves N_H(N_T(H₁)) = T.

Only the earlier-source exchanged-factor setup is used. The larger
normalizer in Mc remains the separate closure argument of 14.6.16.

Source: Aschbacher--Smith, 14.6.12 and 14.6.16, printed pp.1031,1035.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- The factor normalizer is exactly the source subgroup of index two. -/
theorem exchanged_factor_normalizer_eq
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    H ⊓ normalizer (H1 : Set G) = H0 := by
  obtain ⟨t,ht,htN,_⟩ := d.exchanged
  have ht0 : (⟨t,hTH ht⟩ : H) ∉ H0.subgroupOf H := fun hh => htN (d.normalizes_first hh)
  apply le_antisymm _ (le_inf d.zero_le d.normalizes_first)
  intro x hx
  by_contra hx0
  have hx0' : (⟨x,hx.1⟩ : H) ∉ H0.subgroupOf H := hx0
  have hh : (⟨t,hTH ht⟩ : H)⁻¹ * ⟨x,hx.1⟩ ∈ H0.subgroupOf H :=
    ((H0.subgroupOf H).mul_mem_iff_of_index_two d.index).mpr
      (by simp only [inv_mem_iff,ht0,hx0'])
  have htn : t⁻¹ ∈ normalizer (H1 : Set G) := by
    have hprod := (normalizer (H1 : Set G)).mul_mem
      (d.normalizes_first hh) ((normalizer (H1 : Set G)).inv_mem hx.2)
    change (t⁻¹*x)*x⁻¹ ∈ normalizer (H1 : Set G) at hprod
    simpa only [mul_inv_cancel_right] using hprod
  exact htN ((normalizer (H1 : Set G)).inv_mem_iff.mp htn)

variable [Finite G]

/-- All Sylow two-subgroups of H₀ are self-normalizing, by the actual
H/O₂(H) quotient and its two commuting dihedral factors. -/
theorem exchanged_zero_sylow_self_normalizing
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2)
    (P : Sylow 2 (H0.subgroupOf H)) :
    normalizer (P : Set (H0.subgroupOf H)) = P := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := q.subgroupMap (H0.subgroupOf H)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((q.subgroupMap (H0.subgroupOf H)).ker)
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := H)).comap_subtype
  have he : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    unfold actorImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le), d.join_eq]
  have hn : Odd p := by rcases d.prime with rfl | rfl <;> decide
  obtain ⟨e1⟩ := d.first_model
  obtain ⟨e2⟩ := d.second_model
  have hc : actorImage H H1 ≤ centralizer (actorImage H H2 : Set _) := by
    intro x hx y hy
    exact (d.actors_commute x hx y hy).symm
  apply Sylow.self_normalizing_of_two_kernel f (q.subgroupMap_surjective _) hk
  intro Q
  exact Sylow.self_normalizing_of_surjective (MulEquiv.subgroupCongr he.symm).toMonoidHom
    (MulEquiv.subgroupCongr he.symm).surjective
    (Sylow.self_normalizing_dihedral_join _ _ d.actors_disjoint hc p hn e1 e2) Q

/-- The literal N_T(H₁) has normalizer T inside the actual H. -/
theorem exchanged_factor_normalizer_in_H
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    H ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G) := by
  have he := exchanged_factor_normalizer_eq a T hTH p H0 H1 H2 d
  have hS : (T : Subgroup G) ⊓ normalizer (H1 : Set G) = (T : Subgroup G) ⊓ H0 := by
    rw [← he, ← inf_assoc, inf_of_le_left hTH]
  have hsub : (((T : Subgroup G) ⊓ H0).subgroupOf H) =
      ((T.subtype hTH : Sylow 2 H) : Subgroup H) ⊓ H0.subgroupOf H := rfl
  obtain ⟨t,ht,htN,_⟩ := d.exchanged
  have hout : ∃ t ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H),
      t ∉ H0.subgroupOf H := ⟨⟨t,hTH ht⟩,ht,fun hh => htN (d.normalizes_first hh)⟩
  have hn := normalizer_sylow_intersection_eq_of_index_two (T.subtype hTH)
    (H0.subgroupOf H) d.index hout
    (exchanged_zero_sylow_self_normalizing a (T : Subgroup G) p H0 H1 H2 d)
  rw [hS]
  apply le_antisymm
  · intro x hx
    have hh : (⟨x,hx.1⟩ : H) ∈ normalizer
        ((((T.subtype hTH : Sylow 2 H) : Subgroup H) ⊓ H0.subgroupOf H : Subgroup H) : Set H) := by
      rw [← hsub, ← subgroupOf_normalizer_eq (inf_le_left.trans hTH)]
      exact hx.2
    change (⟨x,hx.1⟩ : H) ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H)
    rw [← hn]
    exact hh
  · intro x hx
    refine ⟨hTH hx,?_⟩
    have hh : (⟨x,hTH hx⟩ : H) ∈ normalizer
        ((((T.subtype hTH : Sylow 2 H) : Subgroup H) ⊓ H0.subgroupOf H : Subgroup H) : Set H) := hn.symm ▸ hx
    rw [← hsub, ← subgroupOf_normalizer_eq (inf_le_left.trans hTH)] at hh
    exact hh
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
