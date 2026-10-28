module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Residual generation and normalization of a conjugate span

If L and a p-subgroup S generate H and L lies in Oᵖ(H), then Oᵖ(H)
is exactly the span of the S-conjugates of L. An actor fixing L also fixes
that span whenever S normalizes the actor. The proof uses a normal
p-group quotient and conjugation of the literal subgroup generators.

Source application: Aschbacher--Smith, original 5.2.2, printed p.648;
the actor there is DT₀, not D alone.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A p-subgroup supplement gives the exact residual orbit span. -/
theorem embedded_pResidual_eq_conjugateSpanBy {p : ℕ}
    (L S H : Subgroup G)
    (hL : L ≤ (pResidual p H).map H.subtype) (hS : IsPGroup p S)
    (hgen : L ⊔ S = H) :
    (pResidual p H).map H.subtype = conjugateSpanBy L S := by
  let N := conjugateSpanBy L S
  have hLH : L ≤ H := hgen ▸ le_sup_left
  have hSH : S ≤ H := hgen ▸ le_sup_right
  have hNH : N ≤ H := conjugateSpanBy_le hLH (hSH.trans H.le_normalizer)
  have hNS : N ⊔ S = H := le_antisymm (sup_le hNH hSH)
    (hgen ▸ sup_le_sup (le_conjugateSpanBy L S) le_rfl)
  have hHN : H ≤ normalizer (N : Set G) := by
    rw [← hNS]
    exact sup_le N.le_normalizer (le_normalizer_conjugateSpanBy L S)
  let : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHN
  have hsup : N.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hNH hSH, hNS, subgroupOf_self]
  have hres : pResidual p H ≤ N.subgroupOf H :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top _ _ hS.comap_subtype hsup⟩
  apply le_antisymm
  · simpa only [map_subgroupOf_eq_of_le hNH] using map_mono (f := H.subtype) hres
  · apply conjugateSpanBy_le hL
    have hn : ((pResidual p H).map H.subtype).subgroupOf H = pResidual p H := by
      exact comap_map_eq_self_of_injective H.subtype_injective _
    have hn' : (((pResidual p H).map H.subtype).subgroupOf H).Normal := by
      rw [hn]
      infer_instance
    exact hSH.trans ((normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hn')

/-- Normalization of the actor by the conjugating group propagates seed invariance. -/
theorem normalizes_conjugateSpanBy_of_normalized_actor
    (L S A : Subgroup G) (hAL : A ≤ normalizer (L : Set G))
    (hSA : S ≤ normalizer (A : Set G)) :
    A ≤ normalizer (conjugateSpanBy L S : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨s, hs, l, hl, rfl⟩
  have ha' : s⁻¹ * a * s ∈ A := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hSA (S.inv_mem hs)) a).mp ha
  apply subset_closure
  refine ⟨s, hs, (s⁻¹ * a * s) * l * (s⁻¹ * a * s)⁻¹,
    (mem_normalizer_iff.mp (hAL ha') l).mp hl, ?_⟩
  group
end Subgroup
