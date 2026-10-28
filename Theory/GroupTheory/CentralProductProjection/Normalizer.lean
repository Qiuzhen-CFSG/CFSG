module
public import Theory.GroupTheory.SylowOuterCover
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Normalizer control after projecting onto a normal factor

For a normal subgroup K, the subgroup K ∩ A C(K) is the full preimage
of the projection of A ∩ K C(K) onto K/Z(K). If a Sylow subgroup lies
in A and normalizes B ≤ K, a prime-group outer action reduces A's
normalization of B to this literal projection. A normal closure of a seed
inside K stays in every A-invariant subgroup containing that seed.

No centralizer is discarded and no splitting of the ambient group is
assumed. Source application: Aschbacher--Smith 12.5.4, printed p.819.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- The projection controls normalization when the prescribed supplement already does. -/
theorem component_projection_normalizes_iff
    (K A B S : Subgroup G) [K.Normal]
    (hBK : B ≤ K) (hSA : S ≤ A)
    (hSB : S ≤ normalizer (B : Set G))
    (hcover : (K ⊔ centralizer (K : Set G)) ⊔ S = ⊤) :
    A ≤ normalizer (B : Set G) ↔
      K ⊓ (A ⊔ centralizer (K : Set G)) ≤ normalizer (B : Set G) := by
  let C := centralizer (K : Set G)
  have hCB : C ≤ normalizer (B : Set G) :=
    (centralizer_le hBK).trans (centralizer_le_normalizer _)
  constructor
  · intro hA
    exact inf_le_right.trans (sup_le hA hCB)
  · intro hR a ha
    have hall : a ∈ (K ⊔ C) ⊔ S := hcover.symm ▸ mem_top a
    obtain ⟨d,hd,t,ht,rfl⟩ := mem_sup_of_normal_left.mp hall
    obtain ⟨k,hk,c,hc,rfl⟩ := mem_sup_of_normal_left.mp hd
    have hkc : k * c ∈ A := (mul_mem_cancel_right (hSA ht)).mp ha
    have hkR : k ∈ K ⊓ (A ⊔ C) := by
      refine ⟨hk,?_⟩
      change k ∈ A ⊔ C
      have hh := (A ⊔ C).mul_mem (mem_sup_left hkc) (mem_sup_right (C.inv_mem hc))
      simpa only [mul_inv_cancel_right] using hh
    exact mul_mem (mul_mem (hR hkR) (hCB hc)) (hSB ht)

/-- The projected actor preserves the intersection of an invariant subgroup with K. -/
theorem component_projection_normalizes_intersection
    (K A J : Subgroup G) [K.Normal] (hAJ : A ≤ normalizer (J : Set G)) :
    K ⊓ (A ⊔ centralizer (K : Set G)) ≤ normalizer (J ⊓ K : Set G) := by
  apply inf_le_right.trans
  apply sup_le
  · exact (le_inf hAJ (show A ≤ normalizer (K : Set G) from le_normalizer_of_normal)).trans
      inf_normalizer_le_normalizer_inf
  · exact (centralizer_le (show J ⊓ K ≤ K from inf_le_right)).trans
      (centralizer_le_normalizer _)

/-- Projection preserves the containment of the original seed's normal closure. -/
theorem component_projection_conjugateSpan_le
    (K A B J : Subgroup G) [K.Normal]
    (hBK : B ≤ K) (hBJ : B ≤ J) (hAJ : A ≤ normalizer (J : Set G)) :
    conjugateSpanBy B (K ⊓ (A ⊔ centralizer (K : Set G))) ≤ J ⊓ K :=
  conjugateSpanBy_le (le_inf hBJ hBK)
    (component_projection_normalizes_intersection K A J hAJ)

/-- A prime-group outer action supplies the required cover using the original Sylow. -/
theorem sylow_component_projection_normalizes_iff [Finite G]
    {p : ℕ} [Fact p.Prime] (K A B : Subgroup G) [K.Normal]
    (S : Sylow p G) (hBK : B ≤ K) (hSA : (S : Subgroup G) ≤ A)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (ho : IsPGroup p (MulAut.Outer K)) :
    A ≤ normalizer (B : Set G) ↔
      K ⊓ (A ⊔ centralizer (K : Set G)) ≤ normalizer (B : Set G) :=
  component_projection_normalizes_iff K A B S hBK hSA hSB
    (Theory.GroupTheory.sup_centralizer_sup_sylow_eq_top K ho S)

end Subgroup
