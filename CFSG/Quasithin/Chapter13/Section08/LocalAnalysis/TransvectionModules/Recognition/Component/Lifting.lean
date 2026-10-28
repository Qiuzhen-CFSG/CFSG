module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic

/-!
# Lifting the component product across the two-core

The kernel of H → H/O₂(H) is absorbed into T. A quotient factorization
x=k*t lifts by replacing t with t*((k*t)⁻¹*h). For the actual source Sylow
subgroup, O₂(H)≤T follows by restricting that Sylow subgroup to H.
This proves equality with the setwise product, without assuming O₂(H)≤K.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.5(1),
printed p.947, and the product assertions in 13.7.6, printed pp.938–939.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
private theorem product_lift {A : Type*} [Group A]
    (N K T : Subgroup A) [N.Normal] (hN : N ≤ T)
    (hgen : ∀ x : A ⧸ N, ∃ k : K, ∃ t : T,
      x = QuotientGroup.mk' N (k : A) * QuotientGroup.mk' N (t : A)) :
    ∀ a : A, ∃ k : K, ∃ t : T, (k : A) * t = a := by
  intro a
  obtain ⟨k, t, ht⟩ := hgen (QuotientGroup.mk' N a)
  let n : A := ((k : A) * (t : A))⁻¹ * a
  have hn : n ∈ N := by
    apply (QuotientGroup.eq_one_iff n).mp
    change QuotientGroup.mk' N (((k : A) * (t : A))⁻¹ * a) = 1
    rw [map_mul, map_inv, map_mul, ht, inv_mul_cancel]
  refine ⟨k, ⟨(t : A) * n, T.mul_mem t.property (hN hn)⟩, ?_⟩
  dsimp [n]
  group

/-- Lift a star-product witness with the two-core contained in its right factor. -/
theorem product_of_star_product {G : Type*} [Group G]
    (H K T : Subgroup G)
    (hQT : Source.QH H ≤ T)
    (hgen : ∀ x : Source.Hstar H, ∃ k ∈ Source.starImage H K,
      ∃ t ∈ Source.starImage H T, x = k * t) :
    ∀ h ∈ H, ∃ k ∈ K, ∃ t ∈ T, k * t = h := by
  have hcore : pCore 2 H ≤ T.subgroupOf H := by
    intro x hx
    exact hQT ⟨x, hx, rfl⟩
  have hg : ∀ x : Source.Hstar H, ∃ k : K.subgroupOf H, ∃ t : T.subgroupOf H,
      x = QuotientGroup.mk' (pCore 2 H) (k : H) *
        QuotientGroup.mk' (pCore 2 H) (t : H) := by
    intro x
    obtain ⟨k, ⟨a, ha, rfl⟩, t, ⟨b, hb, rfl⟩, he⟩ := hgen x
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he⟩
  intro h hh
  obtain ⟨k, t, he⟩ := product_lift (pCore 2 H) (K.subgroupOf H) (T.subgroupOf H)
    hcore hg ⟨h, hh⟩
  exact ⟨(k : H), k.property, (t : H), t.property, congrArg Subtype.val he⟩

/-- The source Sylow hypothesis discharges the kernel containment and gives H=KT. -/
theorem product_of_star_product_sylow {G : Type*} [Group G]
    (T : Sylow 2 G) (H K : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hgen : ∀ x : Source.Hstar H, ∃ k ∈ Source.starImage H K,
      ∃ t ∈ Source.starImage H (T : Subgroup G), x = k * t) :
    (H : Set G) = (K : Set G) * (T : Set G) := by
  have hQT : Source.QH H ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow H (T.subtype hTH)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at h
  apply Set.Subset.antisymm
  · intro h hh
    obtain ⟨k, hk, t, ht, he⟩ := product_of_star_product H K T hQT hgen h hh
    exact Set.mem_mul.mpr ⟨k, hk, t, ht, he⟩
  · rintro h ⟨k, hk, t, ht, rfl⟩
    exact H.mul_mem (hKH hk) (hTH ht)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

end
