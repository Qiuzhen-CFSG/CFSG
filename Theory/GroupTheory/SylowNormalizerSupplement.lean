module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct
/-!
# Sylow normalizers across a normal supplement

Let a Sylow subgroup S lie in a normal subgroup H and a supplement B. If
its normalizer inside H is exactly H ∩ B, then its full normalizer is B.
Indeed S is a characteristic Sylow subgroup of H ∩ B, so B normalizes S;
the product H B then reduces every full normalizer element to the known
normalizer in H.

This elementary transfer is used for the residuals of unitary-five parabolics
in Aschbacher--Smith, F.1.3 and F.1.12(7), printed pp.260 and 263--264.
-/

public section

open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
/-- Computing the normalizer in a normal subgroup computes it in the whole supplement. -/
theorem normalizer_eq_of_normal_supplement
    (S : Sylow p G) (H B : Subgroup G) [H.Normal]
    (hSH : (S : Subgroup G) ≤ H) (hSB : (S : Subgroup G) ≤ B)
    (hHB : H ⊔ B = ⊤)
    (hN : normalizer (S.subtype hSH : Set H) = B.subgroupOf H) :
    normalizer (S : Set G) = B := by
  let SB := S.subtype hSB
  have hSBC : (SB : Subgroup B) ≤ H.subgroupOf B := fun x hx => hSH hx
  let Q := SB.subtype hSBC
  have hQ : (Q : Subgroup (H.subgroupOf B)).Normal := by
    constructor
    intro x hx g
    have hg : (⟨g.val.val, g.property⟩ : H) ∈ normalizer (S.subtype hSH : Set H) := by
      rw [hN]
      exact g.val.property
    exact (mem_normalizer_iff.mp hg ⟨x.val.val, x.property⟩).mp hx
  have : (Q : Subgroup (H.subgroupOf B)).Characteristic := Q.characteristic_of_normal hQ
  have hm : (Subgroup.map (H.subgroupOf B).subtype (Q : Subgroup (H.subgroupOf B))).Normal :=
    inferInstance
  have hmap : Subgroup.map (H.subgroupOf B).subtype (Q : Subgroup (H.subgroupOf B)) =
      (SB : Subgroup B) := Subgroup.map_subgroupOf_eq_of_le hSBC
  have hSBnormal : (SB : Subgroup B).Normal := by rwa [hmap] at hm
  have hBN : B ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSB).mp hSBnormal
  apply le_antisymm _ hBN
  intro n hn
  obtain ⟨h, hh, b, hb, he⟩ := mem_sup_of_normal_left.mp (hHB ▸ mem_top n)
  have hhN : h ∈ normalizer (S : Set G) := by
    have he' : h = n * b⁻¹ := by rw [← he]; group
    rw [he']
    exact (normalizer (S : Set G)).mul_mem hn ((normalizer (S : Set G)).inv_mem (hBN hb))
  have hhNH : (⟨h, hh⟩ : H) ∈ normalizer (S.subtype hSH : Set H) :=
    (le_normalizer_comap H.subtype) hhN
  have hhB : h ∈ B := by rw [hN] at hhNH; exact hhNH
  rw [← he]
  exact B.mul_mem hhB hb
end Sylow
