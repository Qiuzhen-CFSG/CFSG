module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Generation through a kernel central in a perfect quotient subgroup

A subgroup supplementing a normal kernel central in a perfect subgroup is
all of the ambient group. Apply this after quotienting by the original
normal two-core. The kernel may still have a central cubic factor; its
centrality is required only in the perfect component image.
Source: Aschbacher–Smith C.1.24(c), printed pp.130–131.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private theorem perfect_central_supplement [Group.IsPerfect G]
    (D : Subgroup G) (hD : center G ⊔ D = ⊤) : D = ⊤ := by
  have hn : (⊤ : Subgroup G) ≤ normalizer (D : Set G) := by
    rw [←hD]
    exact sup_le (center_le_normalizer _) D.le_normalizer
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  apply top_unique
  simpa only [Group.IsPerfect.commutator_eq_top] using
    (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      ((sup_comm D (center G)).trans hD) (inferInstance : IsMulCommutative (center G)))

/-- A kernel central in a perfect subgroup cannot be a proper supplement. -/
theorem eq_top_of_kernel_central_in_perfect (B D K : Subgroup G) [D.Normal]
    [Group.IsPerfect B] (hD : D ≤ (center B).map B.subtype)
    (hgen : D ⊔ K = ⊤) : K = ⊤ := by
  have hDB : D ≤ B := hD.trans (map_subtype_le _)
  have hinner : center B ⊔ K.subgroupOf B = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨d,hd,k,hk,hdk⟩ := mem_sup_of_normal_left.mp
      (show (x : G) ∈ D ⊔ K by rw [hgen]; trivial)
    have hdB := hDB hd
    have hkB : k ∈ B := (B.mul_mem_cancel_left hdB).mp (hdk ▸ x.property)
    have hdZ : (⟨d,hdB⟩ : B) ∈ center B := by
      obtain ⟨c,hc,he⟩ := hD hd
      have he' : c = ⟨d,hdB⟩ := Subtype.ext he
      exact he' ▸ hc
    have he : (⟨d,hdB⟩ : B) * ⟨k,hkB⟩ = x := Subtype.ext hdk
    rw [←he]
    exact (center B ⊔ K.subgroupOf B).mul_mem (mem_sup_left hdZ) (mem_sup_right hk)
  have hBK : B ≤ K := by
    intro x hx
    have ht := perfect_central_supplement (K.subgroupOf B) hinner
    change (⟨x,hx⟩ : B) ∈ K.subgroupOf B
    rw [ht]
    trivial
  apply top_unique
  rw [←hgen]
  exact sup_le (hDB.trans hBK) le_rfl

/-- Full image under q generates the original group once the original normal
kernel Q is present and the remaining q-kernel is central in a perfect image. -/
theorem eq_top_of_perfect_quotient_image (Q : Subgroup G) [Q.Normal]
    (q : G →* H) (K : Subgroup G) (hQK : Q ≤ K)
    (B : Subgroup (G ⧸ Q)) [Group.IsPerfect B]
    (hcentral : q.ker.map (QuotientGroup.mk' Q) ≤ (center B).map B.subtype)
    (himage : K.map q = ⊤) : K = ⊤ := by
  let π := QuotientGroup.mk' Q
  let D := q.ker.map π
  let : D.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Q)
  have hgen : D ⊔ K.map π = ⊤ := by
    have hs : q.ker ⊔ K = ⊤ := by
      have hh := congrArg (Subgroup.comap q) himage
      simpa only [comap_map_eq,comap_top,sup_comm] using hh
    rw [←map_sup,hs,map_top_of_surjective π (QuotientGroup.mk'_surjective Q)]
  have htop := eq_top_of_kernel_central_in_perfect B D (K.map π) hcentral hgen
  have hh := congrArg (Subgroup.comap π) htop
  rw [comap_map_eq,comap_top] at hh
  rw [show π.ker = Q from QuotientGroup.ker_mk' Q] at hh
  simpa only [sup_of_le_left hQK] using hh

end Subgroup
