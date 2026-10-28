module

public import Theory.Mathieu.M22.ValueBoundParabolics
public import Mathlib.GroupTheory.IsPerfect

/-!
# Generation across a kernel central in a perfect subgroup

Let C be normal in G, contained in a perfect subgroup L, and centralizing
L. A subgroup surjecting onto G/C is all of G: its intersection with L
supplements Z(L), and perfectness eliminates a proper central supplement.
Thus local subgroups lifted across such a kernel need only be shown to
generate the quotient. The kernel need not be central in G.

This is the generation step for the odd covers and outer extensions in
Aschbacher–Smith E.4.3(2), printed pp. 241–242, combined manuscript of
1 March 2004. Construction of the local lifts is separate.
-/

public section
namespace Sporadic.Mathieu.M22ValueBound
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- A perfect group has no proper supplement to its center. -/
theorem central_supplement_eq_top {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (B : Subgroup Q) (hB : center Q ⊔ B = ⊤) : B = ⊤ := by
  have hn : (⊤ : Subgroup Q) ≤ normalizer (B : Set Q) := by
    rw [← hB]
    exact sup_le (Subgroup.center_le_normalizer (B : Set Q)) B.le_normalizer
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  apply top_unique
  simpa only [Group.IsPerfect.commutator_eq_top] using
    (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      ((sup_comm B (center Q)).trans hB) (inferInstance : IsMulCommutative (center Q)))

/-- Normality of C is ambient; centrality is only required inside L. -/
theorem eq_top_of_central_perfect_supplement (L C H : Subgroup G) [C.Normal]
    [Group.IsPerfect L] (hCL : C ≤ L) (hc : C ≤ centralizer (L : Set G))
    (hgen : C ⊔ H = ⊤) : H = ⊤ := by
  have hinner : center L ⊔ H.subgroupOf L = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : G) ∈ C ⊔ H := hgen ▸ mem_top _
    obtain ⟨c, hcC, h, hhH, he⟩ := mem_sup_of_normal_left.mp hx
    have hcL := hCL hcC
    have hhL : h ∈ L := by
      have : c * h ∈ L := he ▸ x.property
      exact (L.mul_mem_cancel_left hcL).mp this
    have hcZ : (⟨c, hcL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((hc hcC) y y.property)
    have hh : (⟨h, hhL⟩ : L) ∈ H.subgroupOf L := hhH
    have heL : (⟨c, hcL⟩ : L) * ⟨h, hhL⟩ = x := Subtype.ext he
    rw [← heL]
    exact (center L ⊔ H.subgroupOf L).mul_mem
      ((show center L ≤ center L ⊔ H.subgroupOf L from le_sup_left) hcZ)
      ((show H.subgroupOf L ≤ center L ⊔ H.subgroupOf L from le_sup_right) hh)
  have hLH : L ≤ H := by
    intro x hx
    have := (central_supplement_eq_top (H.subgroupOf L) hinner).symm ▸
      (mem_top (⟨x, hx⟩ : L))
    exact this
  apply top_unique
  rw [← hgen]
  exact sup_le (hCL.trans hLH) le_rfl

/-- Surjectivity modulo a kernel central in a perfect subgroup forces equality. -/
theorem eq_top_of_quotient_image (L C H : Subgroup G) [C.Normal]
    [Group.IsPerfect L] (hCL : C ≤ L) (hc : C ≤ centralizer (L : Set G))
    (hmap : H.map (QuotientGroup.mk' C) = ⊤) : H = ⊤ := by
  apply eq_top_of_central_perfect_supplement L C H hCL hc
  have h := congrArg (fun A : Subgroup (G ⧸ C) => A.comap (QuotientGroup.mk' C)) hmap
  simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top, sup_comm] using h

end Sporadic.Mathieu.M22ValueBound
