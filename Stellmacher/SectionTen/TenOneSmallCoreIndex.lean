module
public import Stellmacher.SectionTen.TenOneSmallNeighborCore
public import Theory.GroupTheory.ThreeKernelParity

/-!
# The neighborhood-core intersection index in Stellmacher (10.1)(a)

In the genuine small-module case, with first local quotient SL₂(2), the
intersection W₀ of all middle-neighbor cores inside the generated
neighborhood Wnext has index four. Only the ambient Section Ten context,
offset-two vertex, order-eight module case, and local quotient model are
inputs; neither a kernel index nor a covering statement is assumed.

The proved cubic action enumerates the three middle neighbors. Each core
cuts Wnext in index two. Each module lies in its own core, while its
intersection with either other core is the same middle four-center. Hence
each module satisfies the parity relation for membership in the three
index-two kernels. The relation defines a subgroup containing all the
generating modules, so any two kernels already determine their common
intersection. The kernels are distinct by the actual cross-neighbor
noncontainment; two distinct subgroups of index two intersect in index four.

This supplies the Wnext/W₀ step in the common small-case quotient orders of
Stellmacher (10.1), printed pp.59–60 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u


variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_neighborhood_core_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QuotientCardEq (GeneratedNeighborhoodV ctx.Γ middle)
      (NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
        GeneratedNeighborhoodV ctx.Γ middle) 4 := by
  classical
  have hslice := @ten_one_small_neighbor_core_slice _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ctx middle hpath hsmall
  have houtside := @ten_one_neighbor_module_not_le_core _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ctx middle hpath
  have hindex := @ten_one_small_neighbor_core_index _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ctx middle hpath hmodel
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let neighbors := {neighbor : ctx.Γ.Vertex // ctx.Γ.adjacent middle neighbor}
  have hdegree : Nat.card neighbors = 3 :=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).degree
  let _ : Finite neighbors := Nat.finite_of_card_ne_zero (by rw [hdegree]; decide)
  let e : neighbors ≃ Fin 3 := Finite.equivFinOfCardEq hdegree
  let vertex : Fin 3 → ctx.Γ.Vertex := fun index => (e.symm index).val
  have hadj (index : Fin 3) : ctx.Γ.adjacent middle (vertex index) := (e.symm index).property
  have hinj : Function.Injective vertex := fun i j hij =>
    e.symm.injective (Subtype.ext hij)
  have hne01 : vertex 0 ≠ vertex 1 := fun h => by have := hinj h; omega
  have hne02 : vertex 0 ≠ vertex 2 := fun h => by have := hinj h; omega
  have hne12 : vertex 1 ≠ vertex 2 := fun h => by have := hinj h; omega
  have hcover {neighbor : ctx.Γ.Vertex} (hneigh : ctx.Γ.adjacent middle neighbor) :
      neighbor = vertex 0 ∨ neighbor = vertex 1 ∨ neighbor = vertex 2 := by
    have heq := congrArg Subtype.val (e.symm_apply_apply ⟨neighbor, hneigh⟩)
    change vertex (e ⟨neighbor, hneigh⟩) = neighbor at heq
    generalize e ⟨neighbor, hneigh⟩ = index at heq
    fin_cases index <;> aesop
  let K₀ := QAt ctx.Γ (vertex 0)
  let K₁ := QAt ctx.Γ (vertex 1)
  let K₂ := QAt ctx.Γ (vertex 2)
  have hzero : (K₀.subgroupOf W).index = 2 := hindex (hadj 0)
  have hone : (K₁.subgroupOf W).index = 2 := hindex (hadj 1)
  have htwo : (K₂.subgroupOf W).index = 2 := hindex (hadj 2)
  have hown (neighbor : ctx.Γ.Vertex) : VAt ctx.Γ neighbor ≤ QAt ctx.Γ neighbor :=
    neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
      (by rw [ctx.critical_length]; decide) neighbor
  have hcross {left right : ctx.Γ.Vertex}
      (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
      (hne : left ≠ right) {element : G} (helement : element ∈ VAt ctx.Γ left) :
      element ∈ QAt ctx.Γ right ↔ element ∈ Z := by
    constructor
    · intro hcore
      exact (hslice hleft hright hne).le ⟨helement, hcore⟩
    · intro hz
      exact ((hslice hleft hright hne).ge hz).2
  have hparity : W ⊓ K₀ ⊓ K₁ ≤ K₂ := by
    apply Subgroup.three_index_two_kernels_parity W K₀ K₁ K₂
      {subgroup | ∃ neighbor, neighbor ∈ Neighborhood ctx.Γ middle ∧ subgroup = VAt ctx.Γ neighbor}
      rfl hzero hone htwo
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩ element helement
    rcases hcover ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor) with rfl | rfl | rfl
    · change (element ∈ QAt ctx.Γ (vertex 0) ↔ element ∈ QAt ctx.Γ (vertex 1)) ↔
        element ∈ QAt ctx.Γ (vertex 2)
      rw [hcross (hadj 0) (hadj 1) hne01 helement,
        hcross (hadj 0) (hadj 2) hne02 helement]
      simp only [hown _ helement, true_iff]
    · change (element ∈ QAt ctx.Γ (vertex 0) ↔ element ∈ QAt ctx.Γ (vertex 1)) ↔
        element ∈ QAt ctx.Γ (vertex 2)
      rw [hcross (hadj 1) (hadj 0) hne01.symm helement,
        hcross (hadj 1) (hadj 2) hne12 helement]
      simp only [hown _ helement, iff_true]
    · change (element ∈ QAt ctx.Γ (vertex 0) ↔ element ∈ QAt ctx.Γ (vertex 1)) ↔
        element ∈ QAt ctx.Γ (vertex 2)
      rw [hcross (hadj 2) (hadj 0) hne02.symm helement,
        hcross (hadj 2) (hadj 1) hne12.symm helement]
      simp only [hown _ helement, iff_self]
  have hW0 : NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ W =
      W ⊓ K₀ ⊓ K₁ := by
    apply le_antisymm
    · exact le_inf (le_inf inf_le_right (inf_le_left.trans
        (sInf_le ⟨vertex 0, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 0), rfl⟩)))
        (inf_le_left.trans
          (sInf_le ⟨vertex 1, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 1), rfl⟩))
    · refine le_inf ?_ (inf_le_left.trans inf_le_left)
      rw [NeighborhoodQIntersection]
      apply le_sInf
      rintro core ⟨neighbor, hneighbor, rfl⟩
      rcases hcover ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor) with rfl | rfl | rfl
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right
      · exact hparity
  have hout : ¬ K₀.subgroupOf W ≤ K₁.subgroupOf W := by
    intro hle
    apply houtside (hadj 0) (hadj 1) hne01
    intro element helement
    have hWmem : element ∈ W :=
      (show VAt ctx.Γ (vertex 0) ≤ W from
        le_sSup ⟨vertex 0, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj 0), rfl⟩) helement
    exact hle (show (⟨element, hWmem⟩ : W) ∈ K₀.subgroupOf W from hown _ helement)
  have hfour := Subgroup.index_inf_eq_four_of_distinct_index_two (K₀.subgroupOf W) (K₁.subgroupOf W)
    hzero hone hout
  have hnative : (W ⊓ K₀ ⊓ K₁).subgroupOf W = K₀.subgroupOf W ⊓ K₁.subgroupOf W := by
    ext element
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, element.property, true_and]
  have hcount := ((W ⊓ K₀ ⊓ K₁).subgroupOf W).index_mul_card
  rw [hnative, hfour, ← hnative, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (show W ⊓ K₀ ⊓ K₁ ≤ W from
      inf_le_left.trans inf_le_left)).toEquiv] at hcount
  change Nat.card W = 4 * Nat.card _
  rw [hW0]
  exact hcount.symm

end Stellmacher.SectionTen
