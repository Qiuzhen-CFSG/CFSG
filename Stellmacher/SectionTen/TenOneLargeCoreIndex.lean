module
public import Stellmacher.SectionTen.TenOneLargeNeighborCore
public import Stellmacher.SectionTen.TenOneLargeNeighborhoodQuotient
public import Theory.GroupTheory.ThreeKernelParity

/-!
# Large neighborhood core-intersection index

Source (19)'s first-step Frobenius20 quotient forces the intersection W₀ of
the three middle-neighbor cores inside Wnext to have index four in Wnext.
The hypotheses are the ambient Section Ten context, offset-two middle vertex,
and the first-step quotient model; no intersection index is assumed.

Each neighbor core cuts the actual generated neighborhood in index two.
On any neighbor module, membership in either foreign core is equivalent to
membership in the actual conjugate closure W, by seed transport and W's
containment in every neighbor core. Hence the three binary kernel characters
satisfy the parity relation on the generating modules, and therefore on all
of Wnext. Any two kernels determine their common intersection. They are
distinct by cross-neighbor critical noncontainment, so the index is four.

This proves the Wnext/W₀ calculation after (19) of Stellmacher (10.1),
Journal of Algebra 190 (1997), printed p.65 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u


variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_neighborhood_core_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep)) :
    QuotientCardEq (GeneratedNeighborhoodV ctx.Γ middle)
      (NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
        GeneratedNeighborhoodV ctx.Γ middle) 4 := by
  classical
  have houtside := @ten_one_neighbor_module_not_le_core _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ctx middle hpath
  have hindex := @ten_one_large_neighbor_core_index _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ctx middle hpath hmodel
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let Z := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
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
      exact ten_one_neighbor_seed_le_generated ctx middle hpath hleft hright hne
        ⟨helement, hcore⟩
    · intro hz
      exact ((ten_one_generated_containment ctx middle hpath).trans
        (inf_le_left.trans (sInf_le
          ⟨right, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hright, rfl⟩))) hz
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
