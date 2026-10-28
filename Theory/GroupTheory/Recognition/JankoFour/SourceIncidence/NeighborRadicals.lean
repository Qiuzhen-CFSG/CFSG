module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreIntersections
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Transport

/-!
# The native image of a neighboring point radical

The stabilizer E_y∩M of the original point in a neighboring radical lies
in the original line radical R. Conjugating within the line identifies its
order as 512. Its kernel under the original Todd projection is E_y∩E=Z,
of order eight, so its image is the full order-64 native trio radical.
Relative normalization by the line overlap places that image in the
intrinsic two-core, with no ambient normality assumption.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (4.4), (5.1)(2),
and the radical-image arguments of (5.5),(5.7), pp.598–601.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

private theorem R_le_point : a.d.R ≤ a.P.M := inf_le_left.trans a.K_le_point

/-- The original line radical maps into the intrinsic native trio core. -/
theorem line_radical_image_le : (a.d.R.subgroupOf a.P.M).map a.P.projection ≤
    M24ChapterHStabilizers.TrioAction.coreAt a.trio := by
  apply le_pCoreIn_of_normalizes
  · have hp : IsPGroup 2 a.d.R := by
      rw [a.d.R_eq_K_twoCore h]
      exact isPGroup_pCoreIn 2 a.d.K
    exact hp.comap_subtype.map _
  · rw [←a.line_image]
    apply map_mono
    exact fun _ hv => a.line_normalizer.symm ▸ a.d.R_le_normalizer hv
  · apply le_normalizer_iff.mpr
    intro g hg v hv
    rw [←a.line_image] at hg
    obtain ⟨m,hm,rfl⟩ := hg
    obtain ⟨r,hr,rfl⟩ := hv
    refine ⟨m*r*m⁻¹,?_,by simp only [map_mul,map_inv]⟩
    exact (mem_normalizer_iff.mp (a.d.R_normalized (a.line_normalizer ▸ hm)) r).mp hr

/-- A neighboring radical's point stabilizer lies in the original R. -/
theorem neighbor_core_le_R (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1))
    (hne : y ≠ Cosets.vertex a.P.M 1) : coreAt a.P y ⊓ a.P.M ≤ a.d.R := by
  intro u hu
  have huf : u • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr hu.2
  have hN : u ∈ a.L.G₂ := by
    have hh := a.core_fixes_lines y ⟨u,hu.1⟩ _ hy
    rw [Cosets.smul_vertex,mul_one] at hh
    exact (Cosets.vertex_eq_base _ _).mp hh
  have hK : u ∈ a.d.K := (a.point_action_kernel ⟨u,hN⟩).mp
    (a.core_regular_other y _ hy ⟨u,hu.1⟩ _ ⟨1,rfl,rfl⟩ hne.symm huf)
  have hS : u ∈ a.d.S := by
    obtain ⟨n,rfl,hn⟩ := hy
    have hnN : n ∈ a.L.G₂ := (Cosets.vertex_eq_base _ _).mp hn
    have he := (coreAt_vertex a.P n).le hu.1
    have heS := a.E_le_S he
    change n⁻¹*u*(n⁻¹)⁻¹ ∈ a.d.S at heS
    have hh := (mem_normalizer_iff.mp
      (a.d.S_normalized (a.line_normalizer ▸ hnN)) (n⁻¹*u*(n⁻¹)⁻¹)).mp heS
    simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  exact ⟨hK,hS⟩

/-- The neighboring point stabilizer has order 512, retaining E_y∩M rather
than replacing it by the smaller intersection E_y∩E. -/
theorem neighbor_core_point_card (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1))
    (hne : y ≠ Cosets.vertex a.P.M 1) :
    Nat.card ((coreAt a.P y).subgroupOf a.P.M) = 512 := by
  have he : coreAt a.P y ⊓ a.P.M = coreAt a.P y ⊓ a.d.R :=
    le_antisymm (le_inf inf_le_left (a.neighbor_core_le_R y hy hne))
      (inf_le_inf_left _ a.R_le_point)
  obtain ⟨n,rfl,hn⟩ := hy
  have hnN : n ∈ a.L.G₂ := (Cosets.vertex_eq_base _ _).mp hn
  have hR : a.d.R.comap (MulAut.conj n⁻¹).toMonoidHom = a.d.R := by
    ext u
    exact (mem_normalizer_iff.mp
      (a.d.R_normalized (a.line_normalizer ▸ a.L.G₂.inv_mem hnN)) u).symm
  rw [←card_map_of_injective a.P.M.subtype_injective,subgroupOf_map_subtype,he,
    coreAt_vertex,←hR,←comap_inf,comap_equiv_eq_map_symm' (MulAut.conj n⁻¹),
    card_map_of_injective (MulAut.conj n⁻¹).symm.injective]
  have hc := a.radical_R_card
  rw [←card_map_of_injective a.P.E.subtype_injective,subgroupOf_map_subtype,inf_comm] at hc
  exact hc

/-- Under the original Todd projection, E_y∩M is exactly the native trio
radical. Its order 512 and kernel Z of order eight give the full order 64. -/
theorem neighbor_core_image (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1))
    (hne : y ≠ Cosets.vertex a.P.M 1) :
    ((coreAt a.P y).subgroupOf a.P.M).map a.P.projection =
      M24ChapterHStabilizers.TrioAction.coreAt a.trio := by
  let A := (coreAt a.P y).subgroupOf a.P.M
  let f := a.P.projection.domRestrict A
  have hr : f.range = A.map a.P.projection := by
    ext u
    constructor
    · rintro ⟨v,rfl⟩; exact ⟨v.val,v.property,rfl⟩
    · rintro ⟨v,hv,rfl⟩; exact ⟨⟨v,hv⟩,rfl⟩
  have hi := a.core_intersection_base y hy hne
  have hk : ∀ u : a.P.M, a.P.projection u = 1 ↔ (u : G) ∈ a.P.E := by
    intro u
    rw [←MonoidHom.mem_ker,a.P.projection_ker]
    rfl
  let e : f.ker ≃ a.d.space :=
    { toFun := fun u => ⟨u.val.val,hi ▸ And.intro ((hk u.val.val).mp u.property) u.val.property⟩
      invFun := fun u =>
        let hu : (u : G) ∈ a.P.E ⊓ coreAt a.P y := hi.symm ▸ u.property
        ⟨⟨⟨u,a.P.E_le hu.1⟩,hu.2⟩,(hk _).mpr hu.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := f.ker.card_mul_index
  rw [index_ker,Nat.card_congr e,show Nat.card a.d.space = 8 from a.d.card,
    show Nat.card A = 512 from a.neighbor_core_point_card y hy hne,hr] at hc
  apply eq_of_le_of_card_ge
  · exact (map_mono (show (coreAt a.P y).subgroupOf a.P.M ≤ a.d.R.subgroupOf a.P.M from
      fun u hu => a.neighbor_core_le_R y hy hne ⟨hu,u.property⟩)).trans
      a.line_radical_image_le
  · rw [M24ChapterHStabilizers.TrioAction.coreAt_card]
    dsimp [A] at hc
    omega
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
