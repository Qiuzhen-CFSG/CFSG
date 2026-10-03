module
public import ABG.ChapterII.Section2.WeakCenter
public import ABG.ChapterII.Section3.WeakCenterQuotient

/-!
# Weakly closed central subgroups for every Sylow subgroup

For a finite Q-group, every subgroup of the center of any chosen Sylow
two-subgroup is weakly closed. The enlarged Q-group definition first supplies
one Sylow witness through `IsQGroup.exists_hasWeaklyClosedCenterSubgroups`.
Sylow conjugacy carries that witness to the chosen subgroup.

The elementary center calculation identifies the center of an isomorphic
subgroup image with the image of its center. Applying the surjective-map
weak-closure theorem to the conjugation automorphism then transports the
property. Thus the conclusion is independent of the defining Sylow witness.
The center-image identity is also public for transporting centrality in the
central Sylow quotient construction of Section 3.

This justifies the arbitrary Sylow subgroup used in ABG Chapter II §3
Proposition 1, `refs/latex/alperin-brauer-gorenstein-pages/page-022.tex`, from
the full enlarged Q-group definition in Chapter II §2.
-/

open scoped Pointwise
namespace ABG

private theorem mem_subgroupCenter_iff {G : Type*} [Group G]
    {S : Subgroup G} {x : G} :
    x ∈ subgroupCenter S ↔ x ∈ S ∧ ∀ y ∈ S, y * x = x * y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
  · rintro ⟨hx, hcomm⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (hcomm y y.property))

/-- The ambient image of a subgroup center commutes with transport through
a multiplicative equivalence. -/
public theorem subgroupCenter_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Subgroup G) :
    subgroupCenter (S.map e.toMonoidHom) = (subgroupCenter S).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hxcomm⟩ := mem_subgroupCenter_iff.mp hx
    obtain ⟨s, hs, rfl⟩ := hxS
    refine ⟨s, mem_subgroupCenter_iff.mpr ⟨hs, ?_⟩, rfl⟩
    intro y hy
    apply e.injective
    simpa using hxcomm (e y) (Subgroup.mem_map_of_mem _ hy)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hsS, hscomm⟩ := mem_subgroupCenter_iff.mp hs
    refine mem_subgroupCenter_iff.mpr ⟨Subgroup.mem_map_of_mem _ hsS, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    simpa using congrArg e (hscomm z hz)

/-- Every Sylow two-subgroup of a finite Q-group has all its central subgroups
weakly closed in the ambient group. -/
public theorem IsQGroup.hasWeaklyClosedCenterSubgroups
    {G : Type*} [Group G] [Finite G] (hQ : IsQGroup G) (S : Sylow 2 G) :
    HasWeaklyClosedCenterSubgroups (S : Subgroup G) := by
  obtain ⟨R, hR⟩ := hQ.exists_hasWeaklyClosedCenterSubgroups
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  have hmap : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
    exact congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hg
  intro Z hZ
  have hcenter : subgroupCenter (S : Subgroup G) =
      (subgroupCenter (R : Subgroup G)).map (MulAut.conj g).toMonoidHom := by
    rw [← hmap, subgroupCenter_map]
  have := hR.weaklyClosedIn_of_le_map (MulAut.conj g).toMonoidHom
    (MulAut.conj g).surjective Z (hcenter ▸ hZ)
  rwa [hmap] at this
end ABG
