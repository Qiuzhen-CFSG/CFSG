module

public import Theory.GroupTheory.PStar.RadicalActionReduction

/-!
# Two-star radicals under central homomorphisms

A surjection with central kernel and p-star target has p-star residual:
restrict the map to the residual and apply the central-Sylow kernel theorem.
For a homomorphism whose image covers the target two-star core, apply this
to the inverse image of that core. Its residual is normal in the source,
so its image proves the reverse radical containment. Normality of the full
image supplies the forward containment.

Source: GLS II, Chapter B, Lemma 5.3 (central-Sylow case) and 5.8(v),
`refs/KGroup/GLS2/ChapterB.tex`. These statements use only the completed
central-kernel extension and normal-product theorems, not general 5.3.
-/

public section
open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G] [Group H] [Finite G]

/-- A central extension of a p-star group has p-star p-residual. -/
theorem isPStar_pResidual_of_surjective_central_kernel
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (hH : IsPStar p H) : IsPStar p (pResidual p G) := by
  let R := pResidual p G
  let g := f.comp R.subtype
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    exact (map_pResidual_of_surjective p f hf).trans hH.1
  have hgc : g.ker ≤ center R := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc hx) (y : G))
  let P : Sylow p g.ker := Sylow.nonempty.some
  exact isPStar_of_surjective_central_sylow_kernel (isPPerfect_pResidual p) g hg P
    ((map_subtype_le _).trans hgc) hH
end Theory.GroupTheory

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A homomorphism with normal image maps the two-star core into the target core. -/
theorem map_twoStarCore_le_of_normal_range (f : G →* H) [f.range.Normal] :
    (pStarCore 2 G).map f ≤ pStarCore 2 H := by
  have h := map_mono (f := f.range.subtype)
    (map_pStarCore_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective (p := 2))
  rw [map_map] at h
  exact h.trans (map_twoStarCore_subtype_le f.range)
end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- Covering the target core suffices to lift it through a central kernel. -/
theorem twoStarCore_le_map_of_central_kernel
    (f : G →* H) (hc : f.ker ≤ center G) (hcover : pStarCore 2 H ≤ f.range) :
    pStarCore 2 H ≤ (pStarCore 2 G).map f := by
  let B := pStarCore 2 H
  let E := B.comap f
  let g := f.subgroupComap B
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hcover y.property
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ B
    rw [hx]
    exact y.property
  have hcE : g.ker ≤ center E := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (congrArg Subtype.val hx)) (y : G))
  have hR := Theory.GroupTheory.isPStar_pResidual_of_surjective_central_kernel
    g hg hcE (isPStar_twoStarCore (G := H))
  have hle : (pResidual 2 E).map E.subtype ≤ pStarCore 2 G :=
    le_pStarCore _ (hR.of_equiv
      ((pResidual 2 E).equivMapOfInjective E.subtype E.subtype_injective))
  have htop : (pResidual 2 E).map g = ⊤ :=
    (map_pResidual_of_surjective 2 g hg).trans (isPStar_twoStarCore (G := H)).1
  intro y hy
  have hmem : (⟨y, hy⟩ : B) ∈ (pResidual 2 E).map g := by rw [htop]; trivial
  obtain ⟨x, hx, hxy⟩ := hmem
  exact mem_map.mpr ⟨(x : G), hle (mem_map.mpr ⟨x, hx, rfl⟩),
    congrArg Subtype.val hxy⟩
end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A central surjection preserves the two-star core, even with an even kernel. -/
theorem map_twoStarCore_of_surjective_central_kernel
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G) :
    (pStarCore 2 G).map f = pStarCore 2 H := by
  apply le_antisymm (map_pStarCore_le_of_surjective f hf)
  apply twoStarCore_le_map_of_central_kernel f hc
  rw [f.range_eq_top_of_surjective hf]
  exact le_top
end Subgroup
