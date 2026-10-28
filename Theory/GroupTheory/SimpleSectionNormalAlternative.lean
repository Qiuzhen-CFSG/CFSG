module
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Simple sections across a normal subgroup

If a subgroup of G surjects onto a simple group T, then either a subgroup
of a chosen normal subgroup N surjects onto T, or a subgroup of G/N does.
The image of N intersected with the original subgroup is normal in T.
If that image is all of T, restrict the original map; if it is trivial,
factor through the actual quotient image. No finiteness is required.

This elementary section transfer is used in ABG II.3 Lemma2, article p24,
to remove kernels and outer quotients before applying the PSL2 subgroup
classification. All sections are actual subgroup surjections and hence
actual quotients by their normal kernels.
-/

namespace Subgroup

public theorem simple_section_normal_or_quotient
    {G T : Type*} [Group G] [Group T] [IsSimpleGroup T]
    (N : Subgroup G) [N.Normal] (U : Subgroup G)
    (f : U →* T) (hf : Function.Surjective f) :
    (∃ W : Subgroup N, ∃ g : W →* T, Function.Surjective g) ∨
      ∃ W : Subgroup (G ⧸ N), ∃ g : W →* T, Function.Surjective g := by
  let P := N.subgroupOf U
  have hnormal : (P.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map f) hnormal with hbot | htop
  · right
    let q := QuotientGroup.mk' N
    let W := U.map q
    let qU : U →* W := q.subgroupMap U
    have hqU : Function.Surjective qU := q.subgroupMap_surjective U
    have hker : qU.ker ≤ f.ker := by
      intro x hx
      have hxN : (x : G) ∈ N := by
        have hqx : q (x : G) = 1 := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff _).mp hqx
      have hfx : f x ∈ P.map f := Subgroup.mem_map_of_mem f hxN
      exact Subgroup.mem_bot.mp (hbot ▸ hfx)
    let g : W →* T := qU.liftOfSurjective hqU ⟨f, hker⟩
    refine ⟨W, g, ?_⟩
    intro t
    obtain ⟨x, rfl⟩ := hf t
    exact ⟨qU x, by simp [g]⟩
  · left
    let W := U.subgroupOf N
    let g : W →* T := {
      toFun := fun x => f ⟨x.1.1, x.2⟩
      map_one' := f.map_one
      map_mul' := fun x y => by
        change f ((⟨x.1.1, x.2⟩ : U) * ⟨y.1.1, y.2⟩) = _
        exact f.map_mul _ _ }
    refine ⟨W, g, ?_⟩
    intro t
    have ht : t ∈ P.map f := htop ▸ mem_top t
    obtain ⟨x, hx, hfx⟩ := ht
    exact ⟨⟨⟨x.1, hx⟩, x.2⟩, hfx⟩

end Subgroup
