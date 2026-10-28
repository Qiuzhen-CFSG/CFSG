module
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo

/-!
# Normal solvable subgroups of native M₂₄ octad stabilizers

The action on the seed octad surjects onto A₈ and has an order-16 kernel.
A normal solvable subgroup has trivial image in A₈, since that quotient
is simple and perfect. Its order therefore divides sixteen. Native octad
transitivity transports the exclusion of nine to every octad stabilizer.

Source: GLS3, Table 5.3e, E₁₆.A₈; Aschbacher--Smith, 15.3.41--42,
printed p.1138. The kernel and quotient are the already proved actions of
the concrete Witt-design carrier, not an abstract extension shape.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
open Subgroup LinearFourCore
open scoped Pointwise

private theorem seedOctad_normal_solvable_not_nine
    (D : Subgroup (octadStabilizer seedOctad)) (hn : D.Normal)
    (hs : Group.IsSolvable D) : ¬ 9 ∣ Nat.card D := by
  let : D.Normal := hn
  let : Group.IsSolvable D := hs
  let f := alternatingAction
  let A := alternatingGroup seedOctad.val
  let X := D.map f
  let : X.Normal := Subgroup.Normal.map hn f alternatingAction_surjective
  let : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := f.subgroupMap D) (f.subgroupMap_surjective D)
  have hX : X = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
      (by rw [seed_card]; decide) (N := X) with h | h
    · exact h
    · let : Group.IsSolvable A := Group.isSolvable_of_surjective
        (f := X.subtype) (MonoidHom.range_eq_top.mp (by rw [subtype_range, h]))
      let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by rw [seed_card]; decide)
      let : Group.IsPerfect (octadStabilizer seedOctad) := seed_perfect
      let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
        (f := f) alternatingAction_surjective
      exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  have hD : D ≤ (action seedOctad).ker := by
    intro x hx
    have hf : f x = 1 := mem_bot.mp (hX ▸ (show f x ∈ X from ⟨x, hx, rfl⟩))
    change action seedOctad x = 1
    rw [← alternatingAction_coe]
    exact congrArg Subtype.val hf
  intro h9
  have hc := h9.trans (card_dvd_of_le hD)
  rw [kernel_card] at hc
  norm_num at hc

/-- No normal solvable subgroup of an actual octad stabilizer has order
divisible by nine: its image in A₈ is trivial, so it lies in the order-16 kernel. -/
theorem octad_normal_solvable_not_nine (O : Octad)
    (D : Subgroup (octadStabilizer O)) (hn : D.Normal)
    (hs : Group.IsSolvable D) : ¬ 9 ∣ Nat.card D := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq O seedOctad
  let e : octadStabilizer O ≃* octadStabilizer seedOctad :=
    MulAction.stabilizerEquivStabilizer (G := M24) hg.symm
  let X := D.map e.toMonoidHom
  let : D.Normal := hn
  let : Group.IsSolvable D := hs
  have hXn : X.Normal := Subgroup.Normal.map hn e.toMonoidHom e.surjective
  have hXs : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := (e.subgroupMap D).toMonoidHom) (e.subgroupMap D).surjective
  have h := seedOctad_normal_solvable_not_nine X hXn hXs
  rwa [card_map_of_injective e.injective] at h

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
