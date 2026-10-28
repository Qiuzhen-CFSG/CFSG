module
public import Stellmacher.SectionNine.DistanceOneQuadraticSubgroupIndex
public import Theory.GroupAction.Quadratic

/-!
# Quadratic subgroups in the actual faithful image for (9.1)

For any supplied faithful quotient witness on the actual initial center,
every quadratic subgroup of the image of the extracted cross-center product
has order at most two. The context, distance-one extraction and action are
unchanged; neither the faithful classification nor the local conclusion is
assumed.

Lift the image subgroup within the actual product V. Its two elementary
factors normalize one another, so the lift is a two-group. Exact witness
commutator and fixed-point transport turns quadraticity of the image into
ambient double-commutator vanishing. The native source-(5) index bound then
puts the lift's index over its intersection with the initial center at most
two. That intersection belongs to the quotient kernel, since the initial
center is abelian. The relative-index formula for the image proves the bound.

This is Stellmacher (9.1), relation (5), Journal of Algebra190 (1997), p.46,
in refs/files/stellmacher-n-group.pdf. Every quotient subgroup is lifted
inside V; no assumption that a two-group action is automatically quadratic
or that the full ambient kernel lies in V is used.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_quadratic_image_card_le_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ∀ X : Subgroup w.X, X ≤ (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection →
      IsQuadraticAction X (ZAt ctx.Γ ctx.criticalPath.a) → Nat.card X ≤ 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  change ∀ X : Subgroup w.X, X ≤ (V.subgroupOf P).map w.projection →
    IsQuadraticAction X Za → Nat.card X ≤ 2
  intro X hX hquad
  have hfactors := distance_one_product_factors Γ cp.a next
  have hVP : V ≤ P := hfactors.2.2.1.trans inf_le_left
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hnext : ZAt Γ next = Za.map (MulAut.conj data.x).toMonoidHom := by
    change z Γ (Γ.act data.x⁻¹ cp.a) = _
    rw [z_act, inv_inv]
  have hnextp : IsPGroup 2 (ZAt Γ next) := by
    rw [hnext]
    exact (IsElementaryAbelian.isPGroup 2 Za).map _
  have hVp : IsPGroup 2 V :=
    IsPGroup.to_sup_of_normal_right'
      ((IsElementaryAbelian.isPGroup 2 Za).to_le inf_le_left)
      (hnextp.to_le inf_le_left) hfactors.1
  let Y1 := V.subgroupOf P ⊓ X.comap w.projection
  let Y := Y1.map P.subtype
  have hYP : Y ≤ P := Subgroup.map_subtype_le _
  have hYV : Y ≤ V := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVP]
    exact Subgroup.map_mono inf_le_left
  have hYimage : (Y.subgroupOf P).map w.projection = X := by
    rw [show Y = Y1.map P.subtype from rfl, subgroupOf_map_subtype_eq]
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y,hy,he⟩ := hX hx
      exact ⟨y,⟨hy,show w.projection y ∈ X from he ▸ hx⟩,he⟩
  have hnativequad : ⁅⁅Za,Y⁆,Y⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    have hf := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad
    have hfm := Subgroup.map_mono (f := Za.subtype) hf
    rw [← hYimage, w.commutatorAction_image_map_subtype Y hYP,
      w.fixedPoints_map_subtype Y hYP] at hfm
    exact hfm.trans inf_le_right
  have hbound := distance_one_quadratic_subgroup_index_le_two ctx hb data Y hYV
    (hVp.to_le hYV) hnativequad
  let W := Y ⊓ Za
  have hWY : W ≤ Y := inf_le_left
  have hWP : W ≤ P := hWY.trans hYP
  have hWker : W.subgroupOf P ≤ w.projection.ker := by
    intro y hy
    rw [w.kernel_eq]
    refine ⟨y.property, ?_⟩
    exact Subgroup.le_centralizer Za hy.2
  have hrel : Nat.card X ≤ W.relIndex Y := by
    rw [← hYimage, ← Subgroup.relIndex_ker,
      ← Subgroup.relIndex_subgroupOf hYP]
    apply Subgroup.relIndex_le_of_le_left hWker
    rw [Subgroup.relIndex_subgroupOf hYP]
    intro hz
    have hm := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) W Y bot_le hWY
    simp only [Subgroup.relIndex_bot_left, hz, Nat.mul_zero] at hm
    have hp : 0 < Nat.card Y := Nat.card_pos
    omega
  have hrelbound : W.relIndex Y ≤ 2 := by
    have hmul := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) W Y bot_le hWY
    simp only [Subgroup.relIndex_bot_left] at hmul
    have hp : 0 < Nat.card W := Nat.card_pos
    change Nat.card Y ≤ 2 * Nat.card W at hbound
    nlinarith
  exact hrel.trans hrelbound
end Stellmacher.SectionNine
