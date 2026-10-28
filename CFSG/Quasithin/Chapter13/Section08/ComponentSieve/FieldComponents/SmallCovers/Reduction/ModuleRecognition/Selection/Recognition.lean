module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.Quotient

/-!
# Applying the universal irreducible input to the entire actor

The B.4.5 input quantifies over intermediate subgroups, including the top
subgroup. A nontrivial elementary quadratic subgroup witnessing q ≤ 2 lifts
to that copy of the actor with unchanged rank and fixed codimension. We then
transport the faithful actor map, component image and linear coordinates back
to the original group. Irreducibility and faithfulness are required on the
exact representation; no module dimension is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.5,
printed pp.86–87; application to 13.8.21(2), printed p.956.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection
universe u v

/-- Universal irreducible B.4.5 recognition, applied to the entire actor and
transported from its top subgroup. -/
theorem hexacodeModel_of_small_ratio {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D)
    (inputs : IrreducibleInputs.{u,v} L) (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp L.subtype)) (hq : quadraticRatio ρ ≤ 2) :
    Nonempty (HexacodeModel L ρ) := by
  let J : Subgroup D := ⊤
  let t : J ≃* D := Subgroup.topEquiv
  let τ := ρ.comp J.subtype
  have hi : IsIrreducible (τ.comp (L.subgroupOf J).subtype) :=
    (irreducible_comp_surjective_iff (subgroupOfEquivOfLe (show L ≤ J from le_top)).toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ J from le_top)).surjective (ρ.comp L.subtype)).mpr hirr
  have hqτ : quadraticRatio τ ≤ 2 := by
    obtain ⟨A, hA, hquad, hbound⟩ := (quadraticRatio_le_two_iff ρ).mp hq
    let A₀ := A.subgroupOf J
    have hm : A₀.map J.subtype = A := map_subgroupOf_eq_of_le le_top
    have helem : IsElementaryTwo A₀ := by
      let : IsElementaryAbelian 2 A := hA.2
      refine ⟨?_, IsElementaryAbelian.subgroupOf (show A ≤ J from le_top)⟩
      intro hb
      apply hA.1
      rw [← hm, hb, Subgroup.map_bot]
    have hc : fixedCodim τ A₀ = fixedCodim ρ A := by
      unfold fixedCodim
      rw [fixedSpace_comp_map, hm]
    have hr : rank A₀ = rank A := by
      rw [← rank_map_injective J.subtype J.subtype_injective, hm]
    apply (quadraticRatio_le_two_iff τ).mpr
    exact ⟨A₀, helem, fun a ha b hb w => hquad a.val ha b.val hb w,
      by rw [hc, hr]; exact hbound⟩
  obtain ⟨m⟩ := inputs.small J le_top W τ (hfaith.comp J.subtype_injective) hi hqτ
  refine ⟨{
    actor := m.actor.comp t.symm.toMonoidHom
    faithful := m.faithful.comp t.symm.injective
    component_image := ?_
    coordinates := m.coordinates
    intertwines := fun g w => m.intertwines (t.symm g) w }⟩
  rw [← Subgroup.map_map]
  have hm : L.map t.symm.toMonoidHom = L.subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_map, map_subgroupOf_eq_of_le (show L ≤ J from le_top)]
    change L.map (MonoidHom.id D) = L
    exact Subgroup.map_id L
  rw [hm]
  exact m.component_image

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Selection
