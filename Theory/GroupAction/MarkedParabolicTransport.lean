module
public import Theory.GroupAction.ResidualMovingPointTransport
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Transport of marked elementary subgroups in a parabolic pair

Compatible isomorphisms of the two parabolics give the same image of every
subgroup in their overlap. Consequently an elementary subgroup transported
through the second parabolic still lies in the actual two-core of the first.
Normality is relative to the second parabolic. The order, elementary structure,
and the actual residual conjugation moving the marked point are retained.

Application: the G₂(2) and M₁₂ concrete inputs in Aschbacher–Smith,
Lemma 14.2.21, printed p.988. No ambient-group extension of the pair
isomorphism is required.
-/

namespace Subgroup
variable {G G' : Type*} [Group G] [Group G']

/-- Core containment is preserved even when the subgroup is mapped through the other parabolic. -/
public theorem pair_map_le_two_core (H A T : Subgroup G) (H' A' : Subgroup G')
    (hTH : T ≤ H) (hTA : T ≤ A) (eH : H ≃* H') (eA : A ≃* A')
    (hcompat : ∀ t : T,
      (eH ⟨t, hTH t.property⟩ : G') = (eA ⟨t, hTA t.property⟩ : G'))
    (E : Subgroup G) (hET : E ≤ T) (hEQ : E ≤ H.pCoreIn 2) :
    ((E.subgroupOf A).map eA.toMonoidHom).map A'.subtype ≤ H'.pCoreIn 2 := by
  rw [← pair_map_eq_of_compatible H A T H' A' hTH hTA eH eA hcompat E hET]
  have h : E.subgroupOf H ≤ pCore 2 H := by
    intro x hx
    obtain ⟨q,hq,hqx⟩ := hEQ hx
    have he : q = x := Subtype.ext hqx
    rwa [he] at hq
  change _ ≤ (pCore 2 H').map H'.subtype
  rw [← pCore_map_iso 2 eH]
  exact map_mono (map_mono h)

/-- Relative normality, elementary order eight, and residual movement in the ambient image. -/
public theorem map_normal_elementary_eight_moving_point
    (A : Subgroup G) (A' : Subgroup G') (e : A ≃* A')
    (E : Subgroup G) (hEA : E ≤ A) [IsElementaryAbelian 2 E]
    [(E.subgroupOf A).Normal] (hE : Nat.card E = 8)
    (z : G) (hz : z ∈ E) (y : A) (hy : y ∈ pResidual 2 A)
    (hm : (y : G) * z * (y : G)⁻¹ ≠ z) :
    let E' := ((E.subgroupOf A).map e.toMonoidHom).map A'.subtype
    let z' := (e ⟨z, hEA hz⟩ : G')
    E' ≤ A' ∧ (E'.subgroupOf A').Normal ∧
      IsElementaryAbelian 2 E' ∧ Nat.card E' = 8 ∧ z' ∈ E' ∧
      ∃ y' : A', y' ∈ pResidual 2 A' ∧
        (y' : G') * z' * (y' : G')⁻¹ ≠ z' := by
  dsimp only
  let E₀ := E.subgroupOf A
  let E₁ := E₀.map e.toMonoidHom
  let E₂ := E₁.map A'.subtype
  have hE₀ : Nat.card E₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv).trans hE
  have hE₁ : Nat.card E₁ = 8 :=
    (Nat.card_congr (e.subgroupMap E₀).toEquiv).symm.trans hE₀
  have hE₂ : Nat.card E₂ = 8 :=
    (Nat.card_congr (E₁.equivMapOfInjective A'.subtype A'.subtype_injective).toEquiv).symm.trans hE₁
  have hnormal : (E₂.subgroupOf A').Normal := by
    change (E₁.map A'.subtype |>.comap A'.subtype).Normal
    rw [comap_map_eq_self_of_injective A'.subtype_injective]
    exact Normal.map (inferInstance : E₀.Normal) e.toMonoidHom e.surjective
  have habel : IsElementaryAbelian 2 E₂ := by
    let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hEA
    let : IsElementaryAbelian 2 E₁ := IsElementaryAbelian.map e.toMonoidHom
    exact IsElementaryAbelian.map A'.subtype
  refine ⟨map_subtype_le _, hnormal, habel, hE₂, ?_, e y, ?_, ?_⟩
  · exact ⟨e ⟨z, hEA hz⟩, ⟨⟨z, hEA hz⟩, hz, rfl⟩, rfl⟩
  · rw [← map_pResidual 2 e]
    exact ⟨y, hy, rfl⟩
  · intro h
    apply hm
    have hi : y * (⟨z, hEA hz⟩ : A) * y⁻¹ = ⟨z, hEA hz⟩ := by
      apply e.injective
      apply Subtype.ext
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
    exact congrArg Subtype.val hi

/-- The complete marked chain used by the elementary-eight argument, transported
through compatible parabolic isomorphisms. All core and residuals are literal. -/
public theorem pair_elementary_eight_transport
    (H A T V E : Subgroup G) (H' A' : Subgroup G')
    (hTH : T ≤ H) (hTA : T ≤ A) (eH : H ≃* H') (eA : A ≃* A')
    (hcompat : ∀ t : T,
      (eH ⟨t, hTH t.property⟩ : G') = (eA ⟨t, hTA t.property⟩ : G'))
    (hVE : V ≤ E) (hET : E ≤ T) (hEQ : E ≤ H.pCoreIn 2)
    [IsElementaryAbelian 2 E] [(E.subgroupOf A).Normal] (hE : Nat.card E = 8)
    (z : G) (hz : z ∈ E) (y : A) (hy : y ∈ pResidual 2 A)
    (hm : (y : G) * z * (y : G)⁻¹ ≠ z) :
    let V' := ((V.subgroupOf A).map eA.toMonoidHom).map A'.subtype
    let E' := ((E.subgroupOf A).map eA.toMonoidHom).map A'.subtype
    let z' := (eA ⟨z, hTA (hET hz)⟩ : G')
    V' ≤ E' ∧ E' ≤ H'.pCoreIn 2 ∧ E' ≤ A' ∧ (E'.subgroupOf A').Normal ∧
      IsElementaryAbelian 2 E' ∧ Nat.card E' = 8 ∧ z' ∈ E' ∧
      ∃ y' : A', y' ∈ pResidual 2 A' ∧
        (y' : G') * z' * (y' : G')⁻¹ ≠ z' := by
  refine ⟨map_mono (map_mono (fun _ hx => hVE hx)),
    pair_map_le_two_core H A T H' A' hTH hTA eH eA hcompat E hET hEQ, ?_⟩
  exact map_normal_elementary_eight_moving_point A A' eA E (hET.trans hTA) hE z hz y hy hm

end Subgroup
