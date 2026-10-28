module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.InnerRadicalNormalizer

/-!+# Radical-preserving automorphisms control the original normalizer

Only automorphisms preserving the actual quotient radical need to be
inner. The original radical acts by such automorphisms on the normal
ordinary component. Faithful descent through the full center lifts their
innerness to the perfect cover, and radical saturation then puts the
intersection normalizer in the original local subgroup.

Source: Aschbacher--Smith C.2.2(1), C.2.8 and C.3.3, pp.144,147,149.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
variable {H M L R V : Subgroup G}

/-- Innerness is required only on automorphisms preserving the actual
radical image in the full central quotient. -/
theorem ordinary_radical_normalizer_le_local_of_preserving_inner
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Q)
    (hi : let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
      ∀ a : MulAut Q,
        (((R.subgroupOf H).subgroupOf K).map q).map a.toMonoidHom =
          ((R.subgroupOf H).subgroupOf K).map q →
        a ∈ MulAut.innerSubgroup Q) :
    normalizer ((R.subgroupOf H).subgroupOf K : Set K) ≤
      (M.subgroupOf H).subgroupOf K := by
  let := h.ordinary_component_normal K hK
  let := hK.2
  let RH := R.subgroupOf H
  let RK := RH.subgroupOf K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hr : RH ≤ K ⊔ centralizer (K : Set H) := by
    rw [←MulAut.conjNormal_comap_innerSubgroup K]
    intro r hr
    let a : MulAut K := MulAut.conjNormal r
    have hRK : RK.map a.toMonoidHom = RK := by
      apply le_antisymm
      · rintro y ⟨x,hx,rfl⟩
        change r * (x : H) * r⁻¹ ∈ RH
        exact RH.mul_mem (RH.mul_mem hr hx) (RH.inv_mem hr)
      · intro y hy
        refine ⟨(MulAut.conjNormal (r⁻¹) : MulAut K) y,?_,?_⟩
        · change r⁻¹ * (y : H) * (r⁻¹)⁻¹ ∈ RH
          simpa only [inv_inv,Subgroup.subtype_apply] using
            RH.mul_mem (RH.mul_mem (RH.inv_mem hr) hy) hr
        · apply Subtype.ext
          change r * (r⁻¹ * (y : H) * (r⁻¹)⁻¹) * r⁻¹ = (y : H)
          simp [mul_assoc]
    let aq := MulAut.centralQuotientAction e a
    have hqa : aq.toMonoidHom.comp q = q.comp a.toMonoidHom := by
      ext x
      exact MulAut.centralQuotientAction_apply e a x
    have hP : (RK.map q).map aq.toMonoidHom = RK.map q := by
      rw [map_map,hqa,←map_map,hRK]
    have hinner := hi aq hP
    rw [←MulAut.comap_inner_centralQuotientAction e]
    exact hinner
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hZ : IsPGroup 2 (center K) := hz.symm ▸ pCore_isPGroup
  have hn := radical_intersection_normalizer_le K RH h.isRadical hZ hr
  have hRH := h.radical_le.trans h.local_le
  intro x hx
  have hx' : (x : H) ∈ normalizer (RH ⊓ K : Set H) := by
    have hh := RK.le_normalizer_map K.subtype (mem_map_of_mem K.subtype hx)
    rwa [subgroupOf_map_subtype] at hh
  have hh := hn ⟨x.property,hx'⟩
  rw [←subgroupOf_normalizer_eq hRH] at hh
  exact h.normalizer_le ⟨x.val.property,hh⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
