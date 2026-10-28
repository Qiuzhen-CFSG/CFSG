module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Marked products of two simple two-core quotients

Two distinct C-components generating a finite group become disjoint commuting
simple factors modulo the ambient two-core. Multiplication in that quotient
therefore gives a surjection onto the two prescribed intrinsic quotients, with
kernel exactly the ambient two-core and with both factor coordinates retained.

This is the component product argument used in Aschbacher–Smith, D.3.5–6
and 10.1.1, printed pp.195–196 and741.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G S U : Type*} [Group G] [Finite G] [Group S] [Group U]
    [IsSimpleGroup S] [IsSimpleGroup U]
/-- The product quotient with the prescribed coordinates on both C-components. -/
theorem exists_twoCore_product_of_simple_pair (B C : Subgroup G) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hne : B ≠ C) (hgen : B ⊔ C = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* S) (eC : (C ⧸ pCore 2 C) ≃* U) :
    ∃ q : G →* S × U, Function.Surjective q ∧ q.ker = pCore 2 G ∧
      (∀ b : B, q b = (eB (QuotientGroup.mk' _ b), 1)) ∧
      (∀ c : C, q c = (1, eC (QuotientGroup.mk' _ c))) := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let A := B.map π
  let D := C.map π
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hA : A.IsCComponent := hB.map_quotient (pCore 2 G)
  have hD : D.IsCComponent := hC.map_quotient (pCore 2 G)
  let a : A ≃* S := (cComponentTwoCoreQuotientEquiv hB).symm.trans eB
  let d : D ≃* U := (cComponentTwoCoreQuotientEquiv hC).symm.trans eC
  let : IsSimpleGroup A := a.isSimpleGroup
  let : IsSimpleGroup D := d.isSimpleGroup
  let := hA.perfect
  have hne' : A ≠ D := fun he => hne (hB.eq_of_map_quotient_eq hC (pCore 2 G) he)
  have hc : A ≤ centralizer (D : Set (G ⧸ pCore 2 G)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (simple_subnormal_commute_of_ne A D hA.subnormal hD.subnormal hne')
  have hz : center A = ⊥ := by
    exact (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  have hd : Disjoint A D := by
    apply disjoint_def.mpr
    intro x hxA hxD
    have hx : (⟨x,hxA⟩ : A) ∈ center A := mem_center_iff.mpr fun y =>
      Subtype.ext ((hc y.property x hxD).symm)
    exact congrArg Subtype.val (show (⟨x,hxA⟩ : A) = 1 from mem_bot.mp (hz ▸ hx))
  have hg : A ⊔ D = ⊤ := by
    rw [← map_sup, hgen, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
  obtain ⟨f,hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A D hd hc
  let g : A × D ≃* (G ⧸ pCore 2 G) :=
    f.trans ((MulEquiv.subgroupCongr hg).trans topEquiv)
  have hgval (x : A) (y : D) : g (x,y) = (x : G ⧸ pCore 2 G) * y := hf x y
  let k : (G ⧸ pCore 2 G) ≃* S × U := g.symm.trans (a.prodCongr d)
  let q := k.toMonoidHom.comp π
  refine ⟨q, k.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_, ?_⟩
  · ext x
    change k (π x) = 1 ↔ x ∈ pCore 2 G
    rw [map_eq_one_iff k k.injective]
    exact QuotientGroup.eq_one_iff x
  · intro b
    have he : g (π.subgroupMap B b,1) = π b := by simpa using hgval (π.subgroupMap B b) 1
    change (a.prodCongr d) (g.symm (π b)) = _
    rw [← he, g.symm_apply_apply]
    change (a (π.subgroupMap B b), d 1) = _
    rw [map_one]
    congr 1
    change eB ((cComponentTwoCoreQuotientEquiv hB).symm (π.subgroupMap B b)) = _
    exact congrArg eB ((cComponentTwoCoreQuotientEquiv hB).symm_apply_apply
      (QuotientGroup.mk' _ b))
  · intro c
    have he : g (1,π.subgroupMap C c) = π c := by simpa using hgval 1 (π.subgroupMap C c)
    change (a.prodCongr d) (g.symm (π c)) = _
    rw [← he, g.symm_apply_apply]
    change (a 1, d (π.subgroupMap C c)) = _
    rw [map_one]
    congr 1
    change eC ((cComponentTwoCoreQuotientEquiv hC).symm (π.subgroupMap C c)) = _
    exact congrArg eC ((cComponentTwoCoreQuotientEquiv hC).symm_apply_apply
      (QuotientGroup.mk' _ c))
end Subgroup
