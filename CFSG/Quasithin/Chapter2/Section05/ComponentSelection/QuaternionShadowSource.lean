module

public import Theory.GroupTheory.QuaternionShadowCentralizers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.AlternatingSix.M10.SylowSemidihedral

/-!
# The terminal quaternion-shadow contradiction

The original M₁₀ action restricts to the actual Sylow subgroup with its exact
quaternion kernel. The component Sylow is dihedral eight, and the original
2.5.5 disjoint-core theorem supplies the commuting conjugate quaternion copy.
The intrinsic model theorem derives incompatible centralizer orders, because
the crossing element acts on the ambient Sylow subgroup.

Source: Aschbacher--Smith, Lemma 2.5.21, printed p.567. No centralizer
cardinality is assumed by this adapter: both orders come from the checked
quaternion and semidihedral models.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection


/-- The subgroup-level terminal quaternion contradiction. -/
theorem quaternion_shadow_contradiction
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (f : S →* Semidihedral.StandardModel 4 (by decide))
    (C D U : Subgroup S)
    (hker : f.ker = C)
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hU : Nonempty (U ≃* DihedralGroup 4))
    (hCD : Disjoint C D) (hCU : Disjoint C U)
    (hDC : D ≤ centralizer (C : Set S))
    (hUC : U ≤ centralizer (C : Set S))
    (a : MulAut S) (ha : D = C.map a.toMonoidHom) : False := by
  subst D
  obtain ⟨eC⟩ := hC
  obtain ⟨eU⟩ := hU
  exact Theory.GroupTheory.QuaternionShadow.no_disjoint_commuting_copy
    f C U hker eC eU hCU hUC a hCD hDC

open ComponentRefinement Stellmacher
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
/-- The terminal quaternion branch of original 2.5.21, on the literal source
setup and the actual M₁₀ quotient action. Normality of the component comes
from 2.5.20 and the M₁₀ action from the preceding 2.5.16 branch; all Sylow,
disjointness, commutation, and centralizer-order premises are discharged here. -/
theorem MathieuSourceSetup.quaternion_m10_impossible
    (c : MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (eK : L ≃* AlternatingSix.ShadowLocal.A6)
    (f : H →* AlternatingSix.M10.extension) (hf : Function.Surjective f)
    (hk : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (L : Set G)).subgroupOf H)
    (eC : (((S : Subgroup H).map H.subtype) ⊓ centralizer (L : Set G) : Subgroup G) ≃* QuaternionGroup 2)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer (((S : Subgroup H).map H.subtype) : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype) : False := by
  let Y := (S : Subgroup H).map H.subtype
  let C := (Y ⊓ centralizer (L : Set G)).subgroupOf Y
  let U := L.subgroupOf Y
  let eY : S ≃* Y := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨qS, _, hqS⟩ := AlternatingSix.M10.exists_sylow_semidihedral_epimorphism f hf S
  let q := qS.comp eY.symm.toMonoidHom
  have hq : q.ker = C := by
    ext y
    change qS (eY.symm y) = 1 ↔ (y : G) ∈ Y ⊓ centralizer (L : Set G)
    rw [hqS, ← MonoidHom.mem_ker, hk]
    change ((eY.symm y : S) : H).val ∈ Y ⊓ centralizer (L : Set G) ↔ _
    have he : ((eY.symm y : S) : H).val = (y : G) :=
      congrArg Subtype.val (eY.apply_symm_apply y)
    rw [he]
  have hcore := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hd := generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le, c.component⟩ hgen hxT hxS hxN hx2
  rw [hcore] at hd
  let a : MulAut Y := Y.normalizerMonoidHom ⟨x⁻¹, (normalizer (Y : Set G)).inv_mem hxN⟩
  have ha (y : Y) : (a y : G) = x⁻¹ * y * x := by
    simp only [a, normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hD (y : Y) (hy : y ∈ C.map a.toMonoidHom) :
      (y : G) ∈ (Y ⊓ centralizer (L : Set G)).conjBy x⁻¹ := by
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨(w : G), hw, ?_⟩
    change x⁻¹ * (w : G) * (x⁻¹)⁻¹ = (a w : G)
    simpa only [inv_inv] using (ha w).symm
  have hCD : Disjoint C (C.map a.toMonoidHom) := by
    apply disjoint_iff_inf_le.mpr
    intro y hy
    apply Subtype.ext
    exact disjoint_iff_inf_le.mp hd.1 ⟨hy.1, hD y hy.2⟩
  have hDC : C.map a.toMonoidHom ≤ centralizer (C : Set Y) := by
    intro y hy w hw
    apply Subtype.ext
    exact ((hd.2.1 hw) _ (hD y hy)).symm
  have hCU : Disjoint C U := by
    apply disjoint_iff_inf_le.mpr
    intro y hy
    have hz : (⟨(y : G), hy.2⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      exact Subtype.ext (hy.1.2 l l.property)
    have hez := (centerCongr eK ⟨⟨(y : G), hy.2⟩, hz⟩).property
    change eK ⟨(y : G), hy.2⟩ ∈ center AlternatingSix.ShadowLocal.A6 at hez
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
    have he : (y : G) = 1 := congrArg (fun l : L => (l : G))
      (eK.injective (hez.trans eK.map_one.symm))
    exact Subtype.ext he
  have hUC : U ≤ centralizer (C : Set Y) := by
    intro u hu w hw
    exact Subtype.ext (hw.2 u hu).symm
  let eC' : C ≃* QuaternionGroup 2 := (subgroupOfEquivOfLe inf_le_left).trans eC
  obtain ⟨P, hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  let swap : U ≃* Y.subgroupOf L := {
    toFun u := ⟨⟨u.val.val, u.property⟩, u.val.property⟩
    invFun u := ⟨⟨u.val.val, u.property⟩, u.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let P' := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨eP⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral P'
  let eU : U ≃* DihedralGroup 4 := swap.trans ((MulEquiv.subgroupCongr hP.symm).trans
    (((P : Subgroup L).equivMapOfInjective eK.toMonoidHom eK.injective).trans eP))
  exact Theory.GroupTheory.QuaternionShadow.no_disjoint_commuting_copy
    q C U hq eC' eU hCU hUC a hCD hDC

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
