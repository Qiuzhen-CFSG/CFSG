module
public import Theory.SpecificGroups.SymmetricFourWreath.CentralFactorGeometry
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates
/-!
# Normal elementary planes in the dihedral wreath Sylow subgroup

A normal elementary subgroup of order sixteen in D8 wreath C2 uses the same
one of the two elementary planes in both coordinates. Its intersection with
the quaternion central-product core has order eight. In a direct product with
an elementary central factor, this gives index two modulo the intrinsic
extraspecial core times that factor; the Thompson subgroup has index four.

These indices retain an arbitrary normal extraspecial subgroup of order 32,
so they apply to the literal Borel residual core in Aschbacher--Smith 2.4.29.
-/
public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm

theorem mem_pair_range (x : P) : x ∈ pair.range ↔ x.right=1 := by
  constructor
  · rintro ⟨a,rfl⟩;rfl
  · intro hx
    refine ⟨(x.left 1,x.left turn),?_⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases c2_eq_one_or_turn i with rfl | rfl
      · simp [pair]
      · simp [pair,turn_ne_one]
    · exact hx.symm

theorem mem_elementaryInP (b c : Bool) (x : P) : x ∈ elementaryInP b c ↔
    x.right=1 ∧ x.left 1∈plane b ∧ x.left turn∈plane c := by
  constructor
  · rintro ⟨⟨a,d⟩,⟨ha,hd⟩,rfl⟩
    exact ⟨rfl,by simpa [pair] using ha,by simpa [pair,turn_ne_one] using hd⟩
  · rintro ⟨hx,ha,hd⟩
    refine ⟨(x.left 1,x.left turn),⟨ha,hd⟩,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases c2_eq_one_or_turn i with rfl | rfl
      · simp [pair]
      · simp [pair,turn_ne_one]
    · exact hx.symm

private instance (b c : Bool) : DecidablePred (·∈elementaryInP b c) := fun x=>
  decidable_of_iff _ (mem_elementaryInP b c x).symm
private instance : DecidablePred (·∈coreInP) := fun x=>
  decidable_of_iff _ (mem_coreInP x).symm
private instance : DecidablePred (·∈pair.range) := fun x=>
  decidable_of_iff _ (mem_pair_range x).symm

theorem normal_elementary_sixteen_eq_same_planes (U : Subgroup P)
    [U.Normal] (hU : IsElementaryAbelian 2 U) (hc : Nat.card U=16) :
    ∃b, U=elementaryInP b b := by
  obtain ⟨b,c,he⟩ := (maximum_elementaryInP U).mp
    ⟨le_top,hU,fun E _ hE=>(elementaryInP_card_bound E hE).trans_eq hc.symm⟩
  have hn : (elementaryInP b c).Normal := he ▸ inferInstance
  have hx : pair (DihedralGroup.sr (if b then 1 else 0),1)∈elementaryInP b c := by
    cases b <;> cases c <;> decide +kernel
  have hy := hn.conj_mem _ hx (RegularWreathProduct.inl turn)
  have htest : ∀ b c : Bool,
      RegularWreathProduct.inl turn * pair (DihedralGroup.sr (if b then 1 else 0),1) *
        (RegularWreathProduct.inl turn)⁻¹ ∈ elementaryInP b c → b=c := by
    decide +kernel
  obtain rfl := htest b c hy
  exact ⟨b,he⟩

theorem card_elementaryInP_inf_core_same (b : Bool) :
    Nat.card (elementaryInP b b ⊓ coreInP : Subgroup P)=8 := by
  let : DecidablePred (·∈(elementaryInP b b ⊓ coreInP : Subgroup P)) := fun x=>
    inferInstanceAs (Decidable (x∈elementaryInP b b ∧ x∈coreInP))
  let : Fintype (elementaryInP b b ⊓ coreInP : Subgroup P) := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  cases b <;> decide +kernel

theorem card_pair_inf_core : Nat.card (pair.range ⊓ coreInP : Subgroup P)=16 := by
  let : DecidablePred (·∈(pair.range ⊓ coreInP : Subgroup P)) := fun x=>
    inferInstanceAs (Decidable (x∈pair.range ∧ x∈coreInP))
  let : Fintype (pair.range ⊓ coreInP : Subgroup P) := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pair_sup_core : pair.range ⊔ coreInP = ⊤ := by
  apply top_unique
  intro x _
  let y := quaternionEmbedding true (QuaternionGroup.a 1)
  have hy : y∈coreInP := ⟨(1,QuaternionGroup.a 1),by simp [quaternionProduct,y]⟩
  have hyr : y.right=turn := by decide +kernel
  by_cases hx : x.right=1
  · exact mem_sup_left ((mem_pair_range x).mpr hx)
  · have hr : x.right=turn := (c2_eq_one_or_turn _).resolve_left hx
    have hx' : x*y⁻¹∈pair.range := (mem_pair_range _).mpr (by
      change x.right * y.right⁻¹=1
      rw [hr,hyr,mul_inv_cancel])
    have hm := (pair.range⊔coreInP).mul_mem (mem_sup_left hx') (mem_sup_right hy)
    simpa only [inv_mul_cancel_right] using hm

variable {D S : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
  [Group S] [Finite S]

theorem core_sup_factor_eq_comap_of_equiv_prod (e : S ≃* P×D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q=32) :
    Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker =
      coreInP.comap ((MonoidHom.fst P D).comp e.toMonoidHom) := by
  let a := (MonoidHom.fst P D).comp e.toMonoidHom
  let f := ((centralProjection.comp (MonoidHom.fst P D)).prod
    (MonoidHom.snd P D)).comp e.toMonoidHom
  let E := Q⊔a.ker
  obtain ⟨_,hk,hJ⟩ := thompson_image_of_equiv_prod e Q hQ
  have hm : E.map f=quotientCore.prod ⊤ := hJ.symm.trans thompson_centralQuotient_prod
  have hle : f.ker≤E := hk.le.trans ((map_subtype_le _).trans le_sup_left)
  change E=coreInP.comap a
  rw [←comap_map_eq_self hle,hm]
  ext x
  change centralProjection (a x)∈quotientCore ∧ (e x).2∈(⊤:Subgroup D) ↔ a x∈coreInP
  simp only [mem_top,and_true]
  rw [←quotientCore_comap]
  rfl

private theorem card_inf_mul_relIndex (H K : Subgroup P) :
    Nat.card (K⊓H : Subgroup P)*H.relIndex K=Nat.card K := by
  have hh := ((K⊓H : Subgroup P).subgroupOf K).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show K⊓H≤K from inf_le_left)).toEquiv] at hh
  change Nat.card (K⊓H : Subgroup P)*(K⊓H).relIndex K=Nat.card K at hh
  rwa [inf_relIndex_left K H] at hh

theorem core_sup_factor_relIndex_normal_elementary (e : S ≃* P×D)
    (Q U : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q=32)
    [U.Normal] (hU : IsElementaryAbelian 2 U) (hc : Nat.card U=16)
    (hd : Disjoint U ((MonoidHom.fst P D).comp e.toMonoidHom).ker) :
    (Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker).relIndex U=2 := by
  let a := (MonoidHom.fst P D).comp e.toMonoidHom
  have ha : Function.Surjective a := fun p=>⟨e.symm (p,1),by simp [a]⟩
  let Ua := U.map a
  have hai : Function.Injective (a.comp U.subtype) := by
    intro x y hxy
    have hker : (x*y⁻¹ : U).val∈a.ker := by
      change a ((x:S)*(y:S)⁻¹)=1
      rw [map_mul,map_inv]
      exact mul_inv_eq_one.mpr hxy
    have hh : ((x*y⁻¹ : U):S)=1 := disjoint_def.mp hd (x*y⁻¹).property hker
    exact mul_inv_eq_one.mp (Subtype.ext hh)
  have hcard : Nat.card Ua=16 := by
    have hr : (a.comp U.subtype).range=Ua := by rw [MonoidHom.range_comp,range_subtype]
    let eu := (MonoidHom.ofInjective hai).trans (MulEquiv.subgroupCongr hr)
    exact (Nat.card_congr eu.toEquiv).symm.trans hc
  let : Ua.Normal := (inferInstance : U.Normal).map a ha
  obtain ⟨b,hb⟩ := normal_elementary_sixteen_eq_same_planes Ua (hU.map a) hcard
  rw [core_sup_factor_eq_comap_of_equiv_prod e Q hQ,relIndex_comap]
  change coreInP.relIndex Ua=2
  have hh := card_inf_mul_relIndex coreInP Ua
  rw [hcard] at hh
  rw [hb,card_elementaryInP_inf_core_same] at hh
  rw [hb]
  omega

theorem thompson_P_eq_pair : Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup P)=pair.range := by
  apply map_injective (f:=sylowEmbedding) sylowEmbedding_injective
  rw [←Stellmacher.elementaryAbelianMaxJ_map_injective sylowEmbedding sylowEmbedding_injective,
    ←MonoidHom.range_eq_map,←standardSylow_coe,elementary_thompson]
  rfl

theorem core_sup_factor_relIndex_thompson (e : S ≃* P×D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q=32) :
    (Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker).relIndex
      (Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup S))=4 := by
  let a := (MonoidHom.fst P D).comp e.toMonoidHom
  have hj : (Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup S)).map a=pair.range := by
    dsimp only [a]
    rw [← map_map,←Stellmacher.elementaryAbelianMaxJ_map_injective e.toMonoidHom e.injective,
      map_top_of_surjective e.toMonoidHom e.surjective,←top_prod_top,
      Stellmacher.elementaryAbelianMaxJ_prod,thompson_P_eq_pair]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩;exact hx.1
    · intro p hp
      exact ⟨(p,1),⟨hp,(Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup D)).one_mem⟩,rfl⟩
  rw [core_sup_factor_eq_comap_of_equiv_prod e Q hQ,relIndex_comap,hj]
  have hh := card_inf_mul_relIndex coreInP pair.range
  have hcard : Nat.card pair.range=64 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective pair_injective).toEquiv,Nat.card_prod,
      DihedralGroup.nat_card]
  rw [card_pair_inf_core,hcard] at hh
  omega
end SymmetricFourWreath
