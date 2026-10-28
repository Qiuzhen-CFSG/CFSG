module
public import Theory.SpecificGroups.PSL2.PrimeInvolutionFixedGeneration
public import Theory.SpecificGroups.PSL2.AdjacentPowerSylow
public import Theory.GroupTheory.IndexTwoCentralGraph

/-! The graph subgroup S₀ supplies the literal inner action on the companion
prime component.  Its involution centralizers generate that component by
the dihedral fixed-generation theorem, retaining the ambient embeddings.
Source: Aschbacher–Smith 2.5.19, printed p.564. -/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

/-- Fixed generation for the actual index-two graph inside a Sylow subgroup
times a central involution.  No generation or faithful-action premise remains. -/
theorem prime_component_le_of_graph_involution_centralizers
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hpower : ∃ k, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (C : Subgroup G) (eC : C ≃* PSL(2,ZMod p)) (P : Sylow 2 C)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ centralizer (C : Set G)) (htnot : t ∉ C)
    (D : Subgroup ((P : Subgroup C).map C.subtype ⊔ zpowers t : Subgroup G))
    (hi : D.index = 2)
    (htD : (⟨t,mem_sup_right (mem_zpowers t)⟩ :
      ((P : Subgroup C).map C.subtype ⊔ zpowers t : Subgroup G)) ∉ D)
    (N : Subgroup G)
    (hfixed : ∀ j : G, j ∈ D.map ((P : Subgroup C).map C.subtype ⊔ zpowers t).subtype →
      orderOf j = 2 → C ⊓ centralizer ({j} : Set G) ≤ N) : C ≤ N := by
  let U := (P : Subgroup C).map C.subtype
  let W := U ⊔ zpowers t
  have hUC : U ≤ C := map_subtype_le _
  have htU : t ∈ centralizer (U : Set G) := (centralizer_le hUC) htC
  obtain ⟨eD,hdisp⟩ := index_two_graph_equiv U t ht htU (fun h => htnot (hUC h)) D hi htD
  let eU : P ≃* U := (P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  let Pm := P.mapSurjective (f := eC.toMonoidHom) eC.surjective
  let eP : P ≃* Pm := (P : Subgroup C).equivMapOfInjective eC.toMonoidHom eC.injective
  obtain ⟨k,hk⟩ := hpower
  obtain ⟨m,hm,⟨em⟩⟩ := Theory.PSL2.sylow_dihedral_of_adjacent_power hp hk Pm
  let e : D ≃* DihedralGroup (2 ^ m) := ((eD.trans eU.symm).trans eP).trans em
  let f₀ : D →* PSL(2,ZMod p) := eC.toMonoidHom.comp ((inclusion hUC).comp eD.toMonoidHom)
  let f : D →* MulAut PSL(2,ZMod p) := MulAut.conj.comp f₀
  have hf₀ : Function.Injective f₀ := eC.injective.comp
    ((inclusion_injective hUC).comp eD.injective)
  have hf : Function.Injective f := by
    have hi := MulAut.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot (ZMod p))
    exact hi.comp hf₀
  let g : PSL(2,ZMod p) →* G := C.subtype.comp eC.symm.toMonoidHom
  have hN : N.comap g = ⊤ := by
    apply Theory.PSL2.prime_dihedral_involution_fixed_generation hp ⟨k,hk⟩ hm e f hf
    intro d hd x hx
    let u : G := (eD d : U)
    let y : G := (eC.symm x : C)
    let j : G := ((d : W) : G)
    have hyC : y ∈ C := (eC.symm x).property
    have hux : f₀ d * x * (f₀ d)⁻¹ = x := (MulAut.mem_fixedSubgroup _ _).mp hx
    have huy : Commute u y := by
      have he := congrArg (fun q : PSL(2,ZMod p) => (eC.symm q : G)) hux
      have hu : eC.symm (f₀ d) = inclusion hUC (eD d) := eC.symm_apply_apply _
      have he' : u * y * u⁻¹ = y := by
        simpa only [map_mul,map_inv,hu,Subgroup.coe_mul,Subgroup.coe_inv,coe_inclusion,u,y] using he
      exact mul_inv_eq_iff_eq_mul.mp he'
    have hvC : j * u⁻¹ ∈ centralizer (C : Set G) :=
      (zpowers_le.mpr htC) (hdisp d)
    have hvy : Commute (j * u⁻¹) y := (hvC y hyC).symm
    have hjy : Commute j y := by
      have hh := hvy.mul_left huy
      simpa only [inv_mul_cancel_right] using hh
    have hjD : j ∈ D.map W.subtype := mem_map_of_mem W.subtype d.property
    have hj2 : orderOf j = 2 := by simpa only [j,Subgroup.orderOf_coe] using hd
    exact hfixed j hjD hj2 ⟨hyC,mem_centralizer_singleton_iff.mpr hjy.symm.eq⟩
  intro x hx
  have he : eC ⟨x,hx⟩ ∈ N.comap g := hN ▸ mem_top _
  change (eC.symm (eC ⟨x,hx⟩) : G) ∈ N at he
  simpa only [eC.symm_apply_apply] using he
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
