module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterCentralizer
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterFusionCrossing
/-!
# Selecting the outer involution from the original crossing

The original source marks identify k=z and O₂(H)=⟨t⟩. The adjusted crossing
centralizes the local residual R. Its displacement on some involution a
of the selected four escapes ⟨t,z⟩; the residual centralizer calculation
therefore forces aˣ to induce an outer automorphism of K. Both crossing
marks and the full centralizer C_G(t)=H retain the same selected t.
Source: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_fusion_selection
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S:Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U≤(S:Subgroup H).map H.subtype)
    (eK : K≃*Matrix.PSL3Three.PSL) :
    z∈K ∧ ∃ t a x : G, orderOf t=2 ∧ t∈twoCore H ∧
      t∈centerIn ((S:Subgroup H).map H.subtype) ∧ twoCore H=zpowers t ∧
      centralizer ({t}:Set G)=H ∧ ¬IsConj t z ∧
      a∈K ∧ orderOf a=2 ∧ x⁻¹*t*x=t*z ∧
      ∃ f : H, (f:G)=x⁻¹*a*x ∧ orderOf f=2 ∧
      MathieuSourceSetup.componentAction c f ∉ MulAut.innerSubgroup K := by
  let Y := (S:Subgroup H).map H.subtype
  obtain ⟨t,k,ht,hk,htC,hcore,hline,_,hspanK,hZ,_⟩ :=
    MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t∈centerIn Y := (show t∈centerIn Y⊓twoCore H from hcore ▸ mem_zpowers t).1
  have hKY : Y≤normalizer (K:Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have horbit : componentOrbit K Y=K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKY) (le_componentOrbit _ _)
  have hkZK : k∈centerIn Y⊓K := by rw [horbit] at hline; exact hline ▸ mem_zpowers k
  let zK : K := ⟨k,hkZK.2⟩
  have hzK : orderOf zK=2 := by simpa only [zK,Subgroup.orderOf_mk] using hk
  have hcore' := linear_three_source_core_eq_central_involution c hG hempty hgen hb hp hUS
    eK t ht htC htZ hZ zK hzK hkZK.1 hspanK
  have hkz := (linear_three_source_marked_split c hG hempty hgen hb hp hUS
    eK t ht htC htZ hZ zK hzK hkZK.1 hspanK).1
  have hzK' : z∈K := hkz ▸ zK.property
  let R := (GLTwoThreeLocal.residual zK).map K.subtype
  have hres := (MathieuSourceSetup.small_component_centralizer_residual c hG hempty hgen
    (Or.inl ⟨eK⟩) t ht htC htZ).2.2
  have hN := local_residual_normalized_by_sylow_normalizer K Y (Or.inl ⟨eK⟩)
    zK hzK t hspanK hres
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem Y c.T c.T.isPGroup' c.sylow_lt
  obtain ⟨x,hxT,hxS,hxN,hxR⟩ := local_residual_crossing_adjustment c (Or.inl ⟨eK⟩)
    zK hzK hkZK.1 hxT hxS hxN (hN hxN)
  obtain ⟨E,hES,hE,hL,_,_,_,hCE⟩ := largest_pair_four_structure_of_source c hG hempty hgen hb hp hUS
  let := hE
  have hEY := hES.trans inf_le_left
  have hEK := hES.trans inf_le_right
  have hzEcent : z∈centralizer (E:Set G) := by
    have hzT : z∈centerIn (c.T:Subgroup G) := by simpa only [centerIn_eq_map_center] using c.mem_center
    exact fun a ha => hzT.2 a (c.sylow_lt.le (hEY ha))
  have hzE : z∈E := hCE ▸ (show z∈K⊓centralizer (E:Set G) from ⟨hzK',hzEcent⟩)
  obtain ⟨hRK,hRz,hzR⟩ := local_residual_ambient_facts K (Or.inl ⟨eK⟩) zK hzK
  rw [hkz] at hRz hzR
  have hER : E≤normalizer (R:Set G) := fun a ha =>
    hzR ⟨hEK ha,mem_centralizer_singleton_iff.mpr (hzEcent a ha)⟩
  have htH := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  have htx := (MathieuSourceSetup.source_crossing_on_center c hgen t ht htC htZ hZ).2 x hxT hxN hxS
  obtain ⟨a,haE,haC,haout⟩ := source_crossing_displacement_outside_center c hG hp hUS
    t htZ.1 htH hEY hL hzE hER hxT hxS hxN hxR htx
  have ha2 : a^2=1 := by
    have hh := Monoid.pow_exponent_eq_one (⟨a,haE⟩:E)
    rw [IsKleinFour.exponent_two] at hh
    exact congrArg Subtype.val hh
  have hane : a≠1 := by
    intro he
    apply haout
    simp only [he,inv_one,mul_one,inv_mul_cancel]
    exact one_mem _
  have hao : orderOf a=2 := orderOf_eq_prime ha2 hane
  have hfa : x⁻¹*a*x∈Y := by
    simpa only [SetLike.mem_coe,inv_inv] using ((normalizer (Y:Set G)).inv_mem hxN a).mp (hEY haE)
  let f : H := ⟨x⁻¹*a*x,map_subtype_le _ hfa⟩
  have hf2 : orderOf f=2 := by
    rw [Subgroup.orderOf_mk]
    simpa only [MulAut.conj_apply,inv_inv] using ((MulAut.conj x⁻¹).orderOf_eq a).trans hao
  let α := MathieuSourceSetup.componentAction c
  have hker : α.ker=(zpowers t).subgroupOf H := by
    rw [normal_component_source_action_ker c hG hempty hgen,hcore']
  have hfo : α f∉MulAut.innerSubgroup K := by
    intro hf
    let aH : H := ⟨a,c.component_le (hEK haE)⟩
    let aK : K := ⟨a,hEK haE⟩
    have haα : α aH=MulAut.conj aK := by ext r; rfl
    have hwa : α (aH⁻¹*f)∈MulAut.innerSubgroup K := by
      rw [map_mul,map_inv,haα]
      exact mul_mem (inv_mem (show MulAut.conj aK∈MulAut.innerSubgroup K from ⟨aK,rfl⟩)) hf
    obtain ⟨b,hb⟩ := hwa
    let bH : H := ⟨b,c.component_le b.property⟩
    have hbα : α bH=MulAut.conj b := by ext r; rfl
    have hd : (aH⁻¹*f)*bH⁻¹∈α.ker := by
      change α ((aH⁻¹*f)*bH⁻¹)=1
      rw [map_mul,map_inv,hbα,← hb,mul_inv_cancel]
    rw [hker] at hd
    have hdG : (a⁻¹*(x⁻¹*a*x))*(b:G)⁻¹∈zpowers t := hd
    have htR : zpowers t≤centralizer (R:Set G) := by
      apply zpowers_le.mpr
      intro r hr
      exact (mem_centralizer_singleton_iff.mp (htH (c.component_le (hRK hr))))
    have hbC : (b:G)∈centralizer (R:Set G) := by
      have hh := (centralizer (R:Set G)).mul_mem
        ((centralizer (R:Set G)).inv_mem (htR hdG)) haC.2
      convert hh using 1
      group
    have hbz : (b:G)∈zpowers z := hRz ▸ (show (b:G)∈K⊓centralizer (R:Set G) from ⟨b.property,hbC⟩)
    have hh := (zpowers t⊔zpowers z).mul_mem (mem_sup_left hdG) (mem_sup_right hbz)
    apply haout
    simpa only [inv_mul_cancel_right] using hh
  exact ⟨hzK',t,a,x,ht,htC,htZ,hcore',
    linear_three_source_centralizer_eq c hG hempty hgen eK hzK' t ht htC htZ hcore',
    (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).2.2.2.2,
    hEK haE,hao,htx,f,rfl,hf2,hfo⟩
end CFSG.Quasithin.Chapter2.Section05
