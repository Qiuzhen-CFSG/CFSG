module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterCoreBound
public import Theory.GroupTheory.CyclicKernelConjugateAbelian
/-!
# The outer generator and the impossible cyclic-four source core

An outer action element, together with K and the action kernel, generates
H. If that kernel had order four, its disjoint commuting crossing conjugate
would fill the residual fixer quotient, making C_S(R) abelian. The kernel
would then centralize both K and the outer generator, hence all of H.
The elementary abelian center of S rules out this cyclic-four subgroup.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_outer_generation
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) (y : H)
    (hy : MathieuSourceSetup.componentAction c y ∉ MulAut.innerSubgroup K) :
    H = (K ⊔ twoCore H) ⊔ zpowers (y : G) := by
  let α := MathieuSourceSetup.componentAction c
  change α y ∉ MulAut.innerSubgroup K at hy
  have hi : (MulAut.innerSubgroup K).index = 2 := by
    have hh := Matrix.PSL3Three.EightGeometry.inner_index_two
    rw [← MulAut.map_innerSubgroup_congr e,
      index_map_of_bijective (MulAut.congr e).bijective] at hh
    exact hh
  have hin (h : H) (hh : α h ∈ MulAut.innerSubgroup K) : (h : G) ∈ K ⊔ twoCore H := by
    obtain ⟨k,hk⟩ := hh
    let kH : H := ⟨k,c.component_le k.property⟩
    have hka : α kH = MulAut.conj k := by ext q; rfl
    have hker : kH⁻¹*h ∈ α.ker := by
      change α (kH⁻¹*h) = 1
      rw [map_mul,map_inv,hka,hk,inv_mul_cancel]
    rw [normal_component_source_action_ker c hG hempty hgen] at hker
    have hcore : (k : G)⁻¹*(h : G) ∈ twoCore H := hker
    have hm := (K ⊔ twoCore H).mul_mem (mem_sup_left k.property) (mem_sup_right hcore)
    simpa only [mul_inv_cancel_left] using hm
  apply le_antisymm
  · intro h hh
    let hH : H := ⟨h,hh⟩
    by_cases hm : α hH ∈ MulAut.innerSubgroup K
    · exact mem_sup_left (hin hH hm)
    · have ha : α (hH*y⁻¹) ∈ MulAut.innerSubgroup K := by
        rw [map_mul,map_inv,mul_mem_iff_of_index_two hi]
        simp only [inv_mem_iff,hm,hy]
      have hs := ((K ⊔ twoCore H) ⊔ zpowers (y : G)).mul_mem
        (mem_sup_left (hin _ ha)) (mem_sup_right (mem_zpowers (y : G)))
      change (h * (y : G)⁻¹) * (y : G) ∈ (K ⊔ twoCore H) ⊔ zpowers (y : G) at hs
      simpa only [inv_mul_cancel_right] using hs
  · exact sup_le (sup_le c.component_le (pCoreIn_le 2 H)) (zpowers_le.mpr y.property)
end CFSG.Quasithin.Chapter2.Section05

namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z x : G}

theorem linear_three_source_core_not_four
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) (k : K) (hk : orderOf k = 2)
    (hout : ¬ (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G))
    (hSN : (S : Subgroup H).map H.subtype ≤ normalizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x^2 ∈ (S : Subgroup H).map H.subtype)
    (hxR : x ∈ centralizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G)) :
    Nat.card (twoCore H) ≠ 4 := by
  intro hfour
  let Y := (S : Subgroup H).map H.subtype
  let B := (GLTwoThreeLocal.residual k).map K.subtype
  let C := Y ⊓ centralizer (B : Set G)
  let α := MathieuSourceSetup.componentAction c
  have hCH : C ≤ H := inf_le_left.trans (map_subtype_le _)
  have hCH' : C = H ⊓ centralizer (B : Set G) := le_antisymm
    (le_inf hCH inf_le_right) (le_inf
      (linear_three_residual_centralizer_le_source_sylow c hG hempty hgen e k hk hSN) inf_le_right)
  obtain ⟨y,hyS,hyR,hyo,hy4,hy2,hC⟩ := linear_three_outer_residual_lift c hG hempty hgen e k hk hout hSN
  have hNC : twoCore H ≤ C := by rw [hCH',hC]; exact le_sup_left
  have hyC : (y : G) ∈ C := ⟨mem_map_of_mem H.subtype hyS,hyR⟩
  obtain ⟨a,_,ha,_,hfix⟩ := linear_three_local_residual_fixer K e k hk
  change fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual k : Set K) = zpowers a at hfix
  have hf (q : C) : α (inclusion hCH q) ∈ zpowers a := by
    rw [← hfix]
    apply (mem_fixingSubgroup_iff _).mpr
    intro r hr
    apply Subtype.ext
    change (q : G) * (r : G) * (q : G)⁻¹ = (r : G)
    exact mul_inv_eq_iff_eq_mul.mpr (q.property.2 r (mem_map_of_mem K.subtype hr)).symm
  let f : C →* zpowers a := (α.comp (inclusion hCH)).codRestrict _ hf
  have hker : f.ker = (twoCore H).subgroupOf C := by
    ext q
    change f q = 1 ↔ _
    rw [Subtype.ext_iff]
    change α (inclusion hCH q) = 1 ↔ _
    rw [← MonoidHom.mem_ker,normal_component_source_action_ker c hG hempty hgen]
    rfl
  have hcyc := (linear_three_source_core_cyclic_dvd_four c hG hempty hgen e k hk hxT hxS hxN hx2 hxR).1
  let := hcyc
  have hxC : x ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hxN,(centralizer (B : Set G)).le_normalizer hxR⟩
  obtain ⟨hd,hcomm,_⟩ := generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2
  have hCC : C ≤ centralizer (C : Set G) := centralizes_self_of_disjoint_cyclic_kernel_conjugate
    C f (twoCore H) hNC hker (by rw [hfour,Nat.card_zpowers,ha]) x⁻¹
    ((normalizer (C : Set G)).inv_mem hxC) hd hcomm
  have hNK : twoCore H ≤ centralizer (K : Set G) := by
    intro n hn
    have hnh : n ∈ H := pCoreIn_le 2 H hn
    have hh : (⟨n,hnh⟩ : H) ∈ α.ker := by
      rw [normal_component_source_action_ker c hG hempty hgen]; exact hn
    change (⟨n,hnh⟩ : H) ∈
      (K.normalizerMonoidHom.comp (inclusion
        ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance))).ker at hh
    rw [normalizer_action_ker_comap] at hh
    exact hh
  have hHN : H ≤ centralizer (twoCore H : Set G) := by
    conv_lhs => rw [linear_three_source_outer_generation c hG hempty hgen e y hyo]
    exact sup_le (sup_le (le_centralizer_iff.mp hNK) (twoCore H).le_centralizer)
      (zpowers_le.mpr ((centralizer_le hNC) (hCC hyC)))
  have hNZ : twoCore H ≤ centerIn Y := le_inf (pCoreIn_le_sylow H S)
    (le_centralizer_iff.mp ((map_subtype_le _).trans hHN))
  let := hZ
  have hdiv := Monoid.exponent_dvd_of_monoidHom (inclusion hNZ) (inclusion_injective hNZ)
  rw [IsCyclic.exponent_eq_card,IsKleinFour.exponent_two,hfour] at hdiv
  norm_num at hdiv
end CFSG.Quasithin.Chapter2.Section05
