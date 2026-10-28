module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoBinarySource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MarkSource
public import Theory.GroupTheory.CentralInnerProjection
/-! # Original central component projection for the local-pair construction
In the normal-component case the original mark z has a central involutory
projection zK in the component Sylow. Its complementary factor t=zK⁻¹z
centralizes the whole source group H. This is precisely the marking used
in the elementary-four construction in 2.5.12; it does not need t nontrivial
or the stronger center-order conclusion of 2.5.11.
Source: Aschbacher--Smith, printed pp.557--558.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.normal_component_central_projection
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    ∃ t zK:G, H≤centralizer ({t}:Set G) ∧ z∈zpowers t⊔zpowers zK ∧
      orderOf zK=2 ∧ zK∈L⊓centerIn ((S:Subgroup H).map H.subtype) ∧
      t=zK⁻¹*z ∧ t∈twoCore H := by
  let Y:=(S:Subgroup H).map H.subtype
  let h:=c.localSetup hG structural115Input localC129Input_knownSimple
  have hc:=MathieuSourceSetup.component_center_eq_bot c hG hempty hgen
  obtain ⟨u,hu,huZ,ha,hC⟩:=MathieuSourceSetup.sylow_projection c hG localC129Input_knownSimple hempty
  have hzZ:z∈centerIn Y:=⟨h.mem_sylow,h.central⟩
  have hYL:Y≤normalizer (L:Set G):=(map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have huS:(u:G)∈centerIn Y:=inner_projection_central_of_centerless Y L hYL hc z hzZ u hu ha
  have hu2:u^2=1:=by
    apply MulAut.conj_injective_of_center_eq_bot hc
    rw [map_pow,map_one]
    exact h.action_sq (MulAut.conj u) ha
  have hu1:u≠1:=fun he=>huZ (he ▸ (center L).one_mem)
  have huo:orderOf (u:G)=2:=(Subgroup.orderOf_coe u).trans (orderOf_eq_prime hu2 hu1)
  let t:=(u:G)⁻¹*z
  have htZ:t∈centerIn Y:=(centerIn Y).mul_mem ((centerIn Y).inv_mem huS) hzZ
  have htL:t∈centralizer (L:Set G):=hC.2
  have htcore:t∈twoCore H:=by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact hC
  have hHt:H≤centralizer ({t}:Set G):=by
    rw [hgen]
    apply sup_le
    · intro a ha
      exact mem_centralizer_singleton_iff.mpr (htL a ha)
    · intro a ha
      exact mem_centralizer_singleton_iff.mpr (htZ.2 a ha)
  refine ⟨t,u,hHt,?_,huo,⟨u.property,huS⟩,rfl,htcore⟩
  have hh: (u:G)*t∈zpowers t⊔zpowers (u:G):=
    mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _))
  simpa only [t,mul_inv_cancel_left] using hh
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
