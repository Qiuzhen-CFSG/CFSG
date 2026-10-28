module

public import CFSG.Quasithin.Chapter13.Section07.PairDIntersections
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage
public import Theory.GroupTheory.SixImageCommutatorKernel

/-!
# The original commutator preimage in13.7.10(4)

The marked natural tensor identifies a translated subspace by displacement.
The actual internal conjugator carries both UH and the whole core factor,
so the coordinate criterion retains the original subgroups. The order-six
image then forces every element satisfying the commutator condition into
the core. This proves the criterion on the entire second span, including
a zero natural section, without an added kernel-placement premise.
Source: Aschbacher--Smith13.7.10(4), printed p.942.
-/

public section

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem pair_core_commutator_preimage
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let U:=Section08.Source.UH H V₃
    let E:=A⊓B
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    ∀z∈B⊓Q,(∀a∈A,⁅a,z⁆∈U⊔E) ↔ z∈conjugate U (g:G)⊔E := by
  dsimp only
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let U:=Section08.Source.UH H V₃
  let I:=A⊔B
  let S:=I.pCoreIn 2
  let E:=A⊓B
  let Q:=X.pCoreIn 2
  have hAI:A≤I:=le_sup_left
  have hBI:B≤I:=le_sup_right
  have hAX:A≤X:=(VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hBX:B≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact mul_mem (mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hIX:I≤X:=sup_le hAX hBX
  obtain ⟨hcore,_⟩:=pair_twoCore_quotient d h hU hV g hout
  change S=I⊓Q at hcore
  have hW:A⊓Q≤S:=hcore.ge.trans' (le_inf (inf_le_left.trans hAI) inf_le_right)
  have hY:B⊓Q≤S:=hcore.ge.trans' (le_inf (inf_le_left.trans hBI) inf_le_right)
  have hUQ:U≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  have hUA:U≤A:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUS:U≤S:=(le_inf hUA hUQ).trans hW
  obtain ⟨x,hxA,hxU,_⟩:=pair_internal_source_subgroups d h hU hV g hout
  have hxQ:(x:G)∈normalizer (Q:Set G):=
    (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
      (hIX x.property)
  have hYx:B⊓Q=(A⊓Q).conjBy (x:G) := by
    change B⊓Q=(A⊓Q).map (MulAut.conj (x:G)).toMonoidHom
    have heQ:Q.map (MulAut.conj (x:G)).toMonoidHom=Q:=mem_normalizer_iff_map_conj_eq.mp hxQ
    rw [map_inf _ _ _ (MulAut.conj (x:G)).injective,heQ]
    exact congrArg (·⊓Q) hxA
  obtain ⟨hN,hEA,e,σ,c,hcoord,hfinite,hcompl,⟨j,hj⟩,hmarks⟩:=pair_natural_quotient d h hU hV g hout
  let :=hN
  let :=hEA
  let π:I→*S₃:=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hk:π.ker=pCore 2 I:=(MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hcore':pCore 2 I=Q.subgroupOf I := by
    apply map_injective I.subtype_injective
    exact hcore.trans ((inf_comm I Q).trans (subgroupOf_map_subtype Q I).symm)
  have hcard:Nat.card ((A.subgroupOf I).map π)=2 := by
    rw [←relIndex_ker _ π,hk,hcore',relIndex_subgroupOf hAI]
    exact (nonabelian_core_indices d h hU hV).1
  obtain ⟨y,hy,_⟩:=(Nat.card_eq_two_iff' (1:(A.subgroupOf I).map π)).mp hcard
  obtain ⟨u,hu,heu⟩:=y.property
  have hu1:π u≠1:=by
    intro he
    exact hy (Subtype.ext (heu.symm.trans he))
  have huQ:(u:G)∉Q := by
    intro huQ
    have huk:u∈π.ker:=(hk.trans hcore').symm ▸ huQ
    exact hu1 huk
  have hu2:π u*π u=1 := by
    have hpow:(⟨π u,mem_map_of_mem π hu⟩:(A.subgroupOf I).map π)^2=1 := by
      simpa only [hcard] using (pow_card_eq_one' (x:=(⟨π u,mem_map_of_mem π hu⟩:(A.subgroupOf I).map π)))
    have he:(π u)^2=1:=congrArg Subtype.val hpow
    simpa only [pow_two] using he
  obtain ⟨hker,hrange,_⟩:=hmarks u hu (fun huW=>huQ huW.2)
  intro z hz
  have hzS:z∈S:=hY hz
  have hh:=c.natural_commutator_preimage σ π j hj A (A⊓Q) U hAI hW hUS u x hu hu1 hu2
    hcard hker hrange (hYx ▸ hcompl) ⟨z,hzS⟩ (hYx ▸ hz)
  change (∀a∈A,⁅a,z⁆∈U⊔E) ↔ z∈U.conjBy (x:G)⊔E at hh
  change conjugate U (g:G)=U.conjBy (x:G) at hxU
  rw [←hxU] at hh
  exact hh
theorem pair_commutator_forces_core
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let I:=A⊔B
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    ∀z∈B,(∀a∈A,⁅a,z⁆∈I.pCoreIn 2)→z∈Q := by
  dsimp only
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let A':=A.subgroupOf I
  let B':=B.subgroupOf I
  have hAI:A≤I:=le_sup_left
  have hBI:B≤I:=le_sup_right
  obtain ⟨hcore,⟨e⟩⟩:=pair_twoCore_quotient d h hU hV g hout
  have hcore':pCore 2 I=Q.subgroupOf I := by
    apply map_injective I.subtype_injective
    exact hcore.trans ((inf_comm I Q).trans (subgroupOf_map_subtype Q I).symm)
  let π:I→*S₃:=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hk:π.ker=pCore 2 I:=(MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hA:Nat.card (A'.map π)=2 := by
    rw [←relIndex_ker _ π,hk,hcore',relIndex_subgroupOf hAI]
    exact (nonabelian_core_indices d h hU hV).1
  obtain ⟨x,hx⟩:=pair_internal_conjugator d h hU hV g hout
  have hx':B'=A'.conjBy x := by
    apply map_injective I.subtype_injective
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI]
    exact hx
  have hB:Nat.card (B'.map π)=2 := by
    rw [hx',map_conjBy_hom]
    change Nat.card ((A'.map π).map (MulAut.conj (π x)).toMonoidHom)=2
    rw [card_map_of_injective (MulAut.conj (π x)).injective,hA]
  have hgen:A'⊔B'=⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI,
      ←MonoidHom.range_eq_map,range_subtype]
  have hAB:Nat.card ((A'⊔B').map π)=6 := by
    rw [hgen,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr
      (e.surjective.comp (QuotientGroup.mk'_surjective _)),card_top]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  intro z hz hcomm
  let zI:I:=⟨z,hBI hz⟩
  have hm:=mem_kernel_of_commutators_of_six_image π A' B' hA hB hAB zI hz
    (fun a ha=>by
      have hc:⁅a,zI⁆∈Q.subgroupOf I:=(hcore.le (hcomm a ha)).2
      exact (hk.trans hcore').symm ▸ hc)
  exact (show zI∈Q.subgroupOf I from (hk.trans hcore') ▸ hm)

 theorem pair_commutator_preimage
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let U:=Section08.Source.UH H V₃
    let E:=A⊓B
    ∀z∈B,(∀a∈A,⁅a,z⁆∈U⊔E) ↔ z∈conjugate U (g:G)⊔E := by
  dsimp only
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let U:=Section08.Source.UH H V₃
  let I:=A⊔B
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let E:=A⊓B
  have hUA:U≤A:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUQ:U≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  obtain ⟨hcore,_⟩:=pair_twoCore_quotient d h hU hV g hout
  change I.pCoreIn 2=I⊓Q at hcore
  have hUS:U≤I.pCoreIn 2:=hcore.ge.trans' (le_inf (hUA.trans le_sup_left) hUQ)
  have hES:E≤I.pCoreIn 2:=(pair_intersection_layer d h hU g hout).2.1
  have hUE:U⊔E≤I.pCoreIn 2:=sup_le hUS hES
  have hgQ:conjugate Q (g:G)=Q:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (Q:Set G)).inv_mem
      (((L⊔(T:Subgroup G):Subgroup G).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L⊔(T:Subgroup G):Subgroup G)))) g.property))
  have hUgQ:conjugate U (g:G)≤Q:=(map_mono hUQ).trans hgQ.le
  intro z hz
  constructor
  · intro hcomm
    have hzQ:=pair_commutator_forces_core d h hU hV g hout z hz
      (fun a ha=>hUE (hcomm a ha))
    exact (pair_core_commutator_preimage d h hU hV g hout z ⟨hz,hzQ⟩).mp hcomm
  · intro hzU
    have hzQ:z∈Q:=(sup_le hUgQ (hES.trans (hcore.le.trans inf_le_right))) hzU
    exact (pair_core_commutator_preimage d h hU hV g hout z ⟨hz,hzQ⟩).mpr hzU

end CFSG.Quasithin.Chapter13.Section07
