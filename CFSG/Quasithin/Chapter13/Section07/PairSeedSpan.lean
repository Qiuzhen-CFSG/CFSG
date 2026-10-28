module

public import CFSG.Quasithin.Chapter13.Section07.PairCommutatorPreimage

/-!
# The literal seed-span product

The displacement preimage makes UH UH^g ZI invariant under the first span;
the source square condition exchanges the two spans and their seeds. The
internal marked conjugator puts UH^g in the actual I-span of UH. Finally,
the abelian natural section makes the generated join the literal ordered
product, proving the first identity of13.7.10(4).
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

theorem pair_seed_span
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let U:=Section08.Source.UH H V₃
    let E:=A⊓B
    conjugateSpanBy U (A⊔B)⊔E=U⊔conjugate U (g:G)⊔E := by
  dsimp only
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let U:=Section08.Source.UH H V₃
  let Ug:=conjugate U (g:G)
  let I:=A⊔B
  let E:=A⊓B
  let K:=U⊔Ug⊔E
  have hUA:U≤A:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUgB:Ug≤B:=map_mono hUA
  have hnE:I≤normalizer (E:Set G):=(pair_intersection_layer d h hU g hout).2.2.1
  have hAH:A≤H:=(VH_le_core d h hU).trans (pCoreIn_le 2 H)
  have hANU:A≤normalizer (U:Set G):=hAH.trans (le_normalizer_conjugateSpanBy V₃ H)
  have hANE:A≤normalizer (E:Set G):=le_sup_left.trans hnE
  have hcomm:∀a∈A,∀z∈Ug,⁅a,z⁆∈U⊔E := by
    intro a ha z hz
    exact (pair_commutator_preimage d h hU hV g hout z (hUgB hz)).mpr (mem_sup_left hz) a ha
  have hAK:A≤normalizer (K:Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha z hz
    have hm:K.map (MulAut.conj a).toMonoidHom≤K := by
      change ((U⊔Ug)⊔E).map _≤K
      rw [Subgroup.map_sup,Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · have he:U.map (MulAut.conj a).toMonoidHom=U:=mem_normalizer_iff_map_conj_eq.mp (hANU ha)
        rw [he]
        exact le_sup_left.trans le_sup_left
      · rintro _ ⟨u,hu,rfl⟩
        have hUEK:U⊔E≤K:=sup_le (le_sup_left.trans le_sup_left) le_sup_right
        have hh:⁅a,u⁆∈K:=hUEK (hcomm a ha u hu)
        have hm:=K.mul_mem hh (show u∈K from mem_sup_left (mem_sup_right hu))
        simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,commutatorElement_def,
          mul_assoc,inv_mul_cancel,mul_one] using hm
      · have he:E.map (MulAut.conj a).toMonoidHom=E:=mem_normalizer_iff_map_conj_eq.mp (hANE ha)
        rw [he]
        exact le_sup_right
    exact hm (mem_map_of_mem _ hz)
  have htwiceU:conjugate Ug (g:G)=U:=h.conjugate_twice_eq_of_square
    (le_normalizer_conjugateSpanBy V₃ H) (h.square_mem_local_of_core_quotient_square g hs)
  have htwiceA:conjugate B (g:G)=A:=h.conjugate_twice_eq_of_square
    (le_normalizer_conjugateSpanBy V H) (h.square_mem_local_of_core_quotient_square g hs)
  have hee:conjugate E (g:G)=E := by
    change (A⊓B).map (MulAut.conj (g:G)⁻¹).toMonoidHom=E
    rw [map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective]
    change B⊓conjugate B (g:G)=A⊓B
    rw [htwiceA,inf_comm]
  have hkk:conjugate K (g:G)=K := by
    change ((U⊔Ug)⊔E).map (MulAut.conj (g:G)⁻¹).toMonoidHom=K
    rw [Subgroup.map_sup,Subgroup.map_sup]
    change (Ug⊔conjugate Ug (g:G))⊔conjugate E (g:G)=(U⊔Ug)⊔E
    rw [htwiceU,hee,sup_comm Ug U]
  have hBK:B≤normalizer (K:Set G) := by
    have hm:conjugate A (g:G)≤conjugate (normalizer (K:Set G)) (g:G):=map_mono hAK
    have hn:conjugate (normalizer (K:Set G)) (g:G)≤normalizer (conjugate K (g:G):Set G):=
      le_normalizer_map (H:=K) (MulAut.conj (g:G)⁻¹).toMonoidHom
    rw [hkk] at hn
    exact hm.trans hn
  have hIK:I≤normalizer (K:Set G):=sup_le hAK hBK
  apply le_antisymm
  · exact sup_le (conjugateSpanBy_le (le_sup_left.trans le_sup_left) hIK) le_sup_right
  · have hUspan:U≤conjugateSpanBy U I:=le_conjugateSpanBy U I
    obtain ⟨x,_,hxU,_⟩:=pair_internal_source_subgroups d h hU hV g hout
    have hUgspan:Ug≤conjugateSpanBy U I := by
      change conjugate U (g:G)≤conjugateSpanBy U I
      rw [hxU]
      rintro _ ⟨u,hu,rfl⟩
      exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy U I x.property) u).mp (hUspan hu)
    exact sup_le (sup_le (hUspan.trans le_sup_left) (hUgspan.trans le_sup_left)) le_sup_right

/-- The source span is the literal ordered product, not only its generated join. -/
theorem pair_seed_span_product
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let U:=Section08.Source.UH H V₃
    let E:=A⊓B
    ((conjugateSpanBy U (A⊔B)⊔E:Subgroup G):Set G)=
      (U:Set G)*(conjugate U (g:G):Set G)*(E:Set G) := by
  dsimp only
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let U:=Section08.Source.UH H V₃
  let Ug:=conjugate U (g:G)
  let I:=A⊔B
  let S:=I.pCoreIn 2
  let E:=A⊓B
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  have hUA:U≤A:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUI:U≤I:=hUA.trans le_sup_left
  have hUQ:U≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  obtain ⟨hcore,_⟩:=pair_twoCore_quotient d h hU hV g hout
  change S=I⊓Q at hcore
  have hUS:U≤S:=hcore.ge.trans' (le_inf hUI hUQ)
  obtain ⟨x,_,hxU,_⟩:=pair_internal_source_subgroups d h hU hV g hout
  obtain ⟨hN,hEA,e,σ,c,_⟩:=pair_natural_quotient d h hU hV g hout
  have hUgS:Ug≤S := by
    change conjugate U (g:G)≤S
    rw [hxU]
    rintro _ ⟨u,hu,rfl⟩
    exact (mem_normalizer_iff.mp (c.normalized x.property) u).mp (hUS hu)
  have hn:S≤normalizer ((U⊔E:Subgroup G):Set G):=c.normalizes_join_kernel U hUS
  have hnE:I≤normalizer (E:Set G):=(pair_intersection_layer d h hU g hout).2.2.1
  have hUgI:Ug≤I:=hUgS.trans (pCoreIn_le 2 I)
  have hjoin:U⊔Ug⊔E=(U⊔E)⊔Ug:=by ac_rfl
  rw [pair_seed_span d h hU hV g hs hout]
  change ((U⊔Ug⊔E:Subgroup G):Set G)=(U:Set G)*(Ug:Set G)*(E:Set G)
  rw [hjoin,coe_mul_of_right_le_normalizer_left (U⊔E) Ug (hUgS.trans hn),
    coe_mul_of_left_le_normalizer_right U E (hUI.trans hnE),mul_assoc,
    ←set_mul_normalizer_comm (Ug:Set G) E (hUgI.trans hnE),←mul_assoc]


end CFSG.Quasithin.Chapter13.Section07
