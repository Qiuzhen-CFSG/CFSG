module

public import CFSG.Quasithin.Chapter13.Section07.PairQuotient
public import CFSG.Quasithin.ChapterF.Section09.F7Specialization
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Theory.GroupTheory.SymmetricThreeConjugateKernel


/-!
# The source core factors and their internal conjugator

The full preimage of the transposition normalizer fixes the original point,
so F.9 places it in H and makes it normalize VH. Sylow conjugacy in the
proved order-six image therefore lifts to a conjugator inside I carrying
one entire VH subgroup to the other. The genuine S₃-kernel theorem now
gives both original core intersections as the factors of O₂(I).

The final consumer constructs g∈L and proves13.7.10(2), including the
literal product identity. It does not assume g belongs to I; that stronger
condition is unnecessary and need not hold for the original choice.
Source: Aschbacher–Smith,13.7.10(2), printed pp.941–942.
-/

@[expose] public section

open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction ChapterF.Section09.Setup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The source point-normalizer control lifts image conjugacy to an actual
conjugator inside I, preserving both full original VH subgroups. -/
theorem pair_internal_conjugator
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃) :
    ∃ x:(Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g:G):Subgroup G),
      conjugate (Section08.Source.VH H V) (g:G)=(Section08.Source.VH H V).conjBy (x:G) := by
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let I:=A⊔conjugate A (g:G)
  have hAX:A≤X:=(VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hBX:conjugate A (g:G)≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact mul_mem (mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hIX:I≤X:=sup_le hAX hBX
  let U:=A.subgroupOf X
  let P:=U⊔U.conjBy g⁻¹
  have hPm:P.map X.subtype=I := by
    rw [Subgroup.map_sup,map_conjBy_hom,map_subgroupOf_eq_of_le hAX]
    rfl
  have hP:P=I.subgroupOf X := map_injective X.subtype_injective
    (hPm.trans (map_subgroupOf_eq_of_le hIX).symm)
  obtain ⟨e⟩:=pair_image_symmetricThree d h hU hV g hout
  have hcard:Nat.card (P.map (permutation d))=6 := by
    rw [hP,Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  obtain ⟨t,ht,htA,_⟩:=nonabelian_transposition_images d h hU hV
  have hA:Nat.card (U.map (permutation d))=2 := by
    rw [htA,Nat.card_zpowers,ht.orderOf]
  have htf:∀w∈form.orthogonal (image d V₁),naturalRepresentation (Fin 6) t w=w := by
    intro w hw
    rw [←seed_perpendicular d] at hw
    obtain ⟨v,hv,rfl⟩:=(mem_image d V₃ _).mp hw
    have htm:t∈U.map (permutation d):=htA.symm ▸ mem_zpowers t
    obtain ⟨a,ha,he⟩:=htm
    rw [←he,←conjugation d a v]
    apply congrArg (fun v:V=>(d.coordinate v).toAdd)
    apply Subtype.ext
    have hc: a.val∈centralizer (V₃:Set G):=
      (centralizer_le (le_conjugateSpanBy V₃ H)) ((VH_centralizes_UH d h hU) ha).2
    change a.val*v.val*a.val⁻¹=v.val
    rw [←hc v.val hv,mul_inv_cancel_right]
  have hn:(normalizer (U.map (permutation d):Set (Equiv.Perm (Fin 6)))).comap (permutation d)≤
      normalizer (U:Set X) := by
    intro y hy
    have hc:permutation d y∈centralizer (zpowers t:Set (Equiv.Perm (Fin 6))) := by
      rw [htA] at hy
      exact normalizer_le_centralizer_of_card_two (zpowers t)
        (by rw [Nat.card_zpowers,ht.orderOf]) hy
    have htn:t≠1:=by
      intro he
      have hh:=ht.orderOf
      rw [he,orderOf_one] at hh
      contradiction
    have hpoint:=Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair.centralizer_stabilizes_line
      (image d V₁) (image_dim d V₁ (h.point_lt.le.trans h.plus_le) 1 d.line_card)
      t (permutation d y) htn htf (hc t (mem_zpowers t))
    have hyN:y.val∈normalizer (V₁:Set G):=(permutation_stabilizes_iff d V₁
      (h.point_lt.le.trans h.plus_le) y).mp ((mem_stabilizer_iff_map _ _).mpr hpoint)
    have hyH:y.val∈H:=h.local_le (h.normalizer_point_LT_eq ▸ ⟨y.property,hyN⟩)
    exact (le_normalizer_comap X.subtype)
      (le_normalizer_conjugateSpanBy V H hyH)
  obtain ⟨x,hx⟩:=exists_internal_conjugator_of_six_image (permutation d) U g⁻¹ hcard hA hn
  have hxI:((x:X):G)∈I:=hPm ▸ mem_map_of_mem X.subtype x.property
  refine ⟨⟨(x:X),hxI⟩,?_⟩
  have he:=congrArg (Subgroup.map X.subtype) hx
  rw [map_conjBy_hom,map_conjBy_hom,map_subgroupOf_eq_of_le hAX] at he
  exact he

/-- The exact kernel factors of13.7.10(2), now using an internal source conjugator. -/
theorem pair_twoCore_factorization
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    (A⊔B).pCoreIn 2=(A⊓Q)⊔(B⊓Q) := by
  dsimp only
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let Q:=X.pCoreIn 2
  let U:=A.subgroupOf I
  have hAI:A≤I:=le_sup_left
  have hAX:A≤X:=(VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hBX:B≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact mul_mem (mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hIX:I≤X:=sup_le hAX hBX
  obtain ⟨hc,⟨e⟩⟩:=pair_twoCore_quotient d h hU hV g hout
  have hcore:pCore 2 I=Q.subgroupOf I := by
    apply map_injective I.subtype_injective
    exact hc.trans ((inf_comm I Q).trans (subgroupOf_map_subtype Q I).symm)
  let f:I→*Equiv.Perm (Fin 3):=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hf:Function.Surjective f:=e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk:f.ker=pCore 2 I:=(MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hkp:IsPGroup 2 f.ker:=hk.symm ▸ pCore_isPGroup
  have hQT:Q≤(T:Subgroup G):=h.sylow_centralizer.symm.le.trans inf_le_left
  have hn:f.ker≤normalizer (U:Set I) := by
    intro z hz
    have hzQ':z∈Q.subgroupOf I := (hk.trans hcore) ▸ hz
    have hzQ:z.val∈Q:=hzQ'
    exact (le_normalizer_comap I.subtype)
      (le_normalizer_conjugateSpanBy V H (h.T_le_H (hQT hzQ)))
  have hcard:Nat.card (U.map f)=2 := by
    rw [←relIndex_ker U f,hk,hcore,relIndex_subgroupOf hAI]
    exact (nonabelian_core_indices d h hU hV).1
  obtain ⟨x,hx⟩:=pair_internal_conjugator d h hU hV g hout
  have hgen:U⊔U.conjBy x=⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_conjBy_hom,map_subgroupOf_eq_of_le hAI,
      ←MonoidHom.range_eq_map,range_subtype]
    exact congrArg (fun C:Subgroup G=>A⊔C) hx.symm
  have he:=symmetric_three_kernel_eq_conjugate_intersections f hf hkp U hn hcard x hgen
  have hem:=congrArg (Subgroup.map I.subtype) he
  rw [hk] at hem
  rw [Subgroup.map_sup,map_conjBy_hom,map_inf _ _ _ I.subtype_injective,
    map_subgroupOf_eq_of_le hAI] at hem
  change I.pCoreIn 2=(A⊓I.pCoreIn 2)⊔(A⊓I.pCoreIn 2).conjBy (x:G) at hem
  have hAQ:A⊓I.pCoreIn 2=A⊓Q := by
    rw [hc,←inf_assoc,inf_eq_left.mpr hAI]
  rw [hAQ] at hem
  have hxQ:x.val∈normalizer (Q:Set G):=
    (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
      (hIX x.property)
  have hconj:(A⊓Q).conjBy (x:G)=B⊓Q := by
    change (A⊓Q).map (MulAut.conj (x:G)).toMonoidHom=B⊓Q
    have heQ:Q.map (MulAut.conj (x:G)).toMonoidHom=Q :=
      mem_normalizer_iff_map_conj_eq.mp hxQ
    rw [map_inf _ _ _ (MulAut.conj (x:G)).injective,heQ]
    change A.conjBy (x:G)⊓Q=B⊓Q
    rw [←hx]
  exact hem.trans (congrArg ((A⊓Q)⊔·) hconj)

/-- The kernel factorization is also the literal product of the two subgroups. -/
theorem pair_twoCore_product
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    ((A⊔B).pCoreIn 2:Set G)=(A⊓Q:Set G)*(B⊓Q:Set G) := by
  dsimp only
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  have hQT:Q≤(T:Subgroup G):=h.sylow_centralizer.symm.le.trans inf_le_left
  have hQA:Q≤normalizer (A:Set G):=hQT.trans (h.T_le_H.trans (le_normalizer_conjugateSpanBy V H))
  have hn:B⊓Q≤normalizer (A⊓Q:Set G):=
    (le_inf (inf_le_right.trans hQA) (inf_le_right.trans Q.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [pair_twoCore_factorization d h hU hV g hout]
  exact coe_mul_of_right_le_normalizer_left (A⊓Q) (B⊓Q) hn

/-- The complete original13.7.10(2) for a source-constructed g, preserving the
actual quotient, both factors, and their product. -/
theorem exists_source_pair_core
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G))
        (inclusion le_sup_left g))^2=1 ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let A:=Section08.Source.VH H V
      let B:=conjugate A (g:G)
      let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      (A⊔B).pCoreIn 2=(A⊓Q)⊔(B⊓Q) ∧
      ((A⊔B).pCoreIn 2:Set G)=(A⊓Q:Set G)*(B⊓Q:Set G) ∧
      Nonempty (((A⊔B:Subgroup G)⧸pCore 2 (A⊔B:Subgroup G))≃*Equiv.Perm (Fin 3)) := by
  obtain ⟨g,hs,hout,_,he⟩:=exists_pair_twoCore_quotient d h hU hV
  exact ⟨g,hs,hout,pair_twoCore_factorization d h hU hV (inclusion le_sup_left g) hout,
    pair_twoCore_product d h hU hV (inclusion le_sup_left g) hout,he⟩
end CFSG.Quasithin.Chapter13.Section07
