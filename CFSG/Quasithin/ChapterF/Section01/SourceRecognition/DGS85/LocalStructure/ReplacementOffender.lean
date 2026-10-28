module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementModule
public import Glauberman.ThompsonPair
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# An escaping quadratic actor on the literal replacement module

Faithfulness rules out characteristic subgroups of Q_delta normal in the
neighboring endpoint. If its ordinary all-abelian Thompson subgroup lay
in Q_lambda, it would equal the Thompson subgroup of the normal core
intersection, a contradiction. This escape is independent of a quotient
model or a Sylow assertion about X.

In both neighboring-center cases, V=<Z_delta^X> lies in the elementary center of that
intersection. Thompson replacement, inside the finite neighboring endpoint,
therefore supplies a maximum-order abelian A in Q_delta outside Q_lambda,
with [V,A,A]=1 and |V:C_V(A)| <= |A:A intersect Q_lambda|. It also escapes
O_2(X). Every subgroup and index is transported back to the original ambient
group, which may be infinite. No faithful catalogue marking or corrected
5.12 Sylow-generation conclusion is assumed or asserted.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121; the Thompson
replacement argument formalized in Glauberman.QuadraticOffenderSelection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem borel_le (h : LocallyRankOneTriple P B) (i : Fin 2) : B ≤ P i :=
  le_sup_right.trans (Classical.choice (h.local_data i)).supplement.le

private theorem noCharacteristicNormal_neighbor (h : LocallyRankOneTriple P B) (i : Fin 2) :
    NoCharacteristicNormal (((P i).pCoreIn 2).subgroupOf (P (other i))) := by
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _)
  let A := ((P i).pCoreIn 2).subgroupOf (P (other i))
  let e : A ≃* (P i).pCoreIn 2 := subgroupOfEquivOfLe hAP
  intro K hK hnK
  let := hK
  let D := K.map e.toMonoidHom
  let : D.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let a' : MulAut A := (e.trans a).trans e.symm
    exact ⟨a' y,characteristic_iff_le_comap.mp hK a' hy,e.apply_symm_apply _⟩
  have hm : D.map ((P i).pCoreIn 2).subtype =
      (K.map A.subtype).map (P (other i)).subtype := by
    rw [map_map,map_map]
    rfl
  have hnD : P (other i) ≤ normalizer (D.map ((P i).pCoreIn 2).subtype : Set G) := by
    rw [hm]
    apply le_normalizer_iff.mpr
    intro g hg z hz
    obtain ⟨z',hz',rfl⟩ := hz
    refine mem_map.mpr ⟨(⟨g,hg⟩ : P (other i)) * z' * (⟨g,hg⟩ : P (other i))⁻¹,
      hnK.conj_mem z' hz' ⟨g,hg⟩,?_⟩
    simp only [map_mul,map_inv]
    rfl
  have hD := characteristic_core_eq_bot_of_cover h i (P (other i))
    (sup_eq_left.mpr (borel_le h _)) D hnD
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hD

private theorem thompson_escape_internal (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    ¬ thompsonSubgroup (((P i).pCoreIn 2).subgroupOf (P (other i))) ≤
      (((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2).subgroupOf (P (other i))) := by
  let := (Classical.choice (h.local_data (other i))).finite_P
  let R := P (other i)
  let A := ((P i).pCoreIn 2).subgroupOf R
  let N := ((P i).pCoreIn 2 ⊓ R.pCoreIn 2).subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hAP : (P i).pCoreIn 2 ≤ R :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _)
  have hAne : A ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map R.subtype) he
    rw [map_subgroupOf_eq_of_le hAP,Subgroup.map_bot] at hh
    exact source_core_ne_bot (Classical.choice (h.local_data i)) hh
  exact Glauberman.allAbelianThompson_not_le_normal A N (fun _ hx => hx.1) hAne
    (noCharacteristicNormal_neighbor h i)

/-- The ordinary all-abelian Thompson subgroup escapes the adjacent core,
before identifying any Sylow of the closure or selecting a quotient model. -/
theorem source_core_thompson_escape (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    ¬ thompsonSubgroup ((P i).pCoreIn 2) ≤ (P (other i)).pCoreIn 2 := by
  let := (Classical.choice (h.local_data i)).finite_P
  let : Finite ((P i).pCoreIn 2) := Finite.of_injective
    (inclusion (pCoreIn_le 2 (P i))) (inclusion_injective _)
  intro hc
  apply thompson_escape_internal h i hn
  intro x hx
  refine ⟨show (x : G) ∈ (P i).pCoreIn 2 from
    thompsonSubgroup_le (((P i).pCoreIn 2).subgroupOf (P (other i))) hx,?_⟩
  have hm := mem_map_of_mem (P (other i)).subtype hx
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _)
  have he : (thompsonSubgroup (((P i).pCoreIn 2).subgroupOf (P (other i)))).map
      (P (other i)).subtype = thompsonSubgroup ((P i).pCoreIn 2) := by
    rw [←thompsonSubgroup_top_map_subtype, map_map]
    let e := subgroupOfEquivOfLe hAP
    have hmap := thompsonSubgroup_top_map_mulEquiv e
    have hh := congrArg (Subgroup.map ((P i).pCoreIn 2).subtype) hmap
    rw [map_map,thompsonSubgroup_top_map_subtype] at hh
    exact hh
  exact hc (he ▸ hm)

/-- Thompson replacement on the literal V=<Z_delta^X> gives a maximum
abelian actor escaping both neighboring and closure cores, with the exact
quadratic identity and original centralizer index bound. -/
theorem source_replacement_quadratic_offender_of_inter_normal (h : LocallyRankOneTriple P B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
      ¬ A ≤ (P (other i)).pCoreIn 2 ∧ ¬ A ≤ X.pCoreIn 2 ∧
      ⁅⁅V,A⁆,A⁆ = ⊥ ∧ (V ⊓ centralizer (A : Set G)).relIndex V ≤
        ((P (other i)).pCoreIn 2).relIndex A := by
  let := (Classical.choice (h.local_data (other i))).finite_P
  let R := P (other i)
  let Q := (P i).pCoreIn 2
  let X := conjugateSpanBy Q R
  let V := conjugateSpanBy (sylowCenterSpan (P i)) X
  let N := Q ⊓ R.pCoreIn 2
  have hQP : Q ≤ R := (source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _)
  have hVN : V ≤ N := (source_replacement_span_le_inter_omega_of_inter_normal h i hn).trans (map_subtype_le _)
  have hVR : V ≤ R := (hVN.trans inf_le_left).trans hQP
  have hNR : N ≤ R := inf_le_right.trans (pCoreIn_le 2 R)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (source_replacement_span_le_inter_omega_of_inter_normal h i hn)
  let Vi := V.subgroupOf R
  let Qi := Q.subgroupOf R
  let Ni := N.subgroupOf R
  let : IsElementaryAbelian 2 Vi := IsElementaryAbelian.subgroupOf hVR
  have hViNi : Vi ≤ Ni := fun _ hx => hVN hx
  have hViQi : Vi ≤ Qi := fun _ hx => (hVN hx).1
  have hnVi : Qi ≤ normalizer (Vi : Set R) := by
    intro x hx
    exact le_normalizer_comap R.subtype
      (le_normalizer_conjugateSpanBy (sylowCenterSpan (P i)) X (le_conjugateSpanBy Q R hx))
  have hcentral : Vi ≤ centralizer (Ni : Set R) := by
    intro v hv n hn'
    apply Subtype.ext
    exact ((mem_omegaCenterIn_iff _ _).mp
      (source_replacement_span_le_inter_omega_of_inter_normal h i hn hv)).2.1 n hn'
  obtain ⟨A,hA,hout,_,hquad⟩ := Glauberman.exists_quadratic_maximum_abelian_outside
    Qi Ni Vi (isPGroup_pCoreIn 2 (P i)).comap_subtype hViQi inferInstance hnVi hcentral
    (thompson_escape_internal h i hn)
  have hbound := Glauberman.maximum_abelian_offender_bound hA hViQi hViNi inferInstance hcentral
  have hmQ : Qi.map R.subtype = Q := map_subgroupOf_eq_of_le hQP
  have hmV : Vi.map R.subtype = V := map_subgroupOf_eq_of_le hVR
  have hmN : Ni.map R.subtype = N := map_subgroupOf_eq_of_le hNR
  have hAm : A.map R.subtype ∈ thompsonAbelianSubgroups Q := by
    have hh := Glauberman.maximum_abelian_map_of_injective R.subtype R.subtype_injective hA
    rwa [hmQ] at hh
  have hescape : ¬ A.map R.subtype ≤ R.pCoreIn 2 := by
    intro ha
    apply hout
    intro a ha'
    exact ⟨hA.1 ha',ha (mem_map_of_mem R.subtype ha')⟩
  refine ⟨A.map R.subtype,hAm,hescape,?_,?_,?_⟩
  · exact fun hc => hescape (hc.trans (pCoreIn_mono_of_normalizes
      (conjugateSpanBy_le_self hQP) (le_normalizer_conjugateSpanBy _ _)))
  · have hh := congrArg (Subgroup.map R.subtype) hquad
    rwa [map_commutator,map_commutator,hmV,Subgroup.map_bot] at hh
  · have hc : (Vi ⊓ centralizer (A : Set R)).map R.subtype =
        V ⊓ centralizer (A.map R.subtype : Set G) := by
      rw [←map_inf_centralizer_of_injective R.subtype R.subtype_injective,hmV]
    have hb := hbound
    rw [←relIndex_map_map_of_injective (Vi ⊓ centralizer (A : Set R)) Vi R.subtype_injective,
      ←relIndex_map_map_of_injective Ni A R.subtype_injective,hc,hmV,hmN] at hb
    have he : N.relIndex (A.map R.subtype) = (R.pCoreIn 2).relIndex (A.map R.subtype) := by
      rw [←inf_relIndex_left (A.map R.subtype) N,←inf_relIndex_left (A.map R.subtype) (R.pCoreIn 2)]
      congr 1
      change A.map R.subtype ⊓ (Q ⊓ R.pCoreIn 2) = _
      rw [←inf_assoc,inf_eq_left.mpr hAm.1]
    exact hb.trans_eq he


/-- The original noncentral interface, retained as a specialization of the general construction. -/
theorem source_replacement_quadratic_offender (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
      ¬ A ≤ (P (other i)).pCoreIn 2 ∧ ¬ A ≤ X.pCoreIn 2 ∧
      ⁅⁅V,A⁆,A⁆ = ⊥ ∧ (V ⊓ centralizer (A : Set G)).relIndex V ≤
        ((P (other i)).pCoreIn 2).relIndex A := by
  have _ := hB
  have _ := hS
  have _ := hnc
  exact source_replacement_quadratic_offender_of_inter_normal h i hn

end CFSG.Quasithin.ChapterF.Source.DGS85
