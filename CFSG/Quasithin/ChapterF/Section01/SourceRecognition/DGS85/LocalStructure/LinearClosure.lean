module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BaumannPremises
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import Theory.SpecificGroups.SL2.NormalizerInvariantClosure

/-!
# Linear Chapter 6 closure premises and the original-core application

Under the printed relative normality assumption, the full Borel normalizes
the opposite core inside its actual Sylow two-subgroup. A marked SL₂ quotient
of the enlarged endpoint therefore supplies the full Sylow image. Transfer
modulo the common core proves the missing Sylow premise on the literal
adjacent-core closure. Its quotient is the restriction of the original map,
transported through an equivalence preserving every completion element.
Together with the established characteristic-two and characteristic-normal
facts, these results discharge all premises of the Baumann application in
this linear case.

For F1.11, the original local linear quotient constructs the enlarged marking.
The final theorem transports the resulting commutator bound back to the
original parabolic core and the reduced endpoint inside the original group.
The full Borel enters through its actual two-core; original S is not identified
with that core. Only the local groups are required to be finite.

Source: DGS, Groups and Graphs (1985), 6.1 and 6.3--6.5, pp.118--122;
Aschbacher--Smith F.1.9, pp.261--262. The general model selection and the
6.5 contradiction remain further obligations.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual linear local quotient supplies the Sylow and marked closure quotient premises of 6.4. -/
theorem source_linear_closure_premises (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    (¬ 2 ∣ (coreInClosure (P i) (P (other i))).index) ∧
      ∃ qX : coreClosure (P i) (P (other i)) →* SL(2,F),
        Function.Surjective qX ∧ qX.ker = pCore 2 (coreClosure (P i) (P (other i))) ∧
          ∀ x, ∃ y : localEnlargement d,
            (y : G) = originalEmbedding (P i) (P (other i)) x ∧ qX x = q y := by
  let := d.finite_P
  let J := localEnlargement d
  let : Finite J := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have hQBS : (P i).pCoreIn 2 ≤ B.pCoreIn 2 := pGroup_le_core_of_core_sylow B _
    (source_core_le_borel (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB
  have hAJ : (P i).pCoreIn 2 ≤ J := hQBS.trans le_sup_right
  have hAP : (P i).pCoreIn 2 ≤ P (other i) := hAJ.trans (localEnlargement_le d)
  let A := ((P i).pCoreIn 2).subgroupOf J
  obtain ⟨T,hT⟩ := hS (other i)
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (localEnlargement_le d)
    (source_all_sylows_le_enlargement d hB (hS (other i)) T)
  have hRS : (R : Subgroup J).map J.subtype = B.pCoreIn 2 :=
    hR.trans (sylow_image_eq_edge_core _ B hBP hB T hT)
  have hR' : (R : Subgroup J) = (B.pCoreIn 2).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hRS,map_subgroupOf_eq_of_le (show B.pCoreIn 2 ≤ J from le_sup_right)]
  have hAR : A ≤ (R : Subgroup J) := by rw [hR']; exact fun _ hx => hQBS hx
  have hkn : q.ker = ((P (other i)).pCoreIn 2).subgroupOf J := by
    rw [hk]
    apply map_injective J.subtype_injective
    change J.pCoreIn 2 = _
    rw [localEnlargement_core d,map_subgroupOf_eq_of_le]
    exact (source_core_le_star d).trans le_sup_left
  have hneq : ¬ A ≤ q.ker := by
    intro ha
    apply core_not_le_of_inter_normal h i ((inter_core_local_normal_iff h i d).mp hn)
    intro x hx
    exact (show (⟨x,hAJ hx⟩ : J) ∈ ((P (other i)).pCoreIn 2).subgroupOf J from
      hkn ▸ ha (show (⟨x,hAJ hx⟩ : J) ∈ A from hx))
  have hnormal : normalizer (R : Set J) ≤ normalizer (A : Set J) := by
    have hNr : normalizer (R : Set J) = (normalizer (B.pCoreIn 2 : Set G)).subgroupOf J := by
      rw [←R.coe_coe,hR']
      exact (subgroupOf_normalizer_eq (show B.pCoreIn 2 ≤ J from le_sup_right)).symm
    intro x hx
    rw [hNr] at hx
    have hxb : (x : G) ∈ B := source_full_normalizer_borel_core d hB ▸
      (show (x : G) ∈ P (other i) ⊓ normalizer (B.pCoreIn 2 : Set G) from
        ⟨localEnlargement_le d x.property,hx⟩)
    apply le_normalizer_comap J.subtype
    exact ((le_sup_right.trans (Classical.choice (h.local_data i)).supplement.le).trans
      ((P i).le_normalizer.trans (normalizer_le_normalizer_characteristic_image (P i) (pCore 2 (P i))))) hxb
  have hD : (A ⊓ q.ker).Normal := by
    rw [hkn]
    change ((((P i).pCoreIn 2).subgroupOf J) ⊓ (((P (other i)).pCoreIn 2).subgroupOf J)).Normal
    change ((((P i).pCoreIn 2).comap J.subtype) ⊓
      (((P (other i)).pCoreIn 2).comap J.subtype)).Normal
    rw [←comap_inf]
    exact normal_subgroupOf_of_le_normalizer hn
  obtain ⟨W,hW⟩ := Matrix.SpecialLinearGroup.normalClosure_linear_sylow R q hq
    (hk.symm ▸ (pCore_isPGroup (p := 2) (G := J))) A hAR hneq hnormal hD
  obtain ⟨honto,hker⟩ := Matrix.SpecialLinearGroup.normalClosure_linear_quotient R q hq hk A hAR hneq hnormal
  have hlocal : conjugateSpanBy ((P i).pCoreIn 2) J =
      conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) := core_closure_local_eq_full h i d
  let e : coreClosure (P i) J ≃* coreClosure (P i) (P (other i)) :=
    ((MarkedClosure.coreClosureEquiv (P i) J hAJ).trans (MulEquiv.subgroupCongr hlocal)).trans
      (MarkedClosure.coreClosureEquiv (P i) (P (other i)) hAP).symm
  have heco (x : coreClosure (P i) J) :
      originalEmbedding (P i) (P (other i)) (e x) = originalEmbedding (P i) J x := by
    rw [←MarkedClosure.coreClosureEquiv_coe (P i) (P (other i)) hAP]
    change (((MarkedClosure.coreClosureEquiv (P i) (P (other i)) hAP)
      ((MarkedClosure.coreClosureEquiv (P i) (P (other i)) hAP).symm _)) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hi : ¬ 2 ∣ (coreInClosure (P i) J).index := by
    change ¬ 2 ∣ (A.subgroupOf (normalClosure (A : Set J))).index
    rw [←hW]
    exact W.not_dvd_index
  have him : (coreInClosure (P i) J).map e.toMonoidHom =
      coreInClosure (P i) (P (other i)) := by
    apply map_injective (MarkedClosure.originalEmbedding_injective (P i) (P (other i)))
    rw [map_map,coreInClosure_image _ _ hAP]
    rw [show (originalEmbedding (P i) (P (other i))).comp e.toMonoidHom =
      originalEmbedding (P i) J from MonoidHom.ext heco]
    exact coreInClosure_image _ _ hAJ
  have hif : (coreInClosure (P i) (P (other i))).index = (coreInClosure (P i) J).index := by
    rw [←him]
    exact index_map_equiv _ e
  refine ⟨hif ▸ hi,?_⟩
  let qX := (q.comp (coreClosure (P i) J).subtype).comp e.symm.toMonoidHom
  refine ⟨qX,honto.comp e.symm.surjective,?_,?_⟩
  · change ((q.comp (coreClosure (P i) J).subtype).comp e.symm.toMonoidHom).ker = _
    change (q.comp (coreClosure (P i) J).subtype).ker = pCore 2 (coreClosure (P i) J) at hker
    rw [←MonoidHom.comap_ker,hker]
    have hm := pCore_map_iso 2 e
    rw [←map_equiv_eq_comap_symm']
    exact hm
  · intro x
    refine ⟨(e.symm x).val,?_,rfl⟩
    have he := heco (e.symm x)
    rw [e.apply_symm_apply] at he
    exact he.symm

/-- Baumann on the original closure, with its Sylow and quotient premises discharged from the local linear map. -/
theorem source_linear_baumann_commutator (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ⁅X.pCoreIn 2,X⁆ ≤ conjugateSpanBy (omegaCenterIn ((P i).pCoreIn 2)) X := by
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  have hAB : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  have hs : ¬ 2 ∣ ((P i).pCoreIn 2).relIndex
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) := by
    rwa [MarkedClosure.coreInClosure_index _ _ hAB] at hi
  let := Fintype.ofFinite F
  obtain ⟨n,_,hF⟩ := FiniteField.card F 2
  exact MarkedClosure.source_baumann_commutator h hB i d hn hs qX hqX hkX n.property
    ((Nat.card_eq_fintype_card (α := F)).trans hF)

namespace Reduction
open Subgroup.CosetGeometry.RankTwo
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual enlarged quotient, constructed from the original F1.11 local linear marking. -/
def reduced_linearEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    (e : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* SL(2,F) := by
  let eSL : SL(2,F) ≃* PSL(2,F) := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      ((reduced_graphLinearQuotient h false e).trans eSL.symm)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      ((reduced_graphLinearQuotient h true e).trans eSL.symm)

/-- Reduced F1.11 application with no additional Sylow or closure-quotient assumptions. -/
theorem reduced_linear_baumann_commutator (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) :
    let X := conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S (other i)).subgroupOf (G₀ L S))
    ⁅X.pCoreIn 2,X⁆ ≤ conjugateSpanBy (omegaCenterIn (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)) X := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  exact source_linear_baumann_commutator (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i d hn q hq hk

/-- The local enlargement has exactly the original starred endpoint plus the original full-Borel core as image. -/
theorem reduced_localEnlargement_image (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S))) :
    (localEnlargement d).map (G₀ L S).subtype = enlargedEndpoint L S i := by
  fin_cases i
  · exact (congrArg (Subgroup.map (G₀ L S).subtype)
      (graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d).symm).trans
        (reduced_graphLocalGroup_image h false)
  · exact (congrArg (Subgroup.map (G₀ L S).subtype)
      (graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d).symm).trans
        (reduced_graphLocalGroup_image h true)

/-- The printed relative normality premise yields the commutator bound on the literal original parabolic core. -/
theorem reduced_original_linear_baumann_commutator (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) :
    let X := conjugateSpanBy ((parabolic L S i).pCoreIn 2) (P₀ L S (other i))
    ⁅X.pCoreIn 2,X⁆ ≤ conjugateSpanBy (omegaCenterIn ((parabolic L S i).pCoreIn 2)) X := by
  have hPG (j : Fin 2) : P₀ L S j ≤ G₀ L S := by
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  have hcore (j : Fin 2) : (((P₀ L S j).subgroupOf (G₀ L S)).pCoreIn 2).map
      (G₀ L S).subtype = (parabolic L S j).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le (hPG j),P₀_core h j]
  have hD : ((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
      ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Subgroup (G₀ L S)).map
      (G₀ L S).subtype = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,hcore,hcore]
  have hn0 : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)) := by
    intro x hx
    have hxl : (x : G) ∈ enlargedEndpoint L S (other i) := by
      rw [←reduced_localEnlargement_image h (other i)
        (Classical.choice ((reduced_triple h).local_data (other i)))]
      exact mem_map_of_mem (G₀ L S).subtype hx
    have hxn := le_normalizer_comap (G₀ L S).subtype (hn hxl)
    rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hxn
  have hm := map_mono (f := (G₀ L S).subtype) (reduced_linear_baumann_commutator h i hn0 e)
  dsimp only at hm ⊢
  simp only [map_commutator,map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_conjugateSpanBy,NilesRankOneKernel.omegaCenterIn_map_injective _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le (hPG i),map_subgroupOf_eq_of_le (hPG (other i)),P₀_core h i] at hm
  exact hm

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
