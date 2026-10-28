module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.Frattini.IndexTwoCentralizerPair

/-!
# The binary adjacent-core contradiction

An escaping odd transporter gives two central elementary supplements with
the same Frattini subgroup. The full Borel and this transporter generate
the first endpoint. The second endpoint already normalizes the closure
core, so faithfulness kills its Frattini subgroup. The core is now a
self-centralizing elementary subgroup of index two, which every odd
normalizer of the first core must preserve. This contradicts escape.

This uses the maximal full Borel and avoids requiring a finite completion.
Source: DGS, Groups and Graphs (1985), 6.5, printed pp.121--122.
-/
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual rank-one amalgam admits no escaping odd transporter for an index-two centralizer core. -/
theorem source_index_two_core_pair_obstruction (h : LocallyRankOneTriple P B)
    (i : Fin 2) (R U : Subgroup G) (hU : IsElementaryAbelian 2 U)
    (hUR : U ≤ R) (hR : R = (P i).pCoreIn 2 ⊓ centralizer (U : Set G))
    (hi : R.relIndex ((P i).pCoreIn 2) = 2)
    (hnR : P (other i) ≤ normalizer (R : Set G))
    (hnU : P (other i) ≤ normalizer (U : Set G))
    (x : G) (hx : x ∈ P i) (hodd : Odd (orderOf x))
    (hout : ¬ U.map (MulAut.conj x).toMonoidHom ≤ R) : False := by
  let := (Classical.choice (h.local_data i)).finite_P
  let A := (P i).pCoreIn 2
  have hAP : A ≤ P i := pCoreIn_le 2 _
  let : Finite A := Finite.of_injective (inclusion hAP) (inclusion_injective _)
  have hRA : R ≤ A := hR ▸ inf_le_left
  let : Finite R := Finite.of_injective (inclusion hRA) (inclusion_injective _)
  have hBP (k : Fin 2) : B ≤ P k :=
    le_sup_right.trans (Classical.choice (h.local_data k)).supplement.le
  have hnormA : P i ≤ normalizer (A : Set G) := (P i).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (P i)))
  have heA : A.map (MulAut.conj x).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hnormA hx)
  obtain ⟨_,_,_,_,hphiX⟩ := index_two_centralizer_pair_frattini A R U (MulAut.conj x)
    (isPGroup_pCoreIn 2 (P i)) hU hUR hR hi heA hout
  let N := (frattini R).map R.subtype
  have hnN : P (other i) ≤ normalizer (N : Set G) := hnR.trans
    (normalizer_le_normalizer_characteristic_image R (frattini R))
  have hxN : x ∈ normalizer (N : Set G) := mem_normalizer_iff_map_conj_eq.mpr hphiX
  have hxB : x ∉ B := by
    intro hxb
    have he := mem_normalizer_iff_map_conj_eq.mp (hnU (hBP _ hxb))
    exact hout (he.le.trans hUR)
  have hnI : P i ≤ normalizer (N : Set G) := by
    rcases source_borel_maximal (Classical.choice (h.local_data i))
      (P i ⊓ normalizer (N : Set G)) (le_inf (hBP i) ((hBP _).trans hnN)) inf_le_left
      with he | he
    · exact (hxB (he ▸ (show x ∈ P i ⊓ normalizer (N : Set G) from ⟨hx,hxN⟩))).elim
    · exact he.ge.trans inf_le_right
  have hgen : P i ⊔ P (other i) = ⊤ := by
    fin_cases i
    · exact h.generate
    · exact (sup_comm _ _).trans h.generate
  let : N.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (hgen ▸ sup_le hnI hnN))
  have hNB : N ≤ B := (map_subtype_le _).trans
    (hRA.trans (source_core_le_borel (Classical.choice (h.local_data i))))
  have hphi : frattini R = ⊥ := (map_eq_bot_iff_of_injective _ R.subtype_injective).mp
    (h.faithful N inferInstance hNB)
  let : Fact (IsPGroup 2 R) := ⟨(isPGroup_pCoreIn 2 (P i)).to_le hRA⟩
  let : IsElementaryAbelian 2 R := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  have hself : A ⊓ centralizer (R : Set G) = R := by
    apply le_antisymm
    · exact (inf_le_inf_left A (centralizer_le hUR)).trans hR.ge
    · exact le_inf hRA (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hxR := elementary_relIndex_two_normalized_of_odd_finite R A hRA hi hself x
    (hnormA hx) hodd
  exact hout ((map_mono hUR).trans (mem_normalizer_iff_map_conj_eq.mp hxR).le)
end CFSG.Quasithin.ChapterF.Source.DGS85
