module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.Frattini.CentralizerPairDisplacement

/-!
# The faithful-amalgam core-pair contradiction at arbitrary index

Sharp element displacement gives the two central supplements and fixes
the common Frattini image under the escaping odd transporter. The full
Borel and that transporter generate the first endpoint; the other
endpoint normalizes the Frattini image already. Faithfulness makes it
trivial. Both cores are now elementary, so the odd-order pair theorem
forces the transporter to preserve the first core, contradicting escape.

The ambient completion need not be finite. The exact displacement input
is supplied by NeighborDisplacement in LinearNoncentralObstruction.
Source: DGS, Groups and Graphs (1985), proof of (6.5), printed p.122.
-/


open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Sharp displacement and the faithful full Borel exclude an escaping odd transporter. -/
theorem source_displacement_core_pair_obstruction (h : LocallyRankOneTriple P B)
    (i : Fin 2) (R U : Subgroup G) (hU : IsElementaryAbelian 2 U)
    (hUR : U ≤ R) (hR : R = (P i).pCoreIn 2 ⊓ centralizer (U : Set G))
    (hb : ∀ a ∈ (P i).pCoreIn 2, a ∉ R →
      R.relIndex ((P i).pCoreIn 2) ≤ (centralizer ({a} : Set G)).relIndex U)
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
  have hnAR : A ≤ normalizer (R : Set G) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans ((hBP _).trans hnR)
  obtain ⟨_,_,_,_,_,hphiX⟩ := centralizer_pair_frattini_of_displacement A R U (MulAut.conj x)
    (isPGroup_pCoreIn 2 (P i)) hU hUR hR hnAR heA hb hout
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
  have heo : Odd (orderOf (MulAut.conj x)) :=
    hodd.of_dvd_nat (orderOf_map_dvd MulAut.conj x)
  have hxR := centralizer_pair_fixed_of_odd A R U (MulAut.conj x)
    (isPGroup_pCoreIn 2 (P i)) hU hUR hR hnAR heA hb heo
  exact hout ((map_mono hUR).trans hxR.le)

end CFSG.Quasithin.ChapterF.Source.DGS85
