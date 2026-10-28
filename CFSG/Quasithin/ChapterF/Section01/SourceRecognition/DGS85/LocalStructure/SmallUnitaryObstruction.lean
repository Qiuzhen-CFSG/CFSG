module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargedReplacementQuotient
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SmallSections

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Both adjacent-core obstructions for marked degree-one unitary enlargements

Under contrary normality, the replacement section for the full enlarged
endpoint descends to its actual core quotient. It retains the escaping
Thompson actor and its sharp original index. The fixed-generated PSU₃(2)
and SU₃(2) square bounds contradict that index, including the special
unitary action's possible cubic scalar kernel. The Sylow-to-normality
implication proves the second clause of 6.5.

The only model premise is the literal enlarged quotient marking. This
module proves the degree-one obstruction once 6.1 supplies that marking;
constructing it from an original small-unitary quotient remains open.
No neighboring-center or opposite-endpoint restriction is used.
Source: DGS, Groups and Graphs (1985), 6.4--6.5, pp.120--122.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Both 6.5 conclusions for either actual degree-one unitary enlarged quotient. -/
theorem source_small_unitary_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hm : ClassicalGroup.IsPSU (localEnlargement d ⧸ pCore 2 (localEnlargement d)) 3 2 ∨
      IsSU (localEnlargement d ⧸ pCore 2 (localEnlargement d)) 3 2) :
    (¬ localEnlargement d ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  have hnfull : ¬ P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
    intro hn
    let M := localEnlargement d
    let := d.finite_P
    let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
    let q := QuotientGroup.mk' (pCore 2 M)
    obtain ⟨W,hW,hWM,hWf,σ,hi,hres,hgen,U,C,_,_,A,_,_,_,hp,hquad,_,hnon,hbound⟩ :=
      source_enlarged_quotient_replacement_section h hB i d hn q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let := hW
    let := hWM
    let := hWf
    let : IsIrreducible σ := hi
    let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
    have hnt : σ ≠ 1 := by
      intro he
      obtain ⟨w,hw⟩ := exists_ne (0 : W)
      apply hw
      apply hres.le
      intro g
      change σ g w = w
      rw [he]
      rfl
    have hsquare := Unitary.small_unitary_generated_square_bound hm
      (pCore_quotient_pCore_eq_bot (G := M) 2) σ hnt hgen _ hp hquad
    have hh := hsquare.trans hbound
    nlinarith
  exact ⟨fun hn => hnfull ((inter_core_local_normal_iff h i d).mp hn),
    core_not_sylow_of_inter_not_normal h i hnfull⟩

end CFSG.Quasithin.ChapterF.Source.DGS85
