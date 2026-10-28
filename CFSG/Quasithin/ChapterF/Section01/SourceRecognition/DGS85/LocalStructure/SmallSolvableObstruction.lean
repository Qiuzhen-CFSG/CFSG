module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ClosureQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementSection
public import Theory.Representation.SmallQuotientActionImage
public import Theory.Representation.RankOne.QuadraticRecognition.SmallSolvableActors

/-!
# The small solvable adjacent-core obstruction

Under contrary normality, restrict the enlarged core quotient to the
literal closure X=<Q_delta^G_lambda>. Its image may be proper, but has
order dividing twenty. The residual-moving simple section of the actual
replacement span V=<Z_delta^X> has exactly that restricted kernel. Thus
the original escaping Thompson actor survives with its original index.
The D₁₀/Sz(2) square bounds contradict the sharp replacement bound.

Both clauses of 6.5 follow, with no assumption on the opposite endpoint
model or on the neighboring center being central. The original completion
can be infinite. SmallSolvableApplication supplies the original F1.11
markings and retains the strict dihedral enlargement alternative.
Source: DGS, Groups and Graphs (1985), 6.4--6.5, pp.120--122.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G D : Type*} [Group G] [Group D] [Finite D]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Both source 6.5 conclusions for an enlarged quotient of order dividing twenty. -/
theorem source_small_solvable_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (q : localEnlargement d →* D) (hk : q.ker = pCore 2 (localEnlargement d))
    (hcard : Nat.card D ∣ 20) :
    (¬ localEnlargement d ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  have hnfull : ¬ P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
    intro hn
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let := d.finite_P
    have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
      ((source_core_le_borel (Classical.choice (h.local_data i))).trans
        (le_sup_right.trans d.supplement.le))
    let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
    obtain ⟨f,hfk,hfj,_⟩ := source_closure_quotient_restriction h hB i d q hk
    obtain ⟨U,C,hUV,W,hW,hWM,hWf,ρ,⟨s⟩,hi,_,hcore,hfaith,hzero,hres,_,A,hA,hout,_,hquad,hbound⟩ :=
      source_replacement_simple_quadratic_section_of_inter_normal h hB hS i hn
    let := hW
    let := hWM
    let := hWf
    let : IsIrreducible ρ := hi
    let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
    have himfix : fixedSpace (imageRepresentation ρ) ⊤ = ⊥ :=
      bot_unique ((fixedSpace_antitone _ le_top).trans hres.le)
    have hρfix : fixedSpace ρ ⊤ = ⊥ := by
      have he : (imageRepresentation ρ).comp (actionHom ρ) = ρ :=
        MonoidHom.ext (imageRepresentation_actionHom ρ)
      rw [←he,fixedSpace_comp_map,map_top_of_surjective (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective]
      exact himfix
    have hfr : f.rangeRestrict.ker = pCore 2 X := (MonoidHom.ker_rangeRestrict f).trans hfk
    have hRzero := pCore_range_eq_bot_of_ker_eq_pCore 2 f hfk
    have hRcard : Nat.card f.range ∣ 20 := (card_subgroup_dvd_card f.range).trans hcard
    obtain ⟨hker,e,he⟩ := actionImage_equiv_of_quotient_card_dvd_twenty ρ f.rangeRestrict
      f.rangeRestrict_surjective (hfr ▸ hcore) hRcard hRzero hzero hρfix
    have hak : (actionHom ρ).ker = ((P (other i)).pCoreIn 2).subgroupOf X := by
      change ρ.asGroupHom.rangeRestrict.ker = _
      rw [MonoidHom.ker_rangeRestrict]
      have hh : ρ.asGroupHom.ker = ρ.ker := by
        ext x
        exact ⟨fun hh => congrArg Units.val hh,fun hh => Units.ext hh⟩
      exact hh.trans (hker.trans ((MonoidHom.ker_rangeRestrict f).trans hfj))
    let I := (A.subgroupOf X).map (actionHom ρ)
    have hAX : A ≤ X := hA.1.trans (le_conjugateSpanBy _ _)
    have hc : Nat.card I = ((P (other i)).pCoreIn 2).relIndex A :=
      actor_image_card_eq_relIndex X _ A (actionHom ρ) hak hAX
    have hIc : 1 < Nat.card I := by
      rw [hc]
      let : Finite A := Finite.of_injective (inclusion hAX) (inclusion_injective _)
      have hp : 0 < ((P (other i)).pCoreIn 2).relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
      have hn1 : ((P (other i)).pCoreIn 2).relIndex A ≠ 1 :=
        fun hh => hout (relIndex_eq_one.mp hh)
      omega
    have hI : IsPGroup 2 I := ((isPGroup_pCoreIn 2 _).to_le hA.1).comap_subtype.map _
    have hcardim : Nat.card (actionImage ρ) ∣ 20 := (Nat.card_congr e.toEquiv).symm ▸ hRcard
    have hsquare := card_dvd_twenty_quadratic_square_bound hcardim hzero
      (imageRepresentation ρ) hfaith I hI hquad
    rw [←hc] at hbound
    have hh := hsquare.trans hbound
    nlinarith
  exact ⟨fun hn => hnfull ((inter_core_local_normal_iff h i d).mp hn),
    core_not_sylow_of_inter_not_normal h i hnfull⟩
end CFSG.Quasithin.ChapterF.Source.DGS85
