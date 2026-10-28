module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosurePair
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixComponentImageLift

/-!
# The original component lies in the two-conjugate group

The unchanged two-core of K lies in T, so it normalizes the original
central closure W. Characteristicity in K makes it normalize the chosen
K-conjugate as well. The proved full action image therefore lifts to
K≤I for I=<W,gWg⁻¹>. All original subgroups and the chosen K-conjugator
are retained.

Source: the generation paragraph after Aschbacher--Smith12.7.18,
printed p.845, using the argument of G.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix MatchingEightGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual original K is contained in the join of the two actual
closures, with the transverse marking and full action generation retained. -/
theorem original_tripleSix_central_closure_generated
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∃ (q : Automizer U →* Equiv.Perm (Fin 6)) (g : K),
      Function.Surjective q ∧
      (inducedAutomizer U K).map q = alternatingGroup (Fin 6) ∧
      (inducedAutomizer U W).map q = matchingEight ∧
      (let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
       let I := W ⊔ Wg
       (inducedAutomizer U Wg).map q = shiftedMatchingEight ∧
       inducedAutomizer U I = ⊤ ∧ K ≤ I ∧ I = K ⊔ W ∧
       K.pCoreIn 2 ≤ normalizer (I : Set G)) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  let Q := K.pCoreIn 2
  obtain ⟨q, g, hq, hK, hW, hWg, hfull, _⟩ :=
    original_tripleSix_central_closure_pair h structural D a z hz hzT hnot houter
  let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
  let I := W ⊔ Wg
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot).1
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have he := (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).2.1
    change W = _ at he
    rw [he]
    exact le_sup_right.trans (le_normalizer_conjugateSpanBy _ _)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    D.sylow_normalizes_component.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hQT : Q ≤ (T : Subgroup G) :=
    sup_eq_right.mp (T.is_maximal'
      ((isPGroup_pCoreIn 2 K).to_sup_of_normal_left' T.isPGroup' hTQ) le_sup_right)
  have hQW : Q ≤ normalizer (W : Set G) := hQT.trans hTW
  have hgQ : (g : G) ∈ normalizer (Q : Set G) :=
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))) g.property
  have hQg : Q.map (MulAut.conj (g : G)).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp hgQ
  have hQWg : Q ≤ normalizer (Wg : Set G) := by
    have hh := (map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hQW).trans
      (W.le_normalizer_map (MulAut.conj (g : G)).toMonoidHom)
    rwa [hQg] at hh
  have hQI : Q ≤ normalizer (I : Set G) :=
    (le_inf hQW hQWg).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hI : I ≤ K ⊔ W := by
    apply sup_le le_sup_right
    rintro _ ⟨x, hx, rfl⟩
    exact (K ⊔ W).mul_mem
      ((K ⊔ W).mul_mem (mem_sup_left g.property) (mem_sup_right hx))
      ((K ⊔ W).inv_mem (mem_sup_left g.property))
  have hKI : K ≤ I := original_tripleSix_component_le_of_full_image h structural D a I
    (hI.trans (sup_le le_sup_left (hWT.trans le_sup_right))) hQI hfull
  have hIe : I = K ⊔ W := le_antisymm hI (sup_le hKI le_sup_left)
  exact ⟨q, g, hq, hK, hW, hWg, hfull, hKI, hIe, hQI⟩

end CFSG.Quasithin.Chapter12.Section07
