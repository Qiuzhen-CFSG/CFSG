module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosurePair
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixComponentImageLift
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixActionKernel
public import Theory.GroupTheory.ConjugatePairImageGeneration

/-!
# Single-element generation in the original transverse pair

The full action kernel inside KT lies in T and normalizes the original W.
Every full-image subgroup containing W therefore contains each I-conjugate
of W. The actual transverse pair generates I, so every nontrivial nonswap
lift in the second member generates I with W. The original marking and
K-conjugator are retained.

Source: the paragraph after Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix MatchingEightGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual pair and every nontrivial nonswap transverse lift generate
the same original group, including its full action kernel. -/
theorem original_tripleSix_central_closure_single_generation
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
       K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
       ∀ b : normalizer (U : Set G), (b : G) ∈ Wg →
         q (U.normalizerMonoidHom.rangeRestrict b) ≠ 1 →
         ¬ (q (U.normalizerMonoidHom.rangeRestrict b)).IsSwap →
         W ⊔ zpowers (b : G) = I) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  let Q := K.pCoreIn 2
  obtain ⟨q, g, hq, hK, hW, hWg, hfull, hsingle⟩ :=
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
  refine ⟨q, g, hq, hK, hW, hWg, hfull, hKI, hIe, hQI, ?_⟩
  intro b hb hne hns
  let J := W ⊔ zpowers b.val
  have hJI : J ≤ I := sup_le le_sup_left ((zpowers_le.mpr hb).trans le_sup_right)
  have hIM : I ≤ K ⊔ (T : Subgroup G) :=
    hI.trans (sup_le le_sup_left (hWT.trans le_sup_right))
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hIN : I ≤ normalizer (U : Set G) := hIM.trans (sup_le D.normalizes hTN)
  let α := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hIN)
  let W₀ := W.subgroupOf I
  let J₀ := J.subgroupOf I
  let gi : I := ⟨g.val,hKI g.property⟩
  have hW₀ : W₀.map I.subtype = W := map_subgroupOf_eq_of_le le_sup_left
  have hJ₀ : J₀.map I.subtype = J := map_subgroupOf_eq_of_le hJI
  have hgen : W₀ ⊔ W₀.map (MulAut.conj gi).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_map]
    change W₀.map I.subtype ⊔ W₀.map
      ((MulAut.conj g.val).toMonoidHom.comp I.subtype) = _
    rw [← map_map,hW₀,← MonoidHom.range_eq_map,range_subtype]
  have hker : α.ker ≤ normalizer (W₀ : Set I) := by
    intro x hx
    have hxc : x.val ∈ centralizer (U : Set G) := by
      apply mem_centralizer_iff.mpr
      intro u hu
      have he := congrArg (fun c : Automizer U => (c.val (⟨u,hu⟩ : U)).val) hx
      change x.val * u * x.val⁻¹ = u at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hxt := (original_tripleSix_action_kernel h structural D a).2
      ⟨hIM x.property,hxc⟩
    exact (le_normalizer_comap I.subtype) (hTW hxt)
  have himage : J₀.map α = α.range := by
    apply le_antisymm (map_le_range _ _)
    rintro _ ⟨x,rfl⟩
    have hx : α x ∈ inducedAutomizer U J := (hsingle b hb hne hns).symm ▸ mem_top _
    obtain ⟨n,hn,he⟩ := hx
    exact ⟨⟨n.val,hJI hn⟩,hn,he⟩
  have htop := eq_top_of_conjugate_pair_image α W₀ J₀ gi hgen
    (subgroupOf_mono I (show W ≤ J from le_sup_left)) hker himage
  have hh := congrArg (fun A : Subgroup I => A.map I.subtype) htop
  simpa only [hJ₀,← MonoidHom.range_eq_map,range_subtype] using hh

end CFSG.Quasithin.Chapter12.Section07
