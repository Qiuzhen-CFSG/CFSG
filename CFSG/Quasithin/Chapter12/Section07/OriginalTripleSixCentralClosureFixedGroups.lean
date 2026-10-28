module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosurePairLayer
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSingleGeneration

/-!
# The original transverse pair has common fixed groups

Actual single-element generation discharges the quotient-generation condition
for each nontrivial nonswap transverse lift. The exact quotient by (W∩Wᵍ)U,
its entire elementary commutator layer, and the original conjugator remain.

Source: the paragraph after Aschbacher--Smith12.7.18, printed pp.845--846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix MatchingEightGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original hypotheses produce the matching conjugator and its entire
literal quotient layer, without additional layer hypotheses. -/
theorem original_tripleSix_central_closure_fixed_groups
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
       K ≤ I ∧ I = K ⊔ W ∧
       I.pCoreIn 2 ≤ (T : Subgroup G) ∧
       I.pCoreIn 2 ≤ normalizer (W : Set G) ∧ U = ⁅U,I⁆ ∧
       (let P := ⁅pCore 2 I, (⊤ : Subgroup I)⁆
        let W₀ := W.subgroupOf I
        let W₁ := Wg.subgroupOf I
        let N := ((W ⊓ Wg) ⊔ U).subgroupOf I
        ∃ hn : N.Normal,
          let := hn
          let π := QuotientGroup.mk' N
          let A := (P ⊓ W₀).map π
          let B := (P ⊓ W₁).map π
          P.map I.subtype = ⁅I.pCoreIn 2,I⁆ ∧
          (P : Set I) = ((P ⊓ W₀ : Subgroup I) : Set I) *
            ((P ⊓ W₁ : Subgroup I) : Set I) ∧
          A ⊔ B = P.map π ∧ Disjoint A B ∧ IsElementaryAbelian 2 (P.map π) ∧
          P.map π ⊓ centralizer (W₀.map π : Set (I ⧸ N)) = A ∧
          ∀ (x : I) (hxN : (x : G) ∈ normalizer (U : Set G)), (x : G) ∈ Wg →
            q (U.normalizerMonoidHom.rangeRestrict ⟨x.val,hxN⟩) ≠ 1 →
            ¬ (q (U.normalizerMonoidHom.rangeRestrict ⟨x.val,hxN⟩)).IsSwap →
            P.map π ⊓ centralizer ({π x} : Set (I ⧸ N)) = B)) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨q,g,hq,hK,hW,hWg,_,hKI,hIe,_,hsingle⟩ :=
    original_tripleSix_central_closure_single_generation h structural D a z hz hzT hnot houter
  let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
  let I := W ⊔ Wg
  let P := ⁅pCore 2 I,(⊤ : Subgroup I)⁆
  let W₀ := W.subgroupOf I
  let W₁ := Wg.subgroupOf I
  let N := ((W ⊓ Wg) ⊔ U).subgroupOf I
  obtain ⟨hcoreT,hcoreW,hUcomm,hn,hPmap,hprod,hsplit,hdis,helem,hfixed,hxfixed⟩ :=
    original_tripleSix_central_closure_pair_layer_at h structural D a z hz hzT hnot g hKI hIe
  let := hn
  let π := QuotientGroup.mk' N
  refine ⟨q,g,hq,hK,hW,hWg,hKI,hIe,hcoreT,hcoreW,hUcomm,hn,
    hPmap,hprod,hsplit,hdis,helem,hfixed,?_⟩
  intro x hxN hx hne hns
  apply hxfixed x hx
  have he := hsingle ⟨x.val,hxN⟩ hx hne hns
  change W ⊔ zpowers x.val = I at he
  have hgen : W₀ ⊔ zpowers x = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le
      (show W ≤ I from le_sup_left),← MonoidHom.range_eq_map,range_subtype]
    exact he
  change W₀.map π ⊔ zpowers (π x) = ⊤
  rw [← MonoidHom.map_zpowers,← Subgroup.map_sup,hgen,map_top_of_surjective π
    (QuotientGroup.mk'_surjective N)]

end CFSG.Quasithin.Chapter12.Section07
