module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureGenerated
public import Theory.GroupTheory.ConjugatePairLayerFixed
public import Theory.GroupTheory.PCoreImage

/-!
# The original two-conjugate commutator layer

The group I=K W is normal in KT, so its actual two-core lies in T and
normalizes W. The original K-conjugator gives the other normalization.
The chosen module is U=[U,K]=[U,I], while the original almost-special
bounds put the squares and commutators of W in U. These facts construct
the exact quotient I/((W∩Wᵍ)U) and its split elementary commutator layer.

Source: Aschbacher--Smith, after (12.7.18), printed pp.845--846.
The original automizer marking and K-conjugator are retained. Single-element
generation is stated as the precise condition for the final fixed group,
not inferred from generation of an induced automizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix MatchingEightGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The layer for an already chosen original K-conjugator, once its actual
pair contains K. This preserves that choice for subsequent generation arguments. -/
theorem original_tripleSix_central_closure_pair_layer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∀ g : K,
      let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
      let I := W ⊔ Wg
      K ≤ I → I = K ⊔ W →
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
          ∀ x : I, (x : G) ∈ Wg → W₀.map π ⊔ zpowers (π x) = ⊤ →
            P.map π ⊓ centralizer ({π x} : Set (I ⧸ N)) = B) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  dsimp only
  intro g hKI hIe
  let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
  let I := W ⊔ Wg
  change K ≤ I at hKI
  change I = K ⊔ W at hIe
  let M := K ⊔ (T : Subgroup G)
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot).1
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have he := hc.2.1
    change W = _ at he
    rw [he]
    exact le_sup_right.trans (le_normalizer_conjugateSpanBy _ _)
  have hIM : I ≤ M := hIe.le.trans (sup_le le_sup_left (hWT.trans le_sup_right))
  have hMI : M ≤ normalizer (I : Set G) := by
    apply sup_le (hKI.trans I.le_normalizer)
    rw [hIe]
    exact (le_inf D.sylow_normalizes_component hTW).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hcoreT : I.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes hIM hMI).trans
    have hh := pCoreIn_le_sylow M (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right))
    rw [Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from le_sup_right)] at hh
    exact hh
  have hcoreW : I.pCoreIn 2 ≤ normalizer (W : Set G) := hcoreT.trans hTW
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hIU : I ≤ normalizer (U : Set G) := hIM.trans (sup_le D.normalizes hTN)
  have hUI : U ≤ I := D.le_component.trans hKI
  have hUcomm : U = ⁅U,I⁆ := le_antisymm
    (D.eq_commutator.le.trans (commutator_mono le_rfl hKI))
    (le_normalizer_iff_commutator_le_left.mp hIU)
  let := D.elementary
  have hUcore : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) hUI hIU
  have hW2 : IsPGroup 2 W := T.isPGroup'.to_le hWT
  have hphi : (frattini W).map W.subtype ≤ zpowers (z : G) := hc.2.2.2.1
  have hZU : zpowers (z : G) ≤ U := zpowers_le.mpr z.property
  have hWW : ⁅W,W⁆ ≤ U := (derived_le_of_frattini_image_le hW2 hphi).trans hZU
  have hsq : ∀ w ∈ W, w ^ 2 ∈ U := by
    let : Fact (IsPGroup 2 W) := ⟨hW2⟩
    intro w hw
    exact hZU (hphi (mem_map_of_mem W.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨w, hw⟩ : W))))
  let W₀ := W.subgroupOf I
  let W₁ := Wg.subgroupOf I
  let U₀ := U.subgroupOf I
  let Q := pCore 2 I
  let P := ⁅Q, (⊤ : Subgroup I)⁆
  let N := ((W ⊓ Wg) ⊔ U).subgroupOf I
  let gi : I := ⟨g.val, hKI g.property⟩
  have hW₀ : W₀.map I.subtype = W := map_subgroupOf_eq_of_le le_sup_left
  have hW₁ : W₁.map I.subtype = Wg := map_subgroupOf_eq_of_le le_sup_right
  have hU₀ : U₀.map I.subtype = U := map_subgroupOf_eq_of_le hUI
  have hconj : W₀.map (MulAut.conj gi).toMonoidHom = W₁ := by
    apply map_injective I.subtype_injective
    rw [map_map, hW₁]
    change W₀.map ((MulAut.conj g.val).toMonoidHom.comp I.subtype) = _
    rw [← map_map, hW₀]
  have hgen : W₀ ⊔ W₁ = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, hW₀, hW₁, ← MonoidHom.range_eq_map, range_subtype]
  have hQN : Q ≤ normalizer (W₀ : Set I) := by
    intro x hx
    exact (le_normalizer_comap I.subtype) (hcoreW (mem_map_of_mem I.subtype hx))
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer hIU
  have hUQ : U₀ ≤ Q := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hUcore hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hUmove : ⁅U₀,(⊤ : Subgroup I)⁆ = U₀ := by
    apply map_injective I.subtype_injective
    rw [map_commutator, hU₀, ← MonoidHom.range_eq_map, range_subtype]
    exact hUcomm.symm
  have hder : ⁅W₀,W₀⁆ ≤ U₀ := by
    intro x hx
    have hm := mem_map_of_mem I.subtype hx
    rw [map_commutator, hW₀] at hm
    exact hWW hm
  have hsq₀ : ∀ w ∈ W₀, w ^ 2 ∈ U₀ := fun w hw => hsq w.val hw
  have hder₁ : ⁅W₁,W₁⁆ ≤ U₀ := by
    have hh := map_mono (f := (MulAut.conj gi).toMonoidHom) hder
    have hUg : U₀.map (MulAut.conj gi).toMonoidHom = U₀ := Normal.map_conj_eq U₀ gi
    rwa [map_commutator, hconj, hUg] at hh
  have hN : N = (W₀ ⊓ W₁) ⊔ U₀ := by
    change ((W ⊓ Wg) ⊔ U).subgroupOf I = _
    rw [subgroupOf_sup (show W ⊓ Wg ≤ I from inf_le_left.trans le_sup_left) hUI]
    rfl
  have hn : N.Normal := by
    rw [hN]
    exact almost_special_pair_layer_normal W₀ W₁ U₀ hgen hder hder₁
  let := hn
  let π := QuotientGroup.mk' N
  have hk : π.ker = (W₀ ⊓ W₀.map (MulAut.conj gi).toMonoidHom) ⊔ U₀ := by
    rw [QuotientGroup.ker_mk', hN, hconj]
  have hgen' : W₀ ⊔ W₀.map (MulAut.conj gi).toMonoidHom = ⊤ := hconj.symm ▸ hgen
  have hfixed := conjugate_pair_commutator_quotient_fixed π (QuotientGroup.mk'_surjective N)
    W₀ Q U₀ gi hgen' hQN hUQ hUmove hk hder hsq₀
  dsimp only at hfixed
  rw [hconj] at hfixed
  have hQW₁ : Q ≤ normalizer (W₁ : Set I) := by
    have hh := (map_mono (f := (MulAut.conj gi).toMonoidHom) hQN).trans
      (W₀.le_normalizer_map (MulAut.conj gi).toMonoidHom)
    have hQg : Q.map (MulAut.conj gi).toMonoidHom = Q := Normal.map_conj_eq Q gi
    rwa [hQg, hconj] at hh
  refine ⟨hcoreT,hcoreW,hUcomm,hn,?_,?_,
    hfixed.1,hfixed.2.1,hfixed.2.2.1,hfixed.2.2.2.1,?_⟩
  · rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  · exact commutator_eq_product_intersections_of_normalizes_generators W₀ W₁ Q hgen hQN hQW₁
  · intro x hx hgenx
    exact hfixed.2.2.2.2 x hx hgenx

/-- The original hypotheses produce the matching conjugator and its entire
literal quotient layer, without additional layer hypotheses. -/
theorem original_tripleSix_central_closure_pair_layer
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
          ∀ x : I, (x : G) ∈ Wg → W₀.map π ⊔ zpowers (π x) = ⊤ →
            P.map π ⊓ centralizer ({π x} : Set (I ⧸ N)) = B)) := by
  obtain ⟨q,g,hq,hK,hW,hWg,_,hKI,hIe,_⟩ :=
    original_tripleSix_central_closure_generated h structural D a z hz hzT hnot houter
  exact ⟨q,g,hq,hK,hW,hWg,hKI,hIe,
    original_tripleSix_central_closure_pair_layer_at h structural D a z hz hzT hnot g hKI hIe⟩

end CFSG.Quasithin.Chapter12.Section07
