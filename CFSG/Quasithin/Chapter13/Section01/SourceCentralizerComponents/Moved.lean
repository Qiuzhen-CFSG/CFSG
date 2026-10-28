module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.Basic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource
public import Theory.GroupTheory.CComponent.CommutatorDichotomy

/-!
# The component moved by the original centralizer radical

In an SQTK-group, a C-component has normalizer of index at most two.
A two-perfect subgroup X therefore normalizes it. When a component K has
quasisimple two-core quotient and [K,X] escapes the ambient two-core,
the ordinary component commutator theorem in that quotient excludes the
solvable branch of A.3.3(7). Thus K lies in [K,X], and normalization gives
[K,X]=K. If X is solvable, K cannot normalize X: that would put the
nonsolvable K inside X.

The relative theorem retains the literal ambient commutator and the actual
image O₂(H). It is applied to H=C_G(u), X=Ξ_p(L), and the component selected
by the preceding Fitting argument. No component model or additional
commutator premise is introduced; the later model exclusions are separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.1.12(3), printed p.874; 1.2.1(3) and A.3.3(7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect subgroup fixes every C-component in an SQTK-group. -/
theorem twoPerfect_normalizes_component (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (X K : Subgroup G) (hX : IsPPerfect 2 X) (hK : K.IsCComponent) :
    X ≤ normalizer (K : Set G) := by
  rcases Section02.component_normal_or_index_two_source hG hK with hn | hi
  · let := hn
    exact le_normalizer_of_normal
  · let N := normalizer (K : Set G)
    let : N.Normal := normal_of_index_eq_two hi
    have hp : IsPGroup 2 (G ⧸ N) := IsPGroup.of_card (n := 1) (by
      change N.index = 2 ^ 1
      simpa only [pow_one] using hi)
    exact (le_pResidual_of_isPPerfect X hX).trans
      (sInf_le ⟨inferInstance, hp⟩)

/-- A component moved outside the two-core lies in its commutator with the actor. -/
theorem moved_component_le_commutator (X K : Subgroup G)
    (hK : K.IsCComponent) (hQ : IsQuasisimple (XiQuotient K))
    (hm : ¬ ⁅K,X⁆ ≤ pCore 2 G) : K ≤ ⁅K,X⁆ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let := hQ
  have hOrd : IsComponent (G ⧸ pCore 2 G) (K.map q) :=
    ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
  have hn : ⁅K.map q,X.map q⁆ ≠ ⊥ := by
    intro he
    apply hm
    rw [← QuotientGroup.ker_mk' (pCore 2 G), ← Subgroup.map_eq_bot_iff, map_commutator]
    exact he
  have hb : K.map q ≤ ⁅K.map q,X.map q⁆ := by
    rcases hOrd.commutator_dichotomy (X.map q) with he | he
    · exact (hn he).elim
    · rw [he]
      exact le_componentOrbit _ _
  rcases hK.commutator_le_radical_or_eq_iSup_conjugates X with hs | he
  · let : Group.IsSolvable (⁅K,X⁆ : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hs)
    let : Group.IsSolvable ((⁅K,X⁆).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    have hb' : K.map q ≤ (⁅K,X⁆).map q := by rwa [map_commutator]
    exact ((XiEmbedding.component_isCComponent hOrd).not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hb'))).elim
  · rw [he]
    exact le_iSup_conjugates _ _

/-- The detected component is normalized and fully moved by the solvable radical;
it cannot normalize that radical in return. -/
theorem moved_component_properties (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (X K : Subgroup G) (hX : IsPPerfect 2 X) (hs : Group.IsSolvable X)
    (hK : K.IsCComponent) (hQ : IsQuasisimple (XiQuotient K))
    (hm : ¬ ⁅K,X⁆ ≤ pCore 2 G) :
    X ≤ normalizer (K : Set G) ∧ ⁅K,X⁆ = K ∧ ¬ K ≤ normalizer (X : Set G) := by
  have hn := twoPerfect_normalizes_component hG X K hX hK
  have he : ⁅K,X⁆ = K := le_antisymm
    (le_normalizer_iff_commutator_le_left.mp hn) (moved_component_le_commutator X K hK hQ hm)
  refine ⟨hn,he,?_⟩
  intro hnorm
  have hKX : K ≤ X := he ▸ le_normalizer_iff_commutator_le_right.mp hnorm
  let := hs
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective (inclusion_injective hKX))

/-- Apply the moved-component conclusions inside the literal source overgroup H,
retaining the ambient commutator and the image of its actual two-core. -/
theorem moved_component_properties_in (H X K : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hXH : X ≤ H)
    (hX : IsPPerfect 2 X) (hs : Group.IsSolvable X)
    (hK : K ∈ cComponentsIn H) (hQ : IsQuasisimple (XiQuotient K))
    (hm : ¬ ⁅K,X⁆ ≤ H.pCoreIn 2) :
    X ≤ normalizer (K : Set G) ∧ ⁅K,X⁆ = K ∧ ¬ K ≤ normalizer (X : Set G) := by
  let X' := X.subgroupOf H
  let K' := K.subgroupOf H
  let eX := subgroupOfEquivOfLe hXH
  let eK := subgroupOfEquivOfLe hK.1
  let eqK : XiQuotient K' ≃* XiQuotient K :=
    QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  have hQ' : IsQuasisimple (XiQuotient K') := hQ.of_mulEquiv eqK.symm
  have hpX : IsPPerfect 2 X' := hX.of_surjective eX.symm.toMonoidHom eX.symm.surjective
  let := hs
  have hsX : Group.IsSolvable X' :=
    Group.isSolvable_of_isSolvable_injective (f := eX.toMonoidHom) eX.injective
  have hm' : ¬ ⁅K',X'⁆ ≤ pCore 2 H := by
    intro hc
    apply hm
    have hh := map_mono (f := H.subtype) hc
    simpa only [K',X',pCoreIn,map_commutator,map_subgroupOf_eq_of_le hK.1,
      map_subgroupOf_eq_of_le hXH] using hh
  obtain ⟨hn,he,hnot⟩ := moved_component_properties hH X' K' hpX hsX hK.2 hQ' hm'
  refine ⟨?_,?_,?_⟩
  · have hh := (map_mono (f := H.subtype) hn).trans (K'.le_normalizer_map H.subtype)
    simpa only [X',K',map_subgroupOf_eq_of_le hK.1,map_subgroupOf_eq_of_le hXH] using hh
  · have hh := congrArg (Subgroup.map H.subtype) he
    simpa only [K',X',pCoreIn,map_commutator,map_subgroupOf_eq_of_le hK.1,
      map_subgroupOf_eq_of_le hXH] using hh
  · intro hc
    exact hnot ((comap_mono hc).trans (X.le_normalizer_comap H.subtype))

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
