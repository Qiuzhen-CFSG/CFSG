module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsFitting
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsCore
public import Theory.GroupTheory.PCoreInRestriction
/-!
# A literal outside component for the original Case-I centralizer

Combine the C.2.6 Fitting-preimage containment with A.4.4 core recovery and
the genuine quotient-component correspondence. The final theorem is stated
for G₁=C_G(Z₁), M_Z=G₁∩M_c and Q₁=O₂(M_Z), and returns an actual ambient
subgroup L with a quasisimple quotient L/O₂(L). Every subgroup and quotient
map is retained. The characteristic-normalizer control already supplies
the core-normalizer bound, so no separate assumption of that bound is needed.

Source: Aschbacher--Smith 15.1.18(2),(5),(7), 15.1.19(1),(3),(4),(6),
printed pp.1092--1093. The earlier source control and odd-core hypotheses
remain explicit; the theorem assumes no component or model witness.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
variable {G : Type*} [Group G] [Finite G]

/-- Component existence from the source radical and two normalizer controls. -/
theorem caseI_exists_component
    {κ : GroupClass} (hG : IsSQTK κ G) (M R : Subgroup G)
    (hr : IsPRadical 2 R) (hRM : R ≤ M)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (ho : pPrimeCore 2 G = ⊥) (hproper : M ≠ ⊤)
    (hn : normalizer (M.pCoreIn 2 : Set G) ≤ M)
    (hres : normalizer ((pResidual 2 M).map M.subtype : Set G) ≤ M) :
    ∃ L : Subgroup G, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧ ¬ L ≤ M :=
  caseI_exists_component_of_twoFittingCore_le M hproper hn
    (caseI_twoFittingCore_le hG M R hr hRM hcontrol ho hres)

/-- Source 15.1.19(6), with the literal centralizer and ambient subgroup maps.
The controls are genuine earlier conclusions of 15.1.18 and 15.1.19(1). -/
theorem source_caseI_15_1_19_6
    {κ : GroupClass} (M Mc Z1 : Subgroup G)
    (hG : IsSQTK κ (centralizer (Z1 : Set G)))
    (hr : IsPRadical 2 (((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).subgroupOf
      (centralizer (Z1 : Set G))))
    (hcontrol :
      (((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).subgroupOf
        (centralizer (Z1 : Set G))).characteristicNormalizerClosure ≤
          (centralizer (Z1 : Set G) ⊓ Mc).subgroupOf (centralizer (Z1 : Set G)))
    (ho : pPrimeCore 2 (centralizer (Z1 : Set G)) = ⊥)
    (hescape : ¬ M ⊓ centralizer (Z1 : Set G) ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hres : centralizer (Z1 : Set G) ⊓ normalizer
      ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
        (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤
          centralizer (Z1 : Set G) ⊓ Mc) :
    ∃ L : Subgroup G, L ≤ centralizer (Z1 : Set G) ∧
      (L.subgroupOf (centralizer (Z1 : Set G))).IsCComponent ∧
      IsQuasisimple (L ⧸ pCore 2 L) ∧ ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc := by
  let H := centralizer (Z1 : Set G)
  let MZ := H ⊓ Mc
  let B := MZ.subgroupOf H
  let R := (MZ.pCoreIn 2).subgroupOf H
  have hMZH : MZ ≤ H := inf_le_left
  have hRM : R ≤ B := comap_mono (pCoreIn_le 2 MZ)
  have hBproper : B ≠ ⊤ := by
    intro he
    have hHB : H ≤ MZ := subgroupOf_eq_top.mp he
    exact hescape (inf_le_right.trans hHB)
  have hnB : normalizer (B.pCoreIn 2 : Set H) ≤ B := by
    change normalizer ((MZ.subgroupOf H).pCoreIn 2 : Set H) ≤ B
    rw [pCoreIn_subgroupOf 2 MZ H hMZH]
    exact (normalizer_le_characteristicNormalizerClosure_self R hr.1).trans hcontrol
  have hBres : ((pResidual 2 B).map B.subtype).map H.subtype =
      (pResidual 2 MZ).map MZ.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hMZH]
  have hnres : normalizer ((pResidual 2 B).map B.subtype : Set H) ≤ B := by
    intro x hx
    apply hres
    refine ⟨x.property,?_⟩
    have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    rwa [hBres] at hm
  obtain ⟨K,hK,hq,hout⟩ := caseI_exists_component hG B R hr hRM hcontrol ho hBproper hnB hnres
  let L := K.map H.subtype
  let e : K ≃* L := equivMapOfInjective K H.subtype H.subtype_injective
  let := hq
  have hL : L ≤ H := map_subtype_le _
  refine ⟨L,hL,?_,?_,?_⟩
  · change ((K.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  · exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (pCore 2 K) (pCore 2 L) e (pCore_map_iso 2 e))
  · intro hLM
    exact hout (map_le_iff_le_comap.mp hLM)
end CFSG.Quasithin.Chapter15.Section01
