module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Containing
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.CoverModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.J2Containing
/-!
# The actual exceptional component lift with the remaining J₄ row

Unique containment and normality are already proved over the full known-simple
catalogue. In the two-core quotient the containing component is quasisimple;
all central covers are excluded, and the actual simple catalogue leaves
equality, J₂, M₂₃ or J₄. Equality lifts to the original subgroup by its
local C-component maximality. All quotient models are intrinsic to the
same containing component. The remaining J₄ output is explicit.

Source: Aschbacher–Smith A.3.12 and 1.2.4, pp.47–48,505;
its exceptional source consumer is 13.6.27, p.934.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual containing component, with every central-cover case discharged. -/
theorem containing_models_of_core_eq_bot
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) :
    B = K ∨ Nonempty (K ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (K ≃* Sporadic.Mathieu.M23) ∨ Nonempty (K ≃* Janko4.Model) := by
  let : IsQuasisimple K := containing_quasisimple hG hO T hB hK hBK h
  obtain ⟨S, _, hl, hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  have hsmall : IsModel ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) :=
    h.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK)))
  rcases quasisimple_containing_component_models_knownSimple hG hO hK with
    ⟨hs, hm⟩ | ⟨hc, hm⟩
  · let : IsSimpleGroup K := hs
    rcases simple_models S (B.subgroupOf K) hl hn hsmall hm with he | hm
    · exact Or.inl (le_antisymm hBK (subgroupOf_eq_top.mp he))
    · exact Or.inr hm
  · exact (not_threeCover S hl hn hsmall hc hm).elim

private noncomputable def sectionImageEquiv (B : Subgroup G) :
    (B ⧸ pCore 2 B) ≃* ((B.map (QuotientGroup.mk' (pCore 2 G))) ⧸
      pCore 2 (B.map (QuotientGroup.mk' (pCore 2 G)))) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  apply MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  rw [ker_subgroupMap, QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_subtype

/-- The complete proved exceptional lift. A J₄ quotient remains explicit,
while all equality and acceptable enlarged exceptional rows are constructed. -/
theorem exists_normal_containing_models
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ Chapter1.L G S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) :
    ∃ K : Subgroup G, K.IsCComponent ∧ K.Normal ∧ B ≤ K ∧
      (B = K ∨ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  obtain ⟨K, ⟨hK, hBK, hKn⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ S hB hn
  let q := QuotientGroup.mk' (pCore 2 G)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hBbar : B.map q ∈ localCComponents Sbar := by
    simpa only [Sbar, q, Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB
  have hnbar : (Sbar : Subgroup (G ⧸ pCore 2 G)) ≤ normalizer (B.map q : Set _) :=
    (map_mono hn).trans (le_normalizer_map q)
  have hsmall : IsModel ((B.map q) ⧸ pCore 2 (B.map q)) :=
    h.of_equiv (sectionImageEquiv B).symm
  have he := containing_models_of_core_eq_bot hQ (pCore_quotient_pCore_eq_bot 2)
    Sbar hBbar (hK.map_quotient _) (map_mono hBK) hnbar hsmall
  refine ⟨K, hK, hKn, hBK, ?_⟩
  rcases he with he | hJ | hM | hJ4
  · have hKB : K ≤ B ⊔ pCore 2 G := by
      have hh := map_le_iff_le_comap.mp he.ge
      simpa only [q, comap_map_eq, QuotientGroup.ker_mk'] using hh
    have hKS : K ≤ B ⊔ S := hKB.trans
      (sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) B)
    have hh := hB.1.eq_of_le (hK.subgroupOf hKS) (comap_mono hBK)
    have hm := congrArg (map (B ⊔ S).subtype) hh
    exact Or.inl (by
      simpa only [map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le hKS] using hm)
  · exact Or.inr (Or.inl ⟨(cComponentTwoCoreQuotientEquiv hK).trans hJ.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(cComponentTwoCoreQuotientEquiv hK).trans hM.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(cComponentTwoCoreQuotientEquiv hK).trans hJ4.some⟩))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
