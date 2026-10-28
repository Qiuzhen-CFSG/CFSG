module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Containing
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.J2SimpleModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.J2CoverModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
/-!
# Lifting a normalized local J₂ section without A.3.12

The containing component exists and is normal by the proved unique
containment theorem over known simple groups. Its two-core image is
quasisimple. The complete simple-carrier inspection forces equality,
and the central-cover inspection eliminates all nonsimple covers.
Equality of the images lifts by maximality of the original local
C-component in its join with the same Sylow subgroup.

Thus the original local J₂ seed itself is a normal C-component; no
proper-embedding classification callback is used.
Source: Aschbacher–Smith A.3.12 and 1.2.4, pp.47–48,505;
the actual exceptional application is 13.6.27, p.934.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Equality with the actual containing component in the two-core-free group. -/
theorem eq_of_jankoTwo_containing_component
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier)) : B = K := by
  let : IsQuasisimple K := containing_quasisimple hG hO T hB hK hBK (Or.inl h)
  obtain ⟨S, _, hl, hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  obtain ⟨e⟩ := h
  have hsmall : Nonempty (((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) ≃*
      Sporadic.LeechRelated.J2.Carrier) :=
    ⟨(QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK))).trans e⟩
  rcases quasisimple_containing_component_models_knownSimple hG hO hK with
    ⟨hs, hm⟩ | ⟨_, hm⟩
  · let : IsSimpleGroup K := hs
    have he := eq_top_of_jankoTwo_theoremC S (B.subgroupOf K) hl hn hsmall hm
    exact le_antisymm hBK (subgroupOf_eq_top.mp he)
  · exact (not_threeCover_of_jankoTwo S hl hn hsmall hm).elim

private noncomputable def imageCoreEquiv (B : Subgroup G) :
    (B ⧸ pCore 2 B) ≃* ((B.map (QuotientGroup.mk' (pCore 2 G))) ⧸
      pCore 2 (B.map (QuotientGroup.mk' (pCore 2 G)))) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  apply MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  rw [ker_subgroupMap, QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_subtype

/-- The literal original local J₂ subgroup is already a normal ambient
C-component. The full known-simple catalogue supplies all earlier inputs. -/
theorem jankoTwo_local_isCComponent_normal
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ Chapter1.L G S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    B.IsCComponent ∧ B.Normal := by
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
  obtain ⟨e⟩ := h
  have hsmall : Nonempty (((B.map q) ⧸ pCore 2 (B.map q)) ≃*
      Sporadic.LeechRelated.J2.Carrier) := ⟨(imageCoreEquiv B).symm.trans e⟩
  have he := eq_of_jankoTwo_containing_component hQ (pCore_quotient_pCore_eq_bot 2)
    Sbar hBbar (hK.map_quotient _) (map_mono hBK) hnbar hsmall
  have hKB : K ≤ B ⊔ pCore 2 G := by
    have hh := map_le_iff_le_comap.mp he.ge
    simpa only [q, comap_map_eq, QuotientGroup.ker_mk'] using hh
  have hKS : K ≤ B ⊔ S := hKB.trans
    (sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) B)
  have hh := hB.1.eq_of_le (hK.subgroupOf hKS) (comap_mono hBK)
  have hm := congrArg (map (B ⊔ S).subtype) hh
  have heq : B = K := by
    simpa only [map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le hKS] using hm
  exact heq.symm ▸ ⟨hK, hKn⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
