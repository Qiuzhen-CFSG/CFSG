module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.MarkedAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.LocalFamily
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The normal containing component in the fixed-line centralizer

The genuine preliminary makes S Sylow in C = C_G(Z₁). Local-family membership
and SQTK then let the full universal A.3.12/A.3.8 deduction construct a normal
containing C-component K, retaining both actual images in C/O₂(C).
The star marking identifies L/O₂(L) with PSL₄(2) through the proved A₈ model
comparison. Equality of the quotient images reflects equality of the original
components by restricting K to the local join containing O₂(C).

These are the containment and equality steps of Aschbacher–Smith,
15.3.32(3), printed pp.1132–1133; 1.2.4, p.505; A.3.12, pp.47–48.
The proper embedding alternatives still require their separate exclusion.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Section02 Chapter1.Terminal Chapter1.Terminal.LinearFourActions
universe u
variable {G : Type u} [Group G] [Finite G]

theorem componentCore_isPSL (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hm : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 4 2 :=
  ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨(componentCoreEquivEightOfModule d c P hP hc e hm).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

theorem exists_normal_containing_component {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧ NonnormalCComponentModel K)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hj : I = c.L ⊔ d.S)
    (hf : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hc : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (h11 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J) :
    let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
      ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
        (∀ D : Subgroup C, D.IsCComponent → c.L.subgroupOf C ≤ D → D = K) ∧
        A312Embedding (twoQuotientImage c.L C)
          (K.map (QuotientGroup.mk' (pCore 2 C))) := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  have hLC : c.L ≤ C := (component_le c).trans
    (overgroup_le_fixedLine_centralizer d c hj hf)
  obtain ⟨P, hP⟩ := fixedLine_centralizer_sylow d hI c hj hf hc h11
  have hSC : d.S ≤ C := hP ▸ map_subtype_le (P : Subgroup C)
  have hPeq : (P : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hP
  have hB : c.L.subgroupOf C ∈ L C P := by
    rw [hPeq]
    exact (mem_LIn_iff_subgroupOf hSC hLC).mp
      (component_mem_fixedLine_local_family d hI c hn hj hf h11)
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    (show d.S ≤ I from hj ▸ le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn)
  have hPB : (P : Subgroup C) ≤ normalizer (c.L.subgroupOf C : Set C) := by
    rw [hPeq, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono hSL
  obtain ⟨K, hK, hBK, hu, he, hnormal⟩ := lemma_1_2_4_of_A_3_12_A_3_8
    hA312 hA38 (fixedLine_centralizer_quotient_sqtk hG d hc) P hB
  exact ⟨P, hP, K, hK, hnormal hPB, hBK, hu, he⟩

omit [Finite G] in
/-- Equality of the actual two-core images forces equality before quotienting.
The ambient two-core lies in S, so the larger component restricts to the
original local join. -/
theorem eq_of_local_core_image_eq {B K : Subgroup G} (S : Sylow 2 G)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (he : B.map (QuotientGroup.mk' (pCore 2 G)) =
      K.map (QuotientGroup.mk' (pCore 2 G))) : B = K := by
  have hKB : K ≤ B ⊔ pCore 2 G := by
    have h := congrArg (comap (QuotientGroup.mk' (pCore 2 G))) he
    rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at h
    exact h ▸ le_sup_left
  have hKBS : K ≤ B ⊔ S := hKB.trans
    (sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) B)
  have heq := hB.eq_of_le (hK.subgroupOf hKBS) (comap_mono hBK)
  have h := congrArg (map (B ⊔ (S : Subgroup G)).subtype) heq
  simpa only [map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le hKBS] using h

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
