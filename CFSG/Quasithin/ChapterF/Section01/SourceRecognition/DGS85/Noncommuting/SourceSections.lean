module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ReciprocalIndices
public import Theory.Representation.BinaryConjugationSection.SylowGeneration
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Literal source applications for the opening of DGS7.1

These applications keep the vertex two-cores, the distinct local actors,
the full local kernels, and the actual conjugation-section coordinates.
They prove reverse kernel escape, quadraticity, reciprocal index equality,
and the strict recognition estimates from the preceding local Sylow and
quadratic-module estimates. The Sylow-center section is proved to satisfy
the review's fixed-space-generation correction, also for the intermediate
normal actor using6.2(a)'s two-residual containment.

Source: DGS, *Groups and Graphs* (1985),3.8,6.2,7.1, especially printed
p.126; Stroth's review correction to5.12. `qt-dgs85-setup-obstruction`
owns the graph realization and the earlier local Sylow/residual premises;
`qt-dgs85-quadratic-modules` owns the lower estimates. SL2 recognition,
natural-module identification and the Chapter7 distance bound are further
obligations of this same noncommuting owner, not conclusions of this file.
-/

public section

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
variable {G : Type*} [Group G]

private theorem local_core_normalized (P : Subgroup G) :
    P ≤ normalizer (P.pCoreIn 2 : Set G) := by
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 P).le_normalizer_map P.subtype

/-- The actual two-core Sylow in the full local kernel suffices for reverse
escape. The ambient completion and the kernel may both have odd-order elements. -/
theorem critical_center_escapes_local_kernel
    (P U Z Z' : Subgroup G) (hUP : U ≤ P) (hZ' : IsPGroup 2 Z')
    (hS : Stellmacher.IsSylowSubgroupIn (P.pCoreIn 2) U)
    (hc : P.pCoreIn 2 ≤ centralizer (Z : Set G)) (hne : ⁅Z,Z'⁆ ≠ ⊥) :
    ¬ Z' ≤ U := by
  have hQU : P.pCoreIn 2 ≤ U := by
    obtain ⟨S,hS⟩ := hS
    exact hS ▸ map_subtype_le (S : Subgroup U)
  exact not_le_kernel_of_noncommuting Z Z' U (P.pCoreIn 2) hZ' hQU
    (hUP.trans (local_core_normalized P)) hS hc hne

/-- The corrected5.12 generation premise for the precise7.1 section:
`Z_delta / Omega_1(Z(L_delta))`, acted on through `L_delta / O_2(G_delta)`.
Here the type G is the finite vertex stabilizer, not the ambient completion. -/
theorem source_centerSection_generated [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (L ⧸ (pCore 2 G).subgroupOf L) W)
    (d : BinaryConjugationSection L
      (⨆ P : Sylow 2 G, Stellmacher.omegaOneCenterAmbient (P : Subgroup G))
      (Stellmacher.omegaOneCenterAmbient L)
      (σ.comp (QuotientGroup.mk' ((pCore 2 G).subgroupOf L)))) :
    (fixedConjugateSpan σ
      (((T.subtype hTL : Sylow 2 L) : Subgroup L).map
        (QuotientGroup.mk' ((pCore 2 G).subgroupOf L)))).toSubmodule = ⊤ := by
  exact sylow_span_normal_section_generated L _ _ T hTL σ _ d rfl

/-- Apply the reciprocal argument to the literal endpoint two-core quotients.
The Sylow-centralizer conclusions of6.2 supply the intersection identities;
mutual local placement supplies quadraticity. The only numerical inputs are
the two corrected5.12(a) estimates, whose producer is the quadratic-module
family. This does not yet assert the recognition or distance conclusions. -/
theorem source_core_quotient_reciprocal
    (P₀ P₁ L₀ L₁ Z₀ Z₁ : Subgroup G) [Finite P₀] [Finite P₁]
    [IsElementaryAbelian 2 Z₀] [IsElementaryAbelian 2 Z₁]
    [((P₀.pCoreIn 2).subgroupOf L₀).Normal]
    [((P₁.pCoreIn 2).subgroupOf L₁).Normal]
    {W₀ W₁ : Type*} [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (L₀ ⧸ (P₀.pCoreIn 2).subgroupOf L₀) W₀)
    (σ₁ : Representation (ZMod 2) (L₁ ⧸ (P₁.pCoreIn 2).subgroupOf L₁) W₁)
    (d₀ : BinaryConjugationSection L₀ Z₀ (Stellmacher.omegaOneCenterAmbient L₀)
      (σ₀.comp (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))))
    (d₁ : BinaryConjugationSection L₁ Z₁ (Stellmacher.omegaOneCenterAmbient L₁)
      (σ₁.comp (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))))
    (hL₀ : L₀ ≤ P₀) (hL₁ : L₁ ≤ P₁)
    (h₁₀ : Z₁ ≤ L₀) (h₀₁ : Z₀ ≤ L₁)
    (hQ₀ : P₀.pCoreIn 2 ≤ L₀) (hQ₁ : P₁.pCoreIn 2 ≤ L₁)
    (hQC₀ : P₀.pCoreIn 2 ≤ centralizer (Z₀ : Set G))
    (hQC₁ : P₁.pCoreIn 2 ≤ centralizer (Z₁ : Set G))
    (hS₀ : Stellmacher.IsSylowSubgroupIn (P₀.pCoreIn 2) (L₀ ⊓ centralizer (Z₀ : Set G)))
    (hS₁ : Stellmacher.IsSylowSubgroupIn (P₁.pCoreIn 2) (L₁ ⊓ centralizer (Z₁ : Set G)))
    (hne : ⁅Z₀,Z₁⁆ ≠ ⊥)
    (hb₀ : Nat.card ((Z₁.subgroupOf L₀).map (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))) ≤
      Nat.card (W₀ ⧸ fixedSpace σ₀ ((Z₁.subgroupOf L₀).map
        (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀)))))
    (hb₁ : Nat.card ((Z₀.subgroupOf L₁).map (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))) ≤
      Nat.card (W₁ ⧸ fixedSpace σ₁ ((Z₀.subgroupOf L₁).map
        (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))))) :
    let A₀ := (Z₁.subgroupOf L₀).map (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))
    let A₁ := (Z₀.subgroupOf L₁).map (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))
    IsQuadratic σ₀ A₀ ∧ IsQuadratic σ₁ A₁ ∧
      Nat.card A₀ = Nat.card A₁ ∧
      Nat.card (W₀ ⧸ fixedSpace σ₀ A₀) = Nat.card A₀ ∧
      Nat.card (W₁ ⧸ fixedSpace σ₁ A₁) = Nat.card A₁ ∧
      Nat.card (W₀ ⧸ fixedSpace σ₀ A₀) < Nat.card A₀ ^ 2 ∧
      Nat.card (W₁ ⧸ fixedSpace σ₁ A₁) < Nat.card A₁ ^ 2 := by
  let : Finite Z₀ := Finite.of_injective (inclusion (d₀.section_le.trans hL₀))
    (inclusion_injective _)
  let : Finite Z₁ := Finite.of_injective (inclusion (d₁.section_le.trans hL₁))
    (inclusion_injective _)
  have hc₀ := inf_centralizer_eq_inf_core L₀ (P₀.pCoreIn 2) Z₀ Z₁
    (IsElementaryAbelian.isPGroup 2 Z₁) h₁₀ hQ₀ hQC₀
    (hL₀.trans (local_core_normalized P₀)) hS₀
  have hc₁ := inf_centralizer_eq_inf_core L₁ (P₁.pCoreIn 2) Z₁ Z₀
    (IsElementaryAbelian.isPGroup 2 Z₀) h₀₁ hQ₁ hQC₁
    (hL₁.trans (local_core_normalized P₁)) hS₁
  have hq := critical_sections_quadratic L₀ L₁ Z₀ Z₁ _ _ σ₀ _ σ₁ _ d₀ d₁ h₁₀ h₀₁
  have hi := reciprocal_section_indices L₀ L₁ (P₀.pCoreIn 2) (P₁.pCoreIn 2) Z₀ Z₁ _ _
    σ₀ _ σ₁ _ d₀ d₁ h₁₀ h₀₁ (QuotientGroup.ker_mk' _) (QuotientGroup.ker_mk' _)
    hc₀ hc₁ hne hb₀ hb₁
  exact ⟨hq.1,hq.2,hi.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
open Subgroup Representation Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G]

/-- The intermediate normal actor in7.1 need only contain the two-residual,
as supplied by6.2(a). Its Sylow is the actual intersection with the original
Sylow, and generation is proved for the same specified quotient section. -/
theorem source_intermediateSection_generated
    (L C : Subgroup G) [L.Normal] (hres : pResidual 2 G ≤ L) (S : Sylow 2 G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (L ⧸ (pCore 2 G).subgroupOf L) W)
    (d : BinaryConjugationSection L
      (⨆ P : Sylow 2 G, Stellmacher.omegaOneCenterAmbient (P : Subgroup G)) C
      (σ.comp (QuotientGroup.mk' ((pCore 2 G).subgroupOf L)))) :
    ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = (S : Subgroup G) ⊓ L ∧
      (fixedConjugateSpan σ
        ((T.mapSurjective (QuotientGroup.mk'_surjective ((pCore 2 G).subgroupOf L))) :
          Subgroup (L ⧸ (pCore 2 G).subgroupOf L))).toSubmodule = ⊤ := by
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal L
  have hm : (T : Subgroup L).map L.subtype = (S : Subgroup G) ⊓ L := by
    rw [hT, subgroupOf_map_subtype]
  have hLS : L ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    exact sup_le_sup hres le_rfl
  refine ⟨T,hm,?_⟩
  exact sylow_span_supplement_section_generated L _ C S hLS T
    (hm.le.trans inf_le_left) σ _ d rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
