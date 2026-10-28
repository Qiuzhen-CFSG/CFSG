module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.SourceCases

/-!
# The genuine E.2.2 cases for right-factor selection

The actual H-star member is a minimal parabolic; its unique maximal
subgroup over T is N_G(L) ∩ H. The proved binary E.2.2 dispatcher supplies
a generating original C-component, its quasisimple two-core quotient,
and either the Bender or diagram marking in the distinct solvable-core
quotient. The exponent exceeds one without asserting equality with n(H).

These source alternatives are inputs to the remaining selection proofs.
They do not identify the marked image with the quotient by O₂ of the
right factor or assert that the whole residual is the right factor.

Source: Aschbacher--Smith E.2.2, pp.215--216, and 5.1.10, p.634.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
variable {G : Type*} [Group G] [Finite G]

/-- The genuine exchanged or single Bender row of E.2.2 on the original H.
The model is explicitly in H/core_H(M), and has not yet been transported
to the quotient by the two-core of a selected factor. -/
@[expose] def RightRankOneSource (T : Sylow 2 G) (L H : Subgroup G) : Prop :=
  ∃ (C : Subgroup H) (f : ℕ), C.IsCComponent ∧
    IsQuasisimple (C ⧸ pCore 2 C) ∧
    C ⊔ (T : Subgroup G).subgroupOf H = ⊤ ∧ 1 < f ∧
    ((ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
        ((T : Subgroup G).subgroupOf H) ∧
      ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) ∨
     (SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
        ((T : Subgroup G).subgroupOf H) ∧
      BenderModel ((normalizer (L : Set G)).subgroupOf H) C f))

/-- The genuine rank-two diagram row, with its central kernel, Borel and
the same marking for the action on the two parabolic classes. -/
@[expose] def RightDiagramSource (T : Sylow 2 G) (L H : Subgroup G) : Prop :=
  ∃ (C : Subgroup H) (f : ℕ), C.IsCComponent ∧
    IsQuasisimple (C ⧸ pCore 2 C) ∧
    C ⊔ (T : Subgroup G).subgroupOf H = ⊤ ∧ 1 < f ∧
    SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) ∧
    DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f

/-- The earlier E.2.2 theorem supplies the two model branches needed by
right-factor selection. No numerical equality across the solvable kernel is used. -/
theorem right_source_cases {T : Sylow 2 G} {L H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) :
    RightRankOneSource T L H ∨ RightDiagramSource T L H := by
  let hP := hstar_minimalParabolic_of_generation_gt_one hTL hH hgen
  obtain ⟨C,f,hC,hqs,hjoin,hf,hcases⟩ := source_binary_cases_generating_knownSimple
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) (T.subtype hH.1.1.2) hP hgen
  have hmax : ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H := by
    let J := ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP
    have hj := ChapterB.minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
    have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
      have hh := map_mono (f := H.subtype) hj.2
      change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    have hJH : J.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hj.1.lt_top
      simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
    apply ChapterE.Section06.FixedPointBounds.ParabolicCartan.maximal_eq_overlap_of_image_le
      H.subtype (T.subtype hH.1.1.2) hP
    · change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ normalizer (L : Set G)
      rw [map_subgroupOf_eq_of_le hH.1.1.2]
      exact hTL
    · simpa only [range_subtype] using hH.1.2
    · exact Chapter3.HStar.proper_overgroup_le T hH hTJ hJH
  rw [hmax] at hcases
  cases hcases with
  | exchanged hc hm => exact Or.inl ⟨C,f,hC,hqs,hjoin,hf,Or.inl ⟨hc,hm⟩⟩
  | bender hc hm => exact Or.inl ⟨C,f,hC,hqs,hjoin,hf,Or.inr ⟨hc,hm⟩⟩
  | diagram hc hm => exact Or.inr ⟨C,f,hC,hqs,hjoin,hf,hc,hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
