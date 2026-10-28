module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNormalized
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource

/-!
# The full Suzuki Borel in an original local

Construct the invariant Borel of the actual Sylow orbit of a Suzuki
component, retaining its one- or two-factor matrix marking. Its solvable
lift lies in the original normalizer by 14.7.29 and normalizes L₁.
The intrinsic Suzuki automorphism detector then makes L₁* centralize
the entire orbit. No A₆ setup or theta identity is assumed: point
normalization comes from the original L₃(2) flag and the solvable lift.

Source: Aschbacher–Smith, the Borel argument in 14.7.32–33,
printed p.1056, refs/quasithin.pdf. The final exclusion is in SuzukiExclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components
open BenderSuzuki.MatrixGroups
open Chapter15.Section03
open Chapter15.Section03.Candidates.SuzukiExclusion
open Suzuki.BorelSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem intrinsic_suzuki_borel {D : Type*} [Group D] [Finite D]
    (K Y S : Subgroup D) (P : Sylow 2 D)
    (hP : (P : Subgroup D) = S) (hK : IsComponent D K) (m : ℕ) (hm : 0 < m)
    (e : K ≃* SuzukiMatrixGroup m) (hSY : S ≤ normalizer (Y : Set D))
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hYK : Y ≤ normalizer (K : Set D))
    (hindex : (normalizer (K : Set D)).index ≤ 2) :
    ∃ B : Subgroup D, B ≤ localSpan K S ∧ S ⊓ localSpan K S ≤ B ∧
      Y ⊔ S ≤ normalizer (B : Set D) ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ ∃ f : localSpan K S ≃* (Fin n → SuzukiMatrixGroup m),
        (B.subgroupOf (localSpan K S)).map f.toMonoidHom =
          pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
  let Ptop : Sylow 2 (⊤ : Subgroup D) := P.mapSurjective (f := (topEquiv (G := D)).symm.toMonoidHom)
    (topEquiv (G := D)).symm.surjective
  have hPtop : (Ptop : Subgroup (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = S := by
    change ((P : Subgroup D).map (topEquiv (G := D)).symm.toMonoidHom).map
      (⊤ : Subgroup D).subtype = S
    rw [map_map]
    change (P : Subgroup D).map (MonoidHom.id D) = S
    rwa [map_id]
  have hI : (normalizer (K.subgroupOf ⊤ : Set (⊤ : Subgroup D))).index ≤ 2 := by
    rw [← subgroupOf_normalizer_eq (show K ≤ ⊤ from le_top)]
    rw [subgroupOf, index_comap_of_surjective _ (topEquiv (G := D)).surjective]
    exact hindex
  obtain ⟨_, hcontains, hle, hn⟩ := suzuki_orbit_normalizer_invariance
    (I := ⊤) le_top le_top Ptop hPtop (hK.subgroupOf le_top) m hm e hSY hY hYK
  obtain ⟨n, hn', f, hf⟩ := BorelConstruction.orbitNormalizer_model
    (I := ⊤) le_top Ptop hPtop (hK.subgroupOf le_top) m hm e hI
  exact ⟨BorelConstruction.orbitNormalizer K S, hle, hcontains, hn, n, hn', f, hf⟩

/-- The original local has an invariant full Borel in its one- or two-factor
Suzuki orbit. Both the Sylow and point actions are the literal quotient images. -/
theorem local_suzuki_invariantBorel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    {m : ℕ} (hm : 0 < m) (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :
    Nonempty (InvariantBorel I K (F.Li L 1) (T : Subgroup G) m) := by
  let N := conjugateSpanBy K (T : Subgroup G)
  have hTI := F.sylow_le_of_mem_Hz hI
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hbase := sup_le hLI hTI
  have hNI : N ≤ I := conjugateSpanBy_le hKI (hTI.trans I.le_normalizer)
  have hnN : (N.subgroupOf I).Normal := by
    have he : N = (conjugateSpanBy (K.subgroupOf I) ((T : Subgroup G).subgroupOf I)).map I.subtype := by
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hKI,map_subgroupOf_eq_of_le hTI]
    rw [he,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective]
    exact local_component_sylow_span_normal h I hI (K.subgroupOf I) hK
  have hIN := (normal_subgroupOf_iff_le_normalizer hNI).mp hnN
  have hindex : (normalizer (K.subgroupOf I : Set I)).index ≤ 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple (local_star_sqtk h I hI) hK with hn | hi
    · let := hn
      simp only [normalizer_eq_top,index_top]
      decide
    · omega
  have hLK : F.Li L 1 ≤ normalizer (K : Set G) := by
    apply Chapter15.Section03.ComponentIntersection.normalizes_of_index_le_two hLI
      (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _)
    change ((normalizer (K : Set G)).subgroupOf I).index ≤ 2
    rw [subgroupOf_normalizer_eq hKI]
    exact hindex
  have hTL : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) :=
    ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural)
  have hL3 : IsPGroup 3 ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_core_quotient_card (F := F) h structural)
  let B := Chapter13.Section08.Source.starImage I K
  let Y := Chapter13.Section08.Source.starImage I (F.Li L 1)
  let S := Chapter13.Section08.Source.starImage I (T : Subgroup G)
  let P : Sylow 2 (HStar I) := (T.subtype hTI).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  have hB : IsComponent (HStar I) B :=
    local_component_star_isComponent h hab structural previous faithful I hI (K.subgroupOf I) hK
  have hi : (normalizer (B : Set (HStar I))).index ≤ 2 := by
    let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
    rw [show B = (K.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) from rfl,
      cComponent_normalizer_index_quotient hK (pCore 2 I)]
    exact hindex
  have horbit : Chapter13.Section08.Source.starImage I N = localSpan B S := by
    change ((conjugateSpanBy K (T : Subgroup G)).subgroupOf I).map _ = _
    have he : (conjugateSpanBy K (T : Subgroup G)).subgroupOf I =
        conjugateSpanBy (K.subgroupOf I) ((T : Subgroup G).subgroupOf I) := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le hNI,map_conjugateSpanBy,
        map_subgroupOf_eq_of_le hKI,map_subgroupOf_eq_of_le hTI]
    rw [he,map_conjugateSpanBy]
    rfl
  obtain ⟨B₀,hB₀,hcontains,hn,n,hn',e,he⟩ := intrinsic_suzuki_borel B Y S P rfl hB m hm
    ((componentStarEquiv I K hKI hK).symm.trans eK)
    (starImage_normalizes I (F.Li L 1) (T : Subgroup G) hTL)
    (starImage_three_quotient I (F.Li L 1) hLI hL3)
    (starImage_normalizes I K (F.Li L 1) hLK) hi
  have hsup : Chapter13.Section08.Source.starImage I (F.Li L 1 ⊔ (T : Subgroup G)) = Y ⊔ S := by
    rw [Chapter13.Section08.Source.starImage,subgroupOf_sup hLI hTI,Subgroup.map_sup]
    rfl
  have hmodel : ∃ f : Chapter13.Section08.Source.starImage I N ≃* (Fin n → SuzukiMatrixGroup m),
      (B₀.subgroupOf (Chapter13.Section08.Source.starImage I N)).map f.toMonoidHom =
        pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
    rw [horbit]
    exact ⟨e,he⟩
  obtain ⟨f,hf⟩ := hmodel
  exact ⟨{ borel := B₀
           le_orbit := horbit.symm ▸ hB₀
           contains_sylow := horbit.symm ▸ hcontains
           orbit_normalized := hbase.trans hIN
           normalized := hsup.symm ▸ hn
           factors := n
           factors_one_or_two := hn'
           equiv := f
           borel_map := hf }⟩

/-- Source 14.7.29 places the full invariant Borel lift in M. Its reverse
normalization of L₁ and the genuine Suzuki detector force L₁* to centralize
the entire component orbit, including when the Sylow subgroup exchanges it. -/
theorem local_suzuki_point_centralizes_orbit
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    {m : ℕ} (hm : 0 < m) (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :
    Chapter13.Section08.Source.starImage I (F.Li L 1) ≤
      centralizer (Chapter13.Section08.Source.starImage I (conjugateSpanBy K (T : Subgroup G)) : Set (HStar I)) := by
  obtain ⟨b⟩ := local_suzuki_invariantBorel h hab structural previous faithful I K hI hKI hK hm eK
  let N := conjugateSpanBy K (T : Subgroup G)
  have hNI : N ≤ I := conjugateSpanBy_le hKI ((F.sylow_le_of_mem_Hz hI).trans I.le_normalizer)
  have hbase := sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  let B₀ := Swapped.LinearTwo.borelLift I N hNI b.borel
  have hB₀I : B₀ ≤ I := (Swapped.LinearTwo.borelLift_le _ _ _ _).trans hNI
  have hnorm : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B₀ : Set G) :=
    Swapped.LinearTwo.borelLift_normalized I N _ hNI hbase b.borel b.orbit_normalized b.normalized
  let : Group.IsSolvable b.borel := b.solvable hm
  have hsol : Group.IsSolvable B₀ := Swapped.LinearTwo.borelLift_solvable _ _ _ _
  have hBL : B₀ ≤ normalizer (F.Li L 1 : Set G) :=
    point_normalized_solvable_normalizes_point d h hab structural previous faithful earlier
      B₀ (hB₀I.trans hI.2.1) hsol hnorm
  have hmap : Chapter13.Section08.Source.starImage I B₀ = b.borel :=
    Swapped.LinearTwo.borelLift_starImage _ _ _ _ b.le_orbit
  have hL3 : IsPGroup 3 ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_core_quotient_card (F := F) h structural)
  apply centralizes_of_mutual_normalization b.le_orbit (b.detects hm)
    (starImage_twoPerfect I (F.Li L 1) (F.Li_one_le_of_mem_Hz hI)
      (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _))
    (starImage_three_quotient I (F.Li L 1) (F.Li_one_le_of_mem_Hz hI) hL3)
    (starImage_normalizes I N (F.Li L 1) (le_sup_left.trans b.orbit_normalized))
    (b.three_free hm)
  · exact (map_mono (subgroupOf_mono I (show F.Li L 1 ≤ F.Li L 1 ⊔ (T : Subgroup G) from le_sup_left))).trans b.normalized
  · rw [←hmap]
    exact starImage_normalizes I (F.Li L 1) B₀ hBL


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
