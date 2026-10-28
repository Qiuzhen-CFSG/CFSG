module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource

/-!
# The invariant Suzuki Borel on the original reduced actor

Construct the Borel in the literal component orbit K₀-star, with its full
one-factor or two-factor Suzuki marking. Its lift in K₀ is solvable and
T-invariant, so 12.6.29 puts it in M. TI at the same nonidentity point
then makes that lift normalize V and hence L₁.

Mutual normalization and the three-free Borel force L₁-star to fix the
Borel's two-core quotient. The concrete Suzuki detector excludes its
order-three field action, also on exchanged components. Two-perfectness
kills the remaining two-group action, so L₁-star centralizes K₀-star.
This constructs the Borel and action premises from the retained earlier
geometry; no theta identity from another chapter is assumed.

Source: Aschbacher--Smith 12.6.29--31, printed pp.835--836. The Borel
argument reuses the proved F.1.3(1) detector and the construction for
13.8.16, printed pp.952--953. The private ambient transport follows
Suzuki/BorelSource/Geometry.lean; the original-group application is here.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Suzuki Chapter13.Section08.Components.Suzuki.BorelSource
open Chapter15.Section03 Chapter15.Section03.Candidates.SuzukiExclusion
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

private theorem intrinsic_borel (K Y S : Subgroup G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = S) (hK : IsComponent G K) (m : ℕ) (hm : 0 < m)
    (e : K ≃* SuzukiMatrixGroup m) (hSY : S ≤ normalizer (Y : Set G))
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hYK : Y ≤ normalizer (K : Set G))
    (hindex : (normalizer (K : Set G)).index ≤ 2) :
    ∃ B : Subgroup G, B ≤ localSpan K S ∧ S ⊓ localSpan K S ≤ B ∧
      Y ⊔ S ≤ normalizer (B : Set G) ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ ∃ f : localSpan K S ≃* (Fin n → SuzukiMatrixGroup m),
        (B.subgroupOf (localSpan K S)).map f.toMonoidHom =
          pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
  let Ptop : Sylow 2 (⊤ : Subgroup G) := P.mapSurjective (f := (topEquiv (G := G)).symm.toMonoidHom)
    (topEquiv (G := G)).symm.surjective
  have hPtop : (Ptop : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = S := by
    change ((P : Subgroup G).map (topEquiv (G := G)).symm.toMonoidHom).map
      (⊤ : Subgroup G).subtype = S
    rw [map_map]
    change (P : Subgroup G).map (MonoidHom.id G) = S
    rwa [map_id]
  have hI : (normalizer (K.subgroupOf ⊤ : Set (⊤ : Subgroup G))).index ≤ 2 := by
    rw [← subgroupOf_normalizer_eq (show K ≤ ⊤ from le_top)]
    rw [subgroupOf, index_comap_of_surjective _ (topEquiv (G := G)).surjective]
    exact hindex
  obtain ⟨_, hcontains, hle, hn⟩ := suzuki_orbit_normalizer_invariance
    (I := ⊤) le_top le_top Ptop hPtop (hK.subgroupOf le_top) m hm e hSY hY hYK
  obtain ⟨n, hn', f, hf⟩ := BorelConstruction.orbitNormalizer_model
    (I := ⊤) le_top Ptop hPtop (hK.subgroupOf le_top) m hm e hI
  exact ⟨BorelConstruction.orbitNormalizer K S, hle, hcontains, hn, n, hn', f, hf⟩

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The actual orbit has an invariant, fully marked Suzuki Borel. -/
theorem SourceHypothesis.original_abelian_suzuki_borel
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :
    Nonempty (InvariantBorel H K (D.fullSetup hZ T z).L₁ T m) := by
  let E := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hLK : E.L₁ ≤ normalizer (K : Set G) := by
    have hp : IsPPerfect 2 (E.L₁.subgroupOf H) :=
      (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective
        (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
    have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source
      (S.original_star_sqtk D hZ z hz hH) hK hp
    rw [←subgroupOf_normalizer_eq hKH] at hn
    exact fun x hx => hn (show (⟨x,hLH hx⟩ : H) ∈ E.L₁.subgroupOf H from hx)
  have hO : (conjugateSpanBy K (T : Subgroup G)).subgroupOf H =
      conjugateSpanBy (K.subgroupOf H) (T.subgroupOf H) :=
    subgroupOf_conjugateSpan H K T hKH hTH
  have hnO : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).Normal := by
    rw [hO]
    exact conjugateSpanBy_sylow_normal (K.subgroupOf H) (T.subtype hTH)
      (Chapter1.Section02.proposition_1_2_1_three_orbit_source
        (S.original_star_sqtk D hZ z hz hH) hK)
  have hOH : conjugateSpanBy K (T : Subgroup G) ≤ H :=
    conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have hON : H ≤ normalizer (conjugateSpanBy K (T : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hOH).mp hnO
  have hq := S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let : IsQuasisimple (actorImage H K) := hq.of_mulEquiv (componentStarEquiv H K hKH hK)
  have hc := star_isComponent H K hK (inferInstance : IsQuasisimple (actorImage H K))
  have hi : (normalizer (actorImage H K : Set (H ⧸ pCore 2 H))).index ≤ 2 := by
    by_cases hn : (K.subgroupOf H).Normal
    · let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
      simp only [normalizer_eq_top,index_top]
      decide
    · exact le_of_eq (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz
        hbound hTI hns hH hKH hK hgen hn).1
  let P := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have ho : actorImage H (conjugateSpanBy K (T : Subgroup G)) =
      localSpan (actorImage H K) (actorImage H T) :=
    star_conjugateSpan H K T hKH hTH
  obtain ⟨B,hB,hcontains,hn,n,hn',e,he⟩ := intrinsic_borel
    (actorImage H K) (actorImage H E.L₁) (actorImage H T) P rfl hc m hm
    ((componentStarEquiv H K hKH hK).symm.trans eK)
    (starImage_normalizes H E.L₁ T hTL)
    (S.original_point_residual_star_twoThree D hZ z hz hTz hH)
    (starImage_normalizes H K E.L₁ hLK) hi
  have he' : ∃ f : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
      (Fin n → SuzukiMatrixGroup m),
      (B.subgroupOf (actorImage H (conjugateSpanBy K (T : Subgroup G)))).map f.toMonoidHom =
        pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
    rw [ho]
    exact ⟨e,he⟩
  obtain ⟨f,hf⟩ := he'
  refine ⟨{
    borel := B
    le_orbit := by
      change B ≤ actorImage H (conjugateSpanBy K (T : Subgroup G))
      rwa [ho]
    contains_sylow := by
      change actorImage H T ⊓ actorImage H (conjugateSpanBy K (T : Subgroup G)) ≤ B
      rwa [ho]
    orbit_normalized := (sup_le hLH hTH).trans hON
    normalized := ?_
    factors := n
    factors_one_or_two := hn'
    equiv := f
    borel_map := hf }⟩
  change actorImage H (E.L₁ ⊔ (T : Subgroup G)) ≤ _
  simpa only [actorImage,subgroupOf_sup hLH hTH,Subgroup.map_sup] using hn

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The Borel two-core quotient detects the original point residual's
whole action, including field actions on exchanged components. -/
theorem SourceHypothesis.original_abelian_suzuki_residual_centralizes
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :
    actorImage H (D.fullSetup hZ T z).L₁ ≤
      centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) : Set (H ⧸ pCore 2 H)) := by
  let E := D.fullSetup hZ T z
  let K₀ := conjugateSpanBy K (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hOH : K₀ ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  obtain ⟨b⟩ := S.original_abelian_suzuki_borel D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hm eK
  let B := Swapped.LinearTwo.borelLift H K₀ hOH b.borel
  have hBO : B ≤ K₀ := Swapped.LinearTwo.borelLift_le _ _ _ _
  have hBH : B ≤ H := hBO.trans hOH
  have hstar : actorImage H B = b.borel :=
    Swapped.LinearTwo.borelLift_starImage _ _ _ _ b.le_orbit
  have hn : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) :=
    Swapped.LinearTwo.borelLift_normalized _ _ _ hOH (sup_le hLH hTH) _
      b.orbit_normalized b.normalized
  let : Group.IsSolvable b.borel := b.solvable hm
  have hBsol : Group.IsSolvable B := Swapped.LinearTwo.borelLift_solvable _ _ _ _
  have hBM : B ≤ M L := by
    apply borel_le_of_solvable_exclusion ⊥ (T : Subgroup G) H (M L) B
    · intro J hTJ _ hsol
      let := hsol
      exact S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns
        (by simpa only [bot_sup_eq] using hTJ)
    · exact hBsol
    · rw [bot_sup_eq]
      let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
      infer_instance
    · simpa only [bot_sup_eq] using le_sup_right.trans hn
    · exact hBH
    · simpa only [bot_sup_eq] using hTH
  have hBNV : B ≤ normalizer (V : Set G) := by
    intro x hx
    apply Mv_le_module_normalizer_of_TI hTI z hz
    refine ⟨hBM hx,?_⟩
    have hh := hH.2.1 (hBH hx)
    rwa [E.Gz_eq] at hh
  have hBL : B ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hBH hBNV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  apply centralizes_of_mutual_normalization b.le_orbit (b.detects hm)
    (S.original_point_residual_star_twoPerfect D hZ z hH)
    (S.original_point_residual_star_twoThree D hZ z hz hTz hH)
  · exact starImage_normalizes H K₀ E.L₁ (le_sup_left.trans b.orbit_normalized)
  · exact b.three_free hm
  · have hh := starImage_normalizes H B E.L₁ (le_sup_left.trans hn)
    change actorImage H E.L₁ ≤ normalizer (actorImage H B : Set (H ⧸ pCore 2 H)) at hh
    rwa [hstar] at hh
  · have hh := starImage_normalizes H E.L₁ B hBL
    change actorImage H B ≤ normalizer (actorImage H E.L₁ : Set (H ⧸ pCore 2 H)) at hh
    rwa [hstar] at hh

end CFSG.Quasithin.Chapter12.Section06
