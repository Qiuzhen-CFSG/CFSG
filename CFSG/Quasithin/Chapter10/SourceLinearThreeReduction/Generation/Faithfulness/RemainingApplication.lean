module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Remainder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.MovingThompson

/-!
# Applying the B-only remainder to the original Hall kernel

Covering uniqueness, the nontrivial-two-core exclusion and all shared
Theorem C exclusions now leave only the explicit B-only catalogue for the
actual escaping normal component. All maps use the original Hall subgroup,
its elementary kernel actor and the unchanged full module. Local Thompson
movement discharges the module-fixation premise in the second application.

The B-only exclusions and quiet-branch generation remain with the source
assembly; no unconditional Hall-faithfulness theorem is asserted.
Source: Aschbacher--Smith 4.4.3,4.4.10--14 and10.2.3(2),
printed pp.619--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal escaping Hall kernel has an actual normal component in the
remaining B-only families, retaining its full center and moved module. -/
theorem source_hstar_hall_kernel_escaping_component_remaining_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥)
    (hfix : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.fullModule.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ SourceHallNormalizerRemainder (K ⧸ center K) := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel⟩ :=
    source_hstar_hall_kernel_escaping_normal_component D hn hH hlarge hP d hk hfix
  let : Fact p.Prime := ⟨hp⟩
  let := hKn
  let := hAe
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,hcard⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hcard]
    exact ho.pow
  have hAV := (le_inf hAY hAC).trans hfix
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn ho A
    (IsElementaryAbelian.isPGroup p A) hAC hAV hAT
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,
    source_nonnormal_oddNormalizer_remaining_models D hn A hAC hodd hAV hu K hK houtK hcK hmodel⟩

/-- In the moving-Thompson branch the remaining-model reduction needs no
module-fixation callback. -/
theorem source_hstar_hall_kernel_remaining_models_of_local_thompson
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.fullModule.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ SourceHallNormalizerRemainder (K ⧸ center K) := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  exact source_hstar_hall_kernel_escaping_component_remaining_models D hn hH hlarge hP d hk
    (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ d.witness.abelianGroup
      (he ▸ d.hall_le) (he ▸ d.hall))

end CFSG.Quasithin.Chapter10
