module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.MarkedData
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.QuasisimpleSections
public import Theory.Quasithin.ComponentRanks

/-!
# Unconditional inner action on a nonnormal ordinary component

A nonnormal component has a distinct commuting conjugate. Its ordinary
odd-prime ranks are therefore bounded by the local quasithin bound of the
actual odd normalizer. The component itself is SQTK, even though the whole
normalizer need not be. The proved A/C source and perfect central descent
give soluble outer action and discharge the projection's inner-action premise.

Source: Aschbacher--Smith 4.4.9--11, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The stronger rank hypothesis holds on a nonnormal component itself. -/
theorem source_oddNormalizer_nonnormal_component_sqtk
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal) :
    IsSQTK KnownSimple.IsKnownSimple K := by
  classical
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE B hne
  have hN : normalizer (K : Set (normalizer (B : Set G))) ≠ ⊤ :=
    fun he => hnK (normalizer_eq_top_iff.mp he)
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN)
  have hneK : K ≠ K.map (MulAut.conj g).toMonoidHom :=
    fun he => hg.2 (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  exact ⟨fun p hp ho => hK.primeRank_le_two_of_ne (hK.map_conj g) hneK hqt p hp ho,
    hkg.subgroup K⟩

/-- Actual source ranks discharge soluble outer action for the nonnormal branch. -/
theorem source_oddNormalizer_nonnormal_component_outer
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal) :
    Group.IsSolvable (MulAut.Outer K) := by
  let : IsQuasisimple K := hK.2
  exact ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable
    (source_oddNormalizer_nonnormal_component_sqtk D B hne K hK hnK)
    ChapterA.Section02.IsSectionOf.refl

/-- The fixed residual acts by inner automorphisms on any escaping nonnormal
component, with no additional model or outer-action input. -/
theorem source_oddNormalizer_nonnormal_component_inner
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let := source_oddNormalizer_nonnormal_component_outer D B hne K hK hnK
  exact source_oddNormalizer_component_inner B K hK hFK

/-- The actual marked quotient and saturated projection are simultaneously
available on the same original residual and component. -/
theorem source_a5_oddNormalizer_nonnormal_marked_data
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    let F := (solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    let Y := D.maximalLocal.subgroupOf (normalizer (B : Set G))
    (∃ f : F →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      Function.Surjective f ∧ f.ker = pCore 2 F) ∧
    ∃ P Q : Subgroup (normalizer (B : Set G)), P ≤ K ∧
      Q ≤ centralizer (K : Set (normalizer (B : Set G))) ∧
      Group.IsPerfect P ∧ Group.IsPerfect Q ∧
      F.subgroupOf (normalizer (B : Set G)) ≤ P ⊔ Q ∧
      P ≤ F.subgroupOf (normalizer (B : Set G)) ⊔ Q ∧
      ⁅P.pCoreIn 2,P⁆ ≠ ⊥ ∧ P.pCoreIn 2 ≤ Y.pCoreIn 2 ∧
      Y ⊓ normalizer (K : Set (normalizer (B : Set G))) ≤
        normalizer (P : Set (normalizer (B : Set G))) := by
  exact source_a5_oddNormalizer_marked_projection_data D e hn hp B hB hBC hBV hperm
    K hK houtK (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

end CFSG.Quasithin.Chapter10
