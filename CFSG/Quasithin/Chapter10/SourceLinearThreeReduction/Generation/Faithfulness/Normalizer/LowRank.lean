module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.FiniteExclusions
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.GroupTheory.PerfectMovedElementaryRank

/-!
# Low-rank and alternating odd-normalizer exclusions

The actual perfect residual moves a nontrivial elementary subgroup in the
component's central quotient, forcing two-rank at least three. This excludes
the odd Theorem C rows and every odd-field PSL₂ row. The known alternating
outer action places the same residual in all alternating rows through degree
nine, where the existing doubled-odd-rank obstruction applies.

The original full module, normal component and complete center are retained.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), printed pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (K : Subgroup (normalizer (B : Set G)))

include D hn hBC hodd hBV

/-- The image of the original moved module forces two-rank at least three,
retaining the full central kernel of the containing component. -/
theorem source_nonnormal_oddNormalizer_quotient_twoRank_ge_three
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    3 ≤ primeRank 2 (K ⧸ center K) := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := F.subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨hP,hW,hE,hm,_,_⟩ :=
    source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
  obtain ⟨_,_,_,_,_,hWP,_,_,_⟩ :=
    source_oddNormalizer_component_local_geometry_of_residual_le D B hBC hodd hBV K hFK
  let : Group.IsPerfect (P.map q) := hP
  let : IsElementaryAbelian 2 (W.map q) := hE
  exact three_le_primeRank_of_perfect_moved_elementary (P.map q) (W.map q)
    (map_mono (hWP.trans (pCoreIn_le 2 P))) hW hm

variable
  (hu : UniqueMaximalOvergroup
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hBC hodd hBV hu hK hout

/-- Soluble outer action places the literal perfect residual in the normal
component under the original covering uniqueness hypothesis. -/
theorem source_nonnormal_oddNormalizer_residual_le_of_solvable_outer
    [Group.IsSolvable (MulAut.Outer K)] :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K := by
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) :=
    le_trans le_top le_normalizer_of_normal
  have hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))) :=
    le_trans le_top le_normalizer_of_normal
  exact (source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    D hn B hBC hodd hBV hu K hK hout hYK
      (source_oddNormalizer_component_inner B K hK hFK)).2.2.2

/-- All alternating rows of B, including degree nine, have their outer
placement premise discharged. -/
theorem source_nonnormal_oddNormalizer_no_alternating_component
    {n : ℕ} (hn9 : n ≤ 9) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.alternating
      (Group.IsPerfect.not_isMulCommutative _) ⟨e⟩
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact source_nonnormal_oddNormalizer_no_placed_alternating_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_solvable_outer D hn B hBC hodd hBV K hu hK hout)
    hn9 e

/-- Every odd-field PSL₂ row of B is excluded, with no restriction on the
field exponent beyond its actual field witness. -/
theorem source_nonnormal_oddNormalizer_no_odd_linear_two_component
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 q) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd
      (Group.IsPerfect.not_isMulCommutative _) ho hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hlo := source_nonnormal_oddNormalizer_quotient_twoRank_ge_three D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_solvable_outer D hn B hBC hodd hBV K hu hK hout)
  have hup := ChapterA.Section02.odd_psl_two_twoRank_le_two ho hm
  omega

/-- All odd-characteristic rows of C are excluded using the original moved
module and the literal central quotient. -/
theorem source_nonnormal_oddNormalizer_no_theoremC_odd_component
    (hm : ChapterA.Section02.IsTheoremCOddModel (K ⧸ center K)) : False := by
  have hlo := source_nonnormal_oddNormalizer_quotient_twoRank_ge_three D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout (.odd hm))
  have hup := hm.twoRank_le_two
  omega

end CFSG.Quasithin.Chapter10
