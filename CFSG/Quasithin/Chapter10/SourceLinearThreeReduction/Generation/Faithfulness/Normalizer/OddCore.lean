module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.ModuleSize
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.CoprimeEscape
public import CFSG.Quasithin.Chapter10.SourceA5OddNormalizerCore

/-!
# Odd-core control for a nonnormal Hall-kernel normalizer

An odd actor fixing the literal orbit quotient and the original full module
fixes a perfect residual covering that orbit modulo its two-core. This
residual generates the module. The nonnormal pair forces the module to
have more than eight elements, so A.1.28 and A.1.26 centralize the odd core
of the actor normalizer. The proved full-module normalizer identity then
places this odd core in the original maximal local group.

The final theorem applies this conclusion to the actual elementary actor
selected inside an original H-star Hall kernel. Its explicit fixation
premise remains owned by qt-d-10-nona5-hall-faithfulness; odd-core control
alone does not prove the full normalizer containment in 4.4.3.

Source: Aschbacher--Smith, 4.4.5, 4.4.8, and 10.2.3(2), printed
pp.620,745, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

private theorem perfect_isPPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  by_contra hne
  let : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance

/-- The odd-core conclusion of source 4.4.8 for the original nonnormal module. -/
theorem source_nonnormal_oddNormalizer_oddCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G)) :
    let O := (pPrimeCore 2 (normalizer (B : Set G))).map (normalizer (B : Set G)).subtype
    ⁅D.fullModule,O⁆ = ⊥ ∧ O ≤ D.maximalLocal := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,he,_⟩ := source_fullModule_oddActor_cover D B hB hodd hBV
  let : Group.IsPerfect F := Group.IsPerfect.map C.subtype
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  let := D.fullModule_elementary (source_uniqueness D)
  let : IsElementaryAbelian 2 (D.fullModule.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  have heN : D.fullModule.subgroupOf N = ⁅D.fullModule.subgroupOf N,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hFN]
    exact he
  have hcN : 8 < Nat.card (D.fullModule.subgroupOf N) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv]
    exact source_nonnormal_fullModule_card_gt_eight D hn
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (D.simpleQTKE.quasithin.subgroup N) (F.subgroupOf N) (D.fullModule.subgroupOf N)
    perfect_isPPerfect hcN heN
  have hm := congrArg (Subgroup.map N.subtype) hh
  have hcomm : ⁅D.fullModule,(pPrimeCore 2 N).map N.subtype⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hVN,Subgroup.map_bot] using hm
  refine ⟨hcomm,?_⟩
  rw [← source_fullModule_normalizer D]
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
    (Subgroup.centralizer_le_normalizer _)

open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- A nontrivial original Hall kernel supplies an escaping elementary actor
whose normalizer has odd core centralized by the original full module.
The module-fixation premise is retained for the Hall-faithfulness assembly. -/
theorem source_hstar_hall_kernel_escaping_oddCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
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
      let O := (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype
      ⁅D.fullModule,O⁆ = ⊥ ∧ O ≤ D.maximalLocal := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_coprime D hn hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hk]
    exact ho.pow
  have hc := source_nonnormal_oddNormalizer_oddCore D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix)
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc⟩

end CFSG.Quasithin.Chapter10
