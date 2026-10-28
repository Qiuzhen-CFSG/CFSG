module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.SmallKernelCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSOriginalSource
/-!
# The original checked-center identity above distance four

The actual binary MS input on K Tᵥ supplies the small-central-kernel theorem.
Its application uses the literal checked quotient K → Ǩ, whose kernel has
order at most two and is central in K Tᵥ. Transport through the inclusion of
K in the join gives [Z₀,K]=[Z(O₂(K)),K] in the original ambient group.

No C.1.34 alternative, fixed-factor classification, Frattini-centralizer
nonabelianness, or extra action premise is used. Prescribed replacement
supplies the earlier large-core layers in the second export.

Source: Aschbacher--Smith 13.6.22, printed pp.932--933; MS93 (4.4)--(4.5).
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open A5Module MSSourceModels MSSourceModels.NonabelianCenters
open MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {K T L : Subgroup G} {z v : G}

theorem large_checked_commutator_of_source
    (hK : K ∈ Yz L T z v) (hv : v ^ 2 = 1)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (t : BinaryMS.MS93.InputSetup (inputOfProductOddIndex hMS e
      (joinProduct_of_normalizes hn) (oddIndex_of_sylow hMS hK.1.2.2.1)))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : BinaryMS.MS93.DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ⁅sourceZ0 K v hK.1.1,K⁆ = sourceU K := by
  let J := K ⊔ Tv T v
  let A := K.subgroupOf J
  let eA : A ≃* K := subgroupOfEquivOfLe le_sup_left
  let f := BinaryRankTwo.CenterPreimage.checkedKMap K v hK.1.1
  let g := f.comp eA.toMonoidHom
  have hf : Function.Surjective g :=
    (BinaryRankTwo.CenterPreimage.checkedKMap_surjective K v hK.1.1).comp eA.surjective
  have hk : IsPGroup 2 g.ker :=
    (BinaryRankTwo.CenterPreimage.checkedKMap_pKernel K v hK.1.1 hv).comap_of_injective
      eA.toMonoidHom eA.injective
  have hgker : g.ker = f.ker.comap eA.toMonoidHom := rfl
  have hcard : Nat.card g.ker ≤ 2 := by
    rw [hgker,comap_equiv_eq_map_symm' eA,card_map_of_injective eA.symm.injective]
    exact Nat.le_of_dvd (by decide) (checkedKMap_kernel_card K v hK.1.1 hv)
  have hc : g.ker.map A.subtype ≤ center J := by
    rintro j ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have h := checkedKMap_kernel_central_join K T v hK.1.1
      (mem_map_of_mem K.subtype (show eA a ∈ f.ker from ha))
    exact (centerIn_eq J ▸ h).2 x x.property
  have hh := t.large_center_preimage_commutator common earlier g hf hk hcard hc
  have hl : (((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).comap g).map
      eA.toMonoidHom =
      ((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).comap f := by
    change (((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).comap
      (f.comp eA.toMonoidHom)).map eA.toMonoidHom = _
    rw [← comap_comap,map_comap_eq_self_of_surjective eA.surjective]
  have hr : ((center (pCore 2 A)).map (pCore 2 A).subtype).map eA.toMonoidHom =
      (center (pCore 2 K)).map (pCore 2 K).subtype := by
    rw [map_embeddedCenter _ _ eA.injective,pCore_map_iso]
  have hm := congrArg (map eA.toMonoidHom) hh
  rw [map_commutator,map_commutator,map_top_of_surjective _ eA.surjective,hl,hr] at hm
  have hg := congrArg (map K.subtype) hm
  rw [map_commutator,map_commutator,← MonoidHom.range_eq_map,range_subtype] at hg
  exact hg
open BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality

/-- Prescribed replacement supplies the earlier MS facts at this same original
source input; no fourth-case classification is assumed. -/
theorem large_checked_commutator_of_replacement
    (hK : K ∈ Yz L T z v) (hv : v ^ 2 = 1)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (t : InputSetup (inputOfProductOddIndex hMS e
      (joinProduct_of_normalizes hn) (oddIndex_of_sylow hMS hK.1.2.2.1)))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators _ p → PrescribedReplacement _ p) :
    ⁅sourceZ0 K v hK.1.1,K⁆ = sourceU K :=
  large_checked_commutator_of_source hK hv hn hMS e t common
    (Source44.SourceEarlier.earlier common hb replacement)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
