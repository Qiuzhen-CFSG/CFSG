module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.LocalNaturalLayer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
/-!
# Literal rank-one source placement from the natural component

The normal self-centralizing residual acts naturally on the original moving
section. Every best offender therefore lies in that residual. The original
Thompson image and the proved E.2.3 Baumann equality place the original
Baumann image in K+, giving the Borel normalizations and local placement.
No universal factor-decomposition or Baumann theorem remains as a premise.
Source: Aschbacher--Smith 13.6.18, printed p.931, and E.2.3, pp.216--217.
-/
public section
open Subgroup Stellmacher Matrix.SpecialLinearGroup
open scoped IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
theorem local_natural_baumann_image_le
    {L V : Subgroup G} (m : Marking L V) (K T : Subgroup G)
    (hk : m.action.ker = pCore 2 L)
    (hL : Tv T (markedV m) ≤ normalizer (Lv L (markedV m) : Set G))
    (hz : Tv T (markedV m) ≤ centralizer ({markedZ m} : Set G))
    (hK : K ∈ Yz L T (markedZ m) (markedV m))
    (hnorm : Tv T (markedV m) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T (markedZ m) (markedV m))]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L T (markedZ m) (markedV m) hL hz)
      (movingSpace K L T (markedZ m) (markedV m)))
    (hq : IsSQTK KnownSimple.IsKnownSimple (Gv (markedV m)))
    (hzOmega : markedZ m ∈ omegaOneCenterAmbient (Tv T (markedV m)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv T (markedV m)) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV m)) (Gv (markedV m)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV m)) =
      pCore 2 (Gv (markedV m)))
    (P : Sylow 2 (K ⊔ Tv T (markedV m) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T (markedV m) : Subgroup G)) =
      (Tv T (markedV m)).subgroupOf (K ⊔ Tv T (markedV m)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤) :
    plusImage K L T (markedZ m) (markedV m) hL hz
        (ChapterB.baumann (Tv T (markedV m))) ≤
      plusImage K L T (markedZ m) (markedV m) hL hz K := by
  exact local_natural_baumann_image_le_of_reduced K L T (markedZ m) (markedV m)
    hL hz hK hnorm hF hb s hq hzOmega hpush hSylow hf P hP hmin
    (ReducedSource.local_reduced m K T hk hL hz hK hnorm hF hb s hzOmega hSylow hf)

theorem local_natural_normalizations_and_placement
    {L V : Subgroup G} (m : Marking L V) (K T M : Subgroup G)
    (hk : m.action.ker = pCore 2 L)
    (hL : Tv T (markedV m) ≤ normalizer (Lv L (markedV m) : Set G))
    (hz : Tv T (markedV m) ≤ centralizer ({markedZ m} : Set G))
    (hK : K ∈ Yz L T (markedZ m) (markedV m))
    (hnorm : Tv T (markedV m) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T (markedZ m) (markedV m))]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L T (markedZ m) (markedV m) hL hz)
      (movingSpace K L T (markedZ m) (markedV m)))
    (hq : IsSQTK KnownSimple.IsKnownSimple (Gv (markedV m)))
    (hzOmega : markedZ m ∈ omegaOneCenterAmbient (Tv T (markedV m)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv T (markedV m)) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV m)) (Gv (markedV m)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV m)) =
      pCore 2 (Gv (markedV m)))
    (P : Sylow 2 (K ⊔ Tv T (markedV m) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T (markedV m) : Subgroup G)) =
      (Tv T (markedV m)).subgroupOf (K ⊔ Tv T (markedV m)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (h1324 : ChapterB.baumann T ≤ Tv T (markedV m))
    (h1325 : normalizer (ChapterB.baumann T : Set G) ≤ M)
    (h1226 : Mv M (markedV m) ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M) :
    borel K (Tv T (markedV m)) ≤
        normalizer (elementaryAbelianMaxJ (Tv T (markedV m)) : Set G) ∧
      borel K (Tv T (markedV m)) ≤
        normalizer (ChapterB.baumann (Tv T (markedV m)) : Set G) ∧
      borel K (Tv T (markedV m)) ≤ Mv M (markedV m) := by
  have him := local_natural_baumann_image_le m K T hk hL hz hK hnorm hF hb s
    hq hzOmega hpush hSylow hf P hP hmin
  exact normalizations_and_placement K L T M V (markedZ m) (markedV m)
    hL hz hK hnorm hF hb s him h1324 h1325 h1226 hMV

/-- Supply the placement premise of `BorelGeometry.local_source_conclusions`
from the marked source data. The block supplies `1 < n`, and the marking
supplies `z ∈ V`; no local image, reducedness or Borel placement premise
remains. Degree and residual/checked fixation use the existing consumer. -/
theorem local_natural_conclusions_of_marking
    {L V : Subgroup G} (m : Marking L V) (K T M : Subgroup G)
    (hk : m.action.ker = pCore 2 L)
    (hL : Tv T (markedV m) ≤ normalizer (Lv L (markedV m) : Set G))
    (hz : Tv T (markedV m) ≤ centralizer ({markedZ m} : Set G))
    (hK : K ∈ Yz L T (markedZ m) (markedV m))
    (hnorm : Tv T (markedV m) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T (markedZ m) (markedV m))]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L T (markedZ m) (markedV m) hL hz)
      (movingSpace K L T (markedZ m) (markedV m)))
    (hq : IsSQTK KnownSimple.IsKnownSimple (Gv (markedV m)))
    (hzOmega : markedZ m ∈ omegaOneCenterAmbient (Tv T (markedV m)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv T (markedV m)) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV m)) (Gv (markedV m)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV m)) =
      pCore 2 (Gv (markedV m)))
    (P : Sylow 2 (K ⊔ Tv T (markedV m) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T (markedV m) : Subgroup G)) =
      (Tv T (markedV m)).subgroupOf (K ⊔ Tv T (markedV m)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (h1324 : ChapterB.baumann T ≤ Tv T (markedV m))
    (h1325 : normalizer (ChapterB.baumann T : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV m) ≤ normalizer (V : Set G))
    (hLV : Lv L (markedV m) ≤ normalizer (V : Set G))
    (hcard : Nat.card (conjugationAction V (Lv L (markedV m)) hLV).range = 3)
    (a : Gv (markedV m))
    (haV : (a : G) ∈ V)
    (haL : (a : G) ∈ centralizer (Lv L (markedV m) : Set G))
    (haT : checkedQuotientMap (markedV m) a ∈
      centralizer (checkedImage (markedV m) (Tv T (markedV m)) : Set (Gcheck (markedV m))))
    (hlocal : (pResidual 2 (Mv M (markedV m))).map (Mv M (markedV m)).subtype ≤
      Lv L (markedV m) ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ s' : NaturalSection (F := F)
        (componentRepresentation K L T (markedZ m) (markedV m) hL hz)
        (movingSpace K L T (markedZ m) (markedV m)),
      let B := borel K (Tv T (markedV m))
      let R := (pResidual 2 B).map B.subtype
      Tv T (markedV m) ≤ B ∧ B ≤ K ⊔ Tv T (markedV m) ∧
      ((B.subgroupOf K).map (componentMap K L T (markedZ m) (markedV m) hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧ n = 2 ∧
      R ≤ centralizer ({(a : G)} : Set G) ∧
      ((R.subgroupOf K).map (componentMap K L T (markedZ m) (markedV m) hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧
      checkedQuotientMap (markedV m) a ∈
        centralizer (checkedImage (markedV m) B : Set (Gcheck (markedV m))) := by
  have hBM := (local_natural_normalizations_and_placement m K T M hk hL hz hK hnorm
    hF hb s hq hzOmega hpush hSylow hf P hP hmin h1324 h1325 hBV hMV).2.2
  have hzV : markedZ m ∈ V := m.range_eq.le ⟨_, rfl⟩
  exact local_source_conclusions K L T M V (markedZ m) (markedV m) hL hz hb.1 hF
    hK hnorm s hBM hBV hLV hcard hzV a haV haL haT hlocal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
