module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Intermediate
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Kernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Noncentral
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage

/-!
# Placement of the marked rank-one Borel from its action image

The block quotient and the natural-section model make the restricted
plus-action kernel a two-group. If the Baumann image lies in K⁺, the
preimage of the component Sylow image is Borel-invariant and lies between
Baum(T_v) and T_v. Heredity gives normalization of J(T_v) and Baum(T_v),
and the earlier 13.6.4–5 bounds give B ≤ M_v. The final theorem supplies
this placement to BorelGeometry.local_source_conclusions.

The marked-source application now discharges image containment through
SourceImage: the actual A₅ marking gives the reduced local action, and the
natural section identifies the single E.2.3 factor with K⁺. It then supplies
placement to the existing degree, residual and checked-action consumer.
The universal E.2.3 implications and independent earlier source hypotheses
remain explicit. The separate full-Borel fixation step of 13.6.18 is not
asserted here. The earlier conditional image APIs are preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948); E.2.3, pp.216–217; B.2.3, p.75.
-/

@[expose] public section

open Subgroup Stellmacher Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The kernel and preimage construction discharges both normalizations and
local placement, conditional on the precise remaining E.2.3 image containment. -/
theorem normalizations_and_placement
    (K L T M V : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (him : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) ≤
      plusImage K L T z v hL hz K)
    (h1324 : ChapterB.baumann T ≤ Tv T v)
    (h1325 : normalizer (ChapterB.baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M) :
    borel K (Tv T v) ≤ normalizer (elementaryAbelianMaxJ (Tv T v) : Set G) ∧
      borel K (Tv T v) ≤ normalizer (ChapterB.baumann (Tv T v) : Set G) ∧
      borel K (Tv T v) ≤ Mv M v := by
  let f := localMap K L T z v hL hz
  have hk := localMap_kernel_isPGroup K L T z v hL hz hK hnorm hF hb s
  have hi : ((ChapterB.baumann (Tv T v)).subgroupOf (K ⊔ Tv T v)).map f ≤
      (K.subgroupOf (K ⊔ Tv T v)).map f := by
    dsimp only [f]
    rw [localMap_image K L T z v hL hz _
      (show ChapterB.baumann (Tv T v) ≤ K ⊔ Tv T v from inf_le_left.trans le_sup_right),
      localMap_image K L T z v hL hz K le_sup_left]
    exact him
  obtain ⟨hBQ, hQT, hN⟩ := intermediate_spec K (Tv T v) hK.1.2.2.1 f hk hi
  have hn := normalizations_of_intermediate (borel K (Tv T v)) (Tv T v)
    (intermediate K (Tv T v) f) hBQ hQT hN
  exact ⟨hn.1, hn.2, placement_of_invariant_intermediate K T M V
    (intermediate K (Tv T v) f) v hK.1.1 h1324 hBQ hQT hN h1325 h1226 hMV⟩

/-- Conditional image API for the existing marked-section, degree and residual
consumer. The marked-source application below discharges image containment. -/
theorem local_source_conclusions_of_image
    (K L T M V : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hb : ChapterC.IsL2EvenBlock K n)
    (him : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) ≤
      plusImage K L T z v hL hz K)
    (h1324 : ChapterB.baumann T ≤ Tv T v)
    (h1325 : normalizer (ChapterB.baumann T : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M v ≤ normalizer (V : Set G))
    (hLV : Lv L v ≤ normalizer (V : Set G))
    (hcard : Nat.card (conjugationAction V (Lv L v) hLV).range = 3)
    (hzV : z ∈ V) (a : Gv v)
    (haV : (a : G) ∈ V) (haL : (a : G) ∈ centralizer (Lv L v : Set G))
    (haT : checkedQuotientMap v a ∈
      centralizer (checkedImage v (Tv T v) : Set (Gcheck v)))
    (hlocal : (pResidual 2 (Mv M v)).map (Mv M v).subtype ≤
      Lv L v ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ s' : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
        (movingSpace K L T z v),
      let B := borel K (Tv T v)
      let R := (pResidual 2 B).map B.subtype
      Tv T v ≤ B ∧ B ≤ K ⊔ Tv T v ∧
      ((B.subgroupOf K).map (componentMap K L T z v hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧ n = 2 ∧
      R ≤ centralizer ({(a : G)} : Set G) ∧
      ((R.subgroupOf K).map (componentMap K L T z v hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧
      checkedQuotientMap v a ∈ centralizer (checkedImage v B : Set (Gcheck v)) := by
  have hBM := (normalizations_and_placement K L T M V z v hL hz hK hnorm
    hF hb s him h1324 h1325 hBV hMV).2.2
  exact local_source_conclusions K L T M V z v hL hz hn hF hK hnorm s hBM
    hBV hLV hcard hzV a haV haL haT hlocal

/-- E.2.3 and B.2.3 applied to the actual marked source configuration give
both normalizations and the placement required in 13.6.18. The image bound,
two-kernel and invariant intermediate subgroup are proved, not premises.
The independent inputs are the earlier local data and minimal-parabolic
status; the universal E.2.3 implications remain with the Chapter E owner. -/
theorem local_source_normalizations_and_placement
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
    {𝒞 : GroupClass} (hE23 : SourceFactors.SourceImplication 𝒞)
    (hBaum : SourceBaumannImplication 𝒞)
    (hq : IsSQTK 𝒞 (Gv (markedV m)))
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
  have him := local_source_baumann_image_le m K T hk hL hz hK hnorm hF hb s
    hE23 hBaum hq hzOmega hpush hSylow hf P hP hmin
  exact normalizations_and_placement K L T M V (markedZ m) (markedV m)
    hL hz hK hnorm hF hb s him h1324 h1325 h1226 hMV

/-- Supply the placement premise of `BorelGeometry.local_source_conclusions`
from the marked source data. The block supplies `1 < n`, and the marking
supplies `z ∈ V`; no local image, reducedness or Borel placement premise
remains. Degree and residual/checked fixation use the existing consumer. -/
theorem local_source_conclusions_of_marking
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
    {𝒞 : GroupClass} (hE23 : SourceFactors.SourceImplication 𝒞)
    (hBaum : SourceBaumannImplication 𝒞)
    (hq : IsSQTK 𝒞 (Gv (markedV m)))
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
  have hBM := (local_source_normalizations_and_placement m K T M hk hL hz hK hnorm
    hF hb s hE23 hBaum hq hzOmega hpush hSylow hf P hP hmin h1324 h1325 hBV hMV).2.2
  have hzV : markedZ m ∈ V := m.range_eq.le ⟨_, rfl⟩
  exact local_source_conclusions K L T M V (markedZ m) (markedV m) hL hz hb.1 hF
    hK hnorm s hBM hBV hLV hcard hzV a haV haL haT hlocal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement

end
