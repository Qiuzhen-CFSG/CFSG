module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.AlternatingObstruction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Kernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Noncentral
public import Stellmacher.BaumannMap

/-!
# The rank-one Baumann image comparison

The genuine E.2.3 decomposition identifies the image of global J(KT_v)
with the marked K⁺: the simple residual forces one factor, and the natural
moving section excludes the S₅ permutation-module alternative even over
field four. The universal equality Baum(T_v)* = J(T_v)*, common to
E.2.3(2) and (3), combines with J(T_v) ≤ J(KT_v) to give the required
Baumann image containment. All maps are the restricted plus map or its
surjective range restriction. J((KT_v)*) is never identified with J(KT_v)*.

The final marked-source application discharges reducedness of the actual
W_K action on KT_v through `ReducedSource.local_reduced`. That proof uses
the genuine A₅ marking, its cubic L_v quotient, and the movement in 13.6.11
to compare the L_v kernels on U_K and W_K. It does not require subnormality
of KT_v in the larger actor or L_v ≤ K. The earlier conditional theorem is
preserved. The universal E.2.3 implications and independent earlier source
hypotheses, including minimal-parabolic status, remain explicit; the parent
Placement task owns the subsequent Borel normalization and placement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948); B.2.3, p.75;
E.2.3, pp.216–217 (PDF pp.227–228).
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection

universe u
/-- The common image equality in E.2.3(2) and (3), universally quantified
on the actual centralizer quotient. The universal theorem is an explicit
source input; no marked component or local image bound occurs in it. -/
def SourceBaumannImplication (𝒞 : GroupClass) : Prop :=
  ∀ {H A : Type u} [Group H] [Finite H] [Group A] [Finite A]
    (P : Sylow 2 H) (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* A) (_hq : Function.Surjective q)
    (_hker : q.ker = centralizer (V : Set H)),
    IsSQTK 𝒞 H → ChapterB.IsMinimalParabolicOver P ⊤ →
    Theory.GroupTheory.generalizedFitting H = pCore 2 H →
    pCore 2 A = ⊥ →
    ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (V : Set H) →
    (ChapterB.baumann (P : Subgroup H)).map q =
      (elementaryAbelianMaxJ (P : Subgroup H)).map q

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem local_baumann_subgroupOf (K T : Subgroup G) (v : G) :
    ChapterB.baumann ((Tv T v).subgroupOf (K ⊔ Tv T v)) =
      (ChapterB.baumann (Tv T v)).subgroupOf (K ⊔ Tv T v) := by
  apply map_injective (K ⊔ Tv T v).subtype_injective
  rw [map_subgroupOf_eq_of_le (show ChapterB.baumann (Tv T v) ≤ K ⊔ Tv T v from
    inf_le_left.trans le_sup_right)]
  have h := baumann_map_injective (K ⊔ Tv T v).subtype
    (K ⊔ Tv T v).subtype_injective ((Tv T v).subgroupOf (K ⊔ Tv T v))
  rw [map_subgroupOf_eq_of_le (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)] at h
  exact h

/-- The source E.2.3 clauses give the required literal plus-image bound,
conditional on reducedness of the actual local action. The linear factor
identification and all quotient transports are discharged here. -/
theorem local_source_baumann_image_le_of_reduced
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    {𝒞 : GroupClass} (hE23 : SourceFactors.SourceImplication 𝒞)
    (hBaum : SourceBaumannImplication 𝒞)
    (hq : IsSQTK 𝒞 (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction (Tv T v) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (P : Sylow 2 (K ⊔ Tv T v : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T v : Subgroup G)) =
      (Tv T v).subgroupOf (K ⊔ Tv T v))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hred : pCore 2 (localMap K L T z v hL hz).range = ⊥) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) ≤
      plusImage K L T z v hL hz K := by
  have hW := (WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans
    (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
  have hnc : ¬ elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G)) ≤
      centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G)) := by
    rw [hP, local_thompson_subgroupOf, ← localMap_ker_internal K L T z v hL hz hW,
      localMap_ker]
    intro hc
    apply local_thompson_noncentral K L T z v hL hz hK hnorm hF hb s hzOmega hpush
    intro x hx
    have hxH : x ∈ K ⊔ Tv T v :=
      (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
        ((show elementaryAbelianMaxJ (Tv T v) ≤ Tv T v from
          sSup_le fun _ hA => hA.1) hx)
    exact hc (show (⟨x, hxH⟩ : (K ⊔ Tv T v : Subgroup G)) ∈
      (elementaryAbelianMaxJ (Tv T v)).subgroupOf (K ⊔ Tv T v) from hx)
  have he := hBaum P (internalWK K L T z v hL hz)
    (localProjection K L T z v hL hz) (localMap K L T z v hL hz).rangeRestrict_surjective
    (localProjection_ker K L T z v hL hz hW)
    (local_sqtk K T v hK.1.1 hq) hmin
    (local_fitting_eq K T v hK.1.1 hSylow hf) hred hnc
  have him := congrArg (fun U : Subgroup (localMap K L T z v hL hz).range =>
    U.map (localMap K L T z v hL hz).range.subtype) he
  simp only [Subgroup.map_map] at him
  change (ChapterB.baumann (P : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) =
    (elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) at him
  have hJ := SourceFactors.local_source_thompson_image K L T z v hL hz hK hnorm hF hb s
    hE23 hq hzOmega hpush hSylow hf P hP hmin hred
  have hle := map_mono (f := localMap K L T z v hL hz)
    (elementaryAbelianMaxJ_sylow_le_top P)
  rw [← him, hJ, hP, local_baumann_subgroupOf,
    localMap_image K L T z v hL hz (ChapterB.baumann (Tv T v))
      (inf_le_left.trans le_sup_right)] at hle
  exact hle

open A5Module

/-- The exact image containment needed in 13.6.18, on the actual marked
source action. Reducedness is proved from the A₅ marking and earlier local
data; the universal E.2.3 implications remain explicit source inputs.
No local reducedness, factor identification, Borel placement or Lᵥ ≤ K
premise remains. -/
theorem local_source_baumann_image_le
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
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤) :
    plusImage K L T (markedZ m) (markedV m) hL hz
        (ChapterB.baumann (Tv T (markedV m))) ≤
      plusImage K L T (markedZ m) (markedV m) hL hz K := by
  exact local_source_baumann_image_le_of_reduced K L T (markedZ m) (markedV m)
    hL hz hK hnorm hF hb s hE23 hBaum hq hzOmega hpush hSylow hf P hP hmin
    (ReducedSource.local_reduced m K T hk hL hz hK hnorm hF hb s hzOmega hSylow hf)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
end
