module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction.Actors
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Original

/-!
# Strict E.2.15 for the original normal and paired Bender sources

The original minimal-parabolic assumptions place the actual normalizer
inside the distinguished maximal subgroup. The completed full-core
witness constructions then supply all model and Borel geometry, and
the strict actor estimate applies to the literal normalizer quotient or
any original normalizing overgroup containing the Sylow subgroup.

The paired source retains only the genuine earlier Theorems A and C.
Source: E.2.7–9 and E.2.15, printed pp.218–222,228; the stronger ambient
action formulation also feeds the original general 3.1.8 application.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
  {T : Sylow 2 H} {V U : Subgroup H} [IsElementaryAbelian 2 V]

theorem original_witness_cubicRatio_lt_two
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨ V.map (MulAut.conj x).toMonoidHom = V)
    {n : ℕ} (w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hn := minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  exact w.cubicRatio_lt_two hVT hTV hVM hn hfit hTI hTU hU

/-- The literal normalizer action requested in E.2.15. -/
theorem original_witness_normalizer_cubicRatio_lt_two
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨ V.map (MulAut.conj x).toMonoidHom = V)
    {n : ℕ} (w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) :
    cubicRatio (DihedralCubic.canonicalAction (normalizer (V : Set H)) V le_rfl) < 2 :=
  original_witness_cubicRatio_lt_two hP hVT hvn hVM hout hfit hTI w
    ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn) le_rfl

theorem normal_bender_cubicRatio_lt_two
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨ V.map (MulAut.conj x).toMonoidHom = V)
    (D : Subgroup (H ⧸ ChapterB.minimalParabolicCore T hP)) [D.Normal]
    (hgen : D ⊔ (T : Subgroup H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) = ⊤)
    (hm : ClassificationModels.IsBenderModel D)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  obtain ⟨n,hm,⟨w⟩⟩ := source T hP V hVT hvn hVM hout D hgen hm
  exact original_witness_cubicRatio_lt_two hP hVT hvn hVM hout hfit hTI w hTU hU

theorem paired_bender_cubicRatio_lt_two
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨ V.map (MulAut.conj x).toMonoidHom = V)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  obtain ⟨n,hm,⟨w⟩⟩ := PairedBender.original_source hA hC hH T hP hs K hK hgen hn
    V hVT hvn hVM hout
  exact original_witness_cubicRatio_lt_two hP hVT hvn hVM hout hfit hTI w hTU hU
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
