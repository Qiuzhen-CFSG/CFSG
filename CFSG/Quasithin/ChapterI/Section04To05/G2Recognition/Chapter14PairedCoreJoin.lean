module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CommonLine243Exclusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreJoinFixed

/-!
# The actual extraspecial join at the Chapter14 consumer

SourceLocalData supplies the original marked configuration. In its remaining
order-27-core branch, the two literal cores generate an extraspecial group
of order 243, with center and derived group their common line. The full
normalizer of the actual Sylow group preserves this join. The original
torus supplies an involution fixing exactly its center, and the cubic
fixed-point bound applies to every commuting cubic element of that Sylow.

This discharges the extraspecial-join and cubic fixed-point premises from
the original Chapter14 inputs. The order-27-core exclusion, the Sylow-nine
branch and the concrete Atlas equivalence remain with the recognition
owner. SourceLocalData production and final Chapter14 assembly retain their
existing owners. Source: Aschbacher–Smith I.4.5, printed p.417, applied in
Theorem14.4.14.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_paired_join (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      Nat.card (cubicOddCore c t.x)=27 →
      let J := cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y
      let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
      Nat.card t.commonLineCore=729 ∧ Nat.card J=243 ∧ IsExtraspecial 3 J ∧
      Subgroup.centralizer (J:Set G)=K ∧ _root_.centerIn J=K ∧ ⁅J,J⁆=K ∧
      normalizer (t.commonLineCore:Set G)≤normalizer (J:Set G) ∧
      ∃ v : G, v∈t.torus.map c.H.subtype ∧ orderOf v=2 ∧
        J ⊓ Subgroup.centralizer ({v}:Set G)=K ∧
        ∀ a : G, a∈t.commonLineCore → orderOf a=3 → Commute v a →
          27≤Nat.card (J ⊓ Subgroup.centralizer ({a}:Set G) : Subgroup G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,fun h => ?_⟩
  obtain ⟨hC,hZ,hderived⟩ := t.paired_cores_join_center_derived h
  exact ⟨t.commonLineCore_card729 h,(t.paired_cores_join_card_normal h).1,
    t.paired_cores_join_extraspecial h,hC,hZ,hderived,
    t.paired_cores_join_normalizer h,t.exists_paired_cores_join_fixed h⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
