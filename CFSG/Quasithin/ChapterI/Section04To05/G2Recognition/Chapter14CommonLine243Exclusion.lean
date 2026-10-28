module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14DiagonalSylow
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CommonLine243Exclusion

/-!
# The Sylow-243 exclusion at the original Chapter14 consumer

The original SourceLocalData supplies the marked configuration. Its paired
order-27 cores now force Sylow order 729 and common-line centralizer order
1458, retaining the actual common line, odd core, and Klein four complement.
For the entire configuration, 3³ dividing the ambient order forces 3⁶.

This discharges the Sylow-243 exclusion directly from the original
Chapter14 hypotheses. It does not exclude arbitrary order-243 subgroups.
The remaining Sylow-729 and Sylow-nine source cases and concrete Atlas
recognition remain with qt-i45-g2-recognition. SourceLocalData production
and final Chapter14 assembly retain their existing owners. Source:
Aschbacher–Smith I.4.5, printed p.417, applied in Theorem14.4.14.
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

theorem source_cubic_common_line_243_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      (3^3∣Nat.card G → 3^6∣Nat.card G) ∧
      (Nat.card (cubicOddCore c t.x)=27 →
      let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
      ∃ P : Sylow 3 G,
        (P:Subgroup G)=t.commonLineCore ∧
        _root_.centerIn (P:Subgroup G)=K ∧
        Subgroup.centralizer (P:Set G)=K ∧
        normalizer (P:Set G)=(P:Subgroup G) ⊔ t.torus.map c.H.subtype ∧
        Disjoint (P:Subgroup G) (t.torus.map c.H.subtype) ∧
        Nat.card (normalizer (P:Set G))=Nat.card P*4 ∧
        Nat.card P=729 ∧
        Nat.card (Subgroup.centralizer (K:Set G))=1458 ∧ ¬3^7∣Nat.card G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,cubic_cube_dvd_sixth_power (c:=c),fun h => ?_⟩
  obtain ⟨P,hP⟩ := t.commonLineCore_sylow h
  refine ⟨P,hP,?_,?_,?_,?_,?_,t.sylow_three_card729_of_twentySeven h P,
    t.core_intersection_centralizer_card1458 h,
    t.seventh_power_not_dvd_of_twentySeven h⟩
  · rw [hP]; exact t.commonLineCore_center h
  · change Subgroup.centralizer ((P:Subgroup G):Set G)=_
    rw [hP]; exact t.commonLineCore_centralizer h
  · change normalizer ((P:Subgroup G):Set G)=(P:Subgroup G) ⊔ _
    rw [hP]; exact (t.commonLineCore_normalizer_split h).1
  · rw [hP]; exact (t.commonLineCore_normalizer_split h).2
  · change Nat.card (normalizer ((P:Subgroup G):Set G))=Nat.card (P:Subgroup G)*4
    rw [hP]; exact t.commonLineCore_normalizer_card h

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
