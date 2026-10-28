module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14DiagonalCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.DiagonalSylow

/-!
# Ambient Sylow geometry from the original Chapter14 local data

In the order-27-core branch, the actual odd core of the common-line
centralizer is an ambient Sylow three-subgroup. Its center and ambient
centralizer are that common line, and its full normalizer is its product
with the original Klein four torus, with trivial intersection. Its order
is 243 or 729; in particular, 3^7 does not divide the ambient order.

This discharges the Sylow and normalizer premises for this branch at the
literal SourceLocalData consumer of Aschbacher–Smith I.4.5, printed p.417,
used in Theorem14.4.14. The order-27-core and Sylow-nine exclusions and the
Atlas model comparison remain open. The SourceLocalData producer and final
Chapter14 assembly retain their existing owners.
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

theorem source_cubic_diagonal_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      Nat.card (cubicOddCore c t.x)=27 →
      let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
      ∃ P : Sylow 3 G,
        (P:Subgroup G)=t.commonLineCore ∧
        _root_.centerIn (P:Subgroup G)=K ∧
        Subgroup.centralizer (P:Set G)=K ∧
        normalizer (P:Set G)=(P:Subgroup G) ⊔ t.torus.map c.H.subtype ∧
        Disjoint (P:Subgroup G) (t.torus.map c.H.subtype) ∧
        Nat.card (normalizer (P:Set G))=Nat.card P*4 ∧
        (Nat.card P=243 ∨ Nat.card P=729) ∧ ¬3^7∣Nat.card G := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,fun h => ?_⟩
  obtain ⟨P,hP⟩ := t.commonLineCore_sylow h
  refine ⟨P,hP,?_,?_,?_,?_,?_,t.sylow_three_card_of_twentySeven h P,
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
