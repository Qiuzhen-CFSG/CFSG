module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14PairedCoreSylow
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreCentralizer

/-!
# The common-line centralizer and diagonal placement in the Chapter14 setup

The original SourceLocalData produces the marked configuration. In the
order27-core branch, the common line has centralizer order divisible by
3^5, centralizes a marked torus involution, and is conjugate to a diagonal
of the original cubic plane. These conclusions use the actual odd cores,
factors and torus; no additional fusion or centralizer assumption is made.

Source: Aschbacher–Smith I.4.5, printed p.417, used in 14.4.14. The final
recognition isomorphism remains unproved; the independent SourceLocalData
producer and final Chapter14 assembly retain their existing owners.
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

theorem source_cubic_paired_core_centralizer (d : Counterexample T L)
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
      3^5 ∣ Nat.card (Subgroup.centralizer (K:Set G)) ∧
      (∃ v : G, v ∈ t.torus.map c.H.subtype ∧ orderOf v=2 ∧
        v ∈ Subgroup.centralizer (K:Set G)) ∧
      (∃ g : G, K.map (MulAut.conj g).toMonoidHom ≤
          zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) ∧
        K.map (MulAut.conj g).toMonoidHom ≠ zpowers ((t.x:c.H):G) ∧
        K.map (MulAut.conj g).toMonoidHom ≠ zpowers ((t.y:c.H):G)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  exact ⟨c,t,fun h => ⟨t.core_intersection_centralizer_fifth_power_dvd h,
    t.core_intersection_centralizing_involution h,t.exists_core_intersection_diagonal h⟩⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
