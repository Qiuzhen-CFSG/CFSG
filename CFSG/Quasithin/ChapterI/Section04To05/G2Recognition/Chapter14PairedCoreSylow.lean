module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14OddCoreIntersection
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreSylow

/-!
# The Sylow-81 exclusion at the original Chapter14 consumer

The original SourceLocalData supplies the marked G₂(3) configuration.
The two order-27 odd cores produce nonconjugate extensions of order 81,
so 3^5 divides the ambient order in this branch. In all branches,
3^3 ∣ |G| implies 3^5 ∣ |G|. This discharges the Sylow-81 exclusion
without adding a simplicity or divisibility premise to the source setup.

Source: Aschbacher–Smith I.4.5, printed p.417, used in 14.4.14. The
SourceLocalData producer remains qt-d-14414-g2-source. The Sylow-nine
case, order-27 cores with larger ambient Sylow subgroups, and the actual
Atlas recognition equivalence remain with qt-i45-g2-recognition.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_paired_core_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      (3^3 ∣ Nat.card G → 3^5 ∣ Nat.card G) ∧
      (Nat.card (cubicOddCore c t.x)=27 →
        (⁅cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G),
          cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)⁆ =
          cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y) ∧
        (∀ g : G,
          (cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom ≠
            cubicOddCore (swapFactors c) t.y ⊔ zpowers ((t.x:c.H):G)) ∧
        3^5 ∣ Nat.card G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,cubic_cube_dvd_fifth_power (c:=c),fun h => ?_⟩
  exact ⟨t.left_core_extension_derived h,t.core_extensions_not_conjugate h,
    t.left_oddCore_twentySeven_fifth_power_dvd h⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
