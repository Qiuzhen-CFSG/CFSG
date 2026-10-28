module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNativeApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourReduced

/-!
# Reduced U₄ restoration at the Chapter 12 chosen module

The actual chosen-module preparation supplies genuine F.1.1. Restoring a
marked reduced U₄ pair therefore constructs the original extension marking
required by the existing consumer. Both orientations, m = 2, the complete
original Borel and the same original selected R remain unchanged. We obtain
the original Sylow intersections, native involution placement, and the
diagram-layer exclusion, without assuming a pure original comparison.

Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith F.1.12, pp.263–264,
F.4.35, p.292, and the chosen-module application, p.795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m) (point : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (UnitaryFourNative.amalgam m hm point))
include D d h hmany hn hpsl hH hp hmgt e

/-- Restore the original source intersections from the reduced row. -/
theorem rankOne_global_intersections_of_reduced_unitaryFour :
    Global.sourceS L H ⊓ R = (T : Subgroup G) ⊓ L ∧
      Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = (2^m)^6 :=
  unitaryFour_original_intersections_of_reduced_iso d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm hmgt point e

/-- The existing native placement consumer now needs only the reduced
comparison; the original-marking premise has been discharged. -/
theorem rankOne_global_involution_placement_of_reduced_unitaryFour
    (x : G) (hx : x ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) (hx2 : x^2=1) :
    (∃ g ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0,
      g*x*g⁻¹ ∈ R.pCoreIn 2) ∨
    (∃ g ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1,
      g*x*g⁻¹ ∈ L.pCoreIn 2) := by
  obtain ⟨f⟩ := exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2)
    m hm hmgt point e
  exact D.rankOne_global_original_unitaryFour_involution_placement
    h hmany hn hpsl hH d hp m hm point f x hx hx2

/-- A reduced U₄ marking is incompatible with the actual selected diagram
layer under the original normalized-Borel hypothesis. -/
theorem rankOne_global_not_reduced_unitaryFour_of_layer
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hl : Global.NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) : False :=
  not_reduced_unitaryFour_of_layer d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm hmgt point e hN hl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
