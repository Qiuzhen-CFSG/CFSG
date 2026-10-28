module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourLeftCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourFieldDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNativeApplication

/-!
# The original U₄ action kernel in Chapter 12

For every actual preparation and selected perfect R, the left join-core is
O₂(L) times C_S(L), with trivial intersection. Its Hermitian action
has exactly the original join-core as kernel. The full outer index is
|C_S(L)| or twice this order; the right join-core has the corresponding
q⁵ multiple. The same original marking makes C_S(L) fix the whole native
left residual. The reduced-row application constructs that marking using
the already-proved DGS restoration.

This isolates the remaining native centralizer obstruction without assuming
S=T, R=O²(H), or either desired core equality. Eliminating C_S(L), constructing
the complete original comparison, DGS exhaustion and final GlobalExit remain.
Source: Aschbacher--Smith F.1.12, pp.263--264; I.1.6(3), p.408;
5.2.6--7, pp.650--651; Chapter 12, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
include D h hmany hn hpsl hH d hp e

/-- The literal original core action retains exactly O₂(LS) as kernel. -/
theorem rankOne_global_original_unitaryFour_core_action_kernel :
    let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
    (Global.Preparation.originalUnitaryFourCoreAction hi hH.1.1.2).ker =
      ((L ⊔ Global.sourceS L H).pCoreIn 2).subgroupOf (Global.sourceS L H) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_core_action_kernel hi hH.1.1.2 hp m hm point e

/-- The extra original left core is the actual residual centralizer factor. -/
theorem rankOne_global_original_unitaryFour_left_core_factorization :
    (L ⊔ Global.sourceS L H).pCoreIn 2 =
        L.pCoreIn 2 ⊔ (Global.sourceS L H ⊓ centralizer (L : Set G)) ∧
      Disjoint (L.pCoreIn 2) (Global.sourceS L H ⊓ centralizer (L : Set G)) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_left_core_factorization hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_core_disjoint_centralizer hi hH.1.1.2 hp m hm point e⟩

/-- The full original outer index has only its residual centralizer factor left. -/
theorem rankOne_global_original_unitaryFour_outer_centralizer_alternatives :
    ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H) =
        Nat.card (Global.sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) ∨
      ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H) =
        2 * Nat.card (Global.sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_outer_centralizer_alternatives hi hH.1.1.2 hp m hm point e

/-- The original right-core order uses the same residual centralizer. -/
theorem rankOne_global_original_unitaryFour_right_core_card_alternatives :
    Nat.card ((R ⊔ Global.sourceS L H).pCoreIn 2) =
        (2^m)^5 * Nat.card (Global.sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) ∨
      Nat.card ((R ⊔ Global.sourceS L H).pCoreIn 2) =
        2 * (2^m)^5 * Nat.card (Global.sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_right_core_card_alternatives hi hH.1.1.2 hp m hm point e

/-- The remaining centralizer fixes the whole native residual under the
same original endpoint marking, including its full-overlap agreement. -/
theorem rankOne_global_original_unitaryFour_residual_centralizer_native_fixed
    (s : Global.sourceS L H) (hs : s.val ∈ centralizer (L : Set G))
    (x : Global.OriginalUnitaryFour.nativeResidual m hm point) : e.sylowHom s x.val=x.val := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_residual_centralizer_native_fixed hi hH.1.1.2 hp m hm point e s hs x

omit e in
include D h hmany hn hpsl hH d hp in
/-- Genuine reduced U₄ restoration discharges the marking premise in the
original action-kernel reduction for every selected perfect R. -/
theorem rankOne_global_left_core_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point)) :
    (L ⊔ Global.sourceS L H).pCoreIn 2 =
        L.pCoreIn 2 ⊔ (Global.sourceS L H ⊓ centralizer (L : Set G)) ∧
      Disjoint (L.pCoreIn 2) (Global.sourceS L H ⊓ centralizer (L : Set G)) ∧
      (((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H) =
        Nat.card (Global.sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) ∨
      ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H) =
        2 * Nat.card (Global.sourceS L H ⊓ centralizer (L : Set G) : Subgroup G)) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨e⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 hi hH.1.1.2) m hm hmgt point r
  exact ⟨d.original_unitaryFour_left_core_factorization hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_core_disjoint_centralizer hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_outer_centralizer_alternatives hi hH.1.1.2 hp m hm point e⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
