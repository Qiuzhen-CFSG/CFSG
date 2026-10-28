module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourFieldDegree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourCenterKernel

/-!
# The original U₄ fixed line and field degree in Chapter 12

For every actual preparation and selected perfect R, the center of O₂(R)
is exactly the fixed line of T∩L on O₂(L), with its ambient embeddings
retained. The original S centralizes this line, so its left-quotient
field image has order at most two. The exact field kernel is retained as
S∩(L O₂(LS)); no equality O₂(LS)=O₂(L) is inserted.

These are literal applications of the normalized-Borel restriction in
F.1.12, pp.263--264, using F.4.29's Hermitian action and the original
Chapter 12 setup, p.795 (`refs/quasithin.pdf`). The full extension bound,
compatible comparison, DGS exhaustiveness and final GlobalExit remain.
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


/-- The same selected right core supplies the whole original fixed line. -/
theorem rankOne_global_original_unitaryFour_fixed_core :
    L.pCoreIn 2 ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) =
      ((center (pCore 2 R)).map (pCore 2 R).subtype).map R.subtype := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_fixed_core_eq_right_core_center hi hH.1.1.2 hp m hm point e

/-- Inner squares hold on the literal original left quotient. -/
theorem rankOne_global_original_unitaryFour_left_quotient_square_inner
    (u : Global.sourceS L H) :
    let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
    (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom ⟨u.val,
        ((Global.sourceS_le_sylow hi.sylow_normalizes hH.1.1.2).trans hi.sylow_normalizes) u.property⟩))^2 ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_left_quotient_square_inner hi hH.1.1.2 hp m hm point e u

/-- The original field image has at most two elements, with its entire
kernel identified before removing the left join-core. -/
theorem rankOne_global_original_unitaryFour_left_field_degree
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
    let φ := Global.Preparation.originalUnitaryFourLeftFieldAction hi hH.1.1.2 q
    (∀ u : Global.sourceS L H, (φ u)^2=1) ∧ Nat.card φ.range ≤ 2 ∧
      φ.ker = (L ⊔ (L ⊔ Global.sourceS L H).pCoreIn 2).subgroupOf (Global.sourceS L H) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_left_field_square hi hH.1.1.2 hp m hm point e q,
    d.original_unitaryFour_left_field_card_le_two hi hH.1.1.2 hp m hm point e q,
    Global.Preparation.original_unitaryFour_left_field_kernel hi hH.1.1.2 q⟩

/-- The degree bound retains O₂(LS) in the denominator; removing it is
still required to bound the full original extension. -/
theorem rankOne_global_original_unitaryFour_left_core_quotient_index_le_two :
    (L ⊔ (L ⊔ Global.sourceS L H).pCoreIn 2).relIndex (Global.sourceS L H) ≤ 2 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_left_core_quotient_index_le_two hi hH.1.1.2 hp m hm point e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
