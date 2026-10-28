module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.CoreRank
public import Theory.GroupTheory.AbelianThreeCubic

/-!
# The non-elementary abelian three-core in degree six

The original source representation supplies both the bound 81 on the
three-core order and its elementary subgroup of order 27 above rank two.
For an abelian non-elementary core, cubing then produces a characteristic
cubic subgroup. Its image in the original acting group is normal.
Consequently the source no-normal-cubic hypothesis forces this core to
be elementary. No monomial or Sylow representation model is assumed.

Source: Aschbacher--Smith G.9.4, printed p.355; applied in 14.3.15.
-/

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual non-elementary abelian high-rank three-core supplies a
normal cubic subgroup of the original acting group. -/
public theorem source_six_abelian_nonelementary_core_normal_cubic
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hd : Module.finrank (ZMod 2) V = 6)
    (hr : 2 < primeRank 3 (pCore 3 G))
    (hab : IsMulCommutative (pCore 3 G))
    (hne : ¬ IsElementaryAbelian 3 (pCore 3 G)) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 ∧ C ≤ pCore 3 G := by
  obtain ⟨E,hE,hEc⟩ := source_six_rank_three_has_elementary_twentyseven h hd hr
  let : IsElementaryAbelian 3 E := hE
  let : IsMulCommutative (pCore 3 G) := hab
  exact Theory.GroupTheory.AbelianThreeCubic.exists_normal_cubic
    (pCore 3 G) pCore_isPGroup (source_six_threeCore_card_le_eightyone h hd) E hEc hne

/-- The original no-normal-cubic input removes the non-elementary abelian
case above three-rank two. -/
public theorem source_six_abelian_core_elementary_of_no_normal_cubic
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hd : Module.finrank (ZMod 2) V = 6)
    (hr : 2 < primeRank 3 (pCore 3 G))
    (hab : IsMulCommutative (pCore 3 G))
    (hno : ∀ C : Subgroup G, C.Normal → Nat.card C = 3 → False) :
    IsElementaryAbelian 3 (pCore 3 G) := by
  by_contra hne
  obtain ⟨C,hCn,hCc,_⟩ := source_six_abelian_nonelementary_core_normal_cubic h hd hr hab hne
  exact hno C hCn hCc

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
