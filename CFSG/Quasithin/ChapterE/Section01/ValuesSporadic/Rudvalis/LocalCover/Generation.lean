module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair.Definitions

/-!
# Generation by the aligned Rudvalis local pair

The literal max4 and the prescribed conjugate of max6 generate the model,
assuming its simplicity. Its two-core is trivial: otherwise simplicity makes
the whole model a two-group, contrary to the odd divisor of max4's order.
An odd-index maximal subgroup therefore has one of the two certified local
isomorphism types, by the nontrivial-two-core and radical-normalizer cover.

If the join of the two locals were proper, place it in a maximal subgroup.
It has odd index since max4 contains an ambient Sylow two-subgroup. Either
local isomorphism type then forces one of the orders 344064 and 245760 to
divide the other, which is impossible. The second local is compared with
max6 through the actual conjugation equivalence.

This supplies the generation premise of
`exists_local_cover_of_invariant_pair`; the extension-cover assembly supplies
simplicity through its original equivalence with the simple normal subgroup.
Source: Aschbacher–Smith E.1.14(5), printed p.214; GLS3 Table 5.3r,
printed p.279; the [Asc86b] coverage certificates used by the imports.
-/

open Subgroup
open Rudvalis Rudvalis.SylowOvergroups

namespace CFSG.Quasithin.ChapterE.Rudvalis.LocalCover

private theorem model_twoCore [IsSimpleGroup Model] : pCore 2 Model = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 Model) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 Model := by
      have ht : IsPGroup 2 (⊤ : Subgroup Model) := h ▸ pCore_isPGroup
      exact ht.of_equiv topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hthree : 3 ∣ Nat.card Model :=
      (show 3 ∣ Nat.card max4 by rw [max4_card]; decide).trans max4.card_subgroup_dvd_card
    rw [hn] at hthree
    have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
    norm_num at this

/-- The two concrete locals generate Rudvalis under the simplicity hypothesis
supplied by the simple normal subgroup in the extension-cover application. -/
public theorem locals_sup_eq_top [IsSimpleGroup Model] :
    SylowInvariantPair.locals 0 ⊔ SylowInvariantPair.locals 1 = ⊤ := by
  by_contra hproper
  obtain ⟨M, hM, hjoin⟩ :=
    (eq_top_or_exists_le_coatom
      (SylowInvariantPair.locals 0 ⊔ SylowInvariantPair.locals 1)).resolve_left hproper
  have hfirst : SylowInvariantPair.locals 0 ≤ M := le_sup_left.trans hjoin
  have hsecond : SylowInvariantPair.locals 1 ≤ M := le_sup_right.trans hjoin
  obtain ⟨S, hS⟩ := max4ContainsSylow
  have hodd : ¬ 2 ∣ M.index := fun h =>
    S.not_dvd_index (h.trans (index_dvd_of_le (hS.trans hfirst)))
  have hcover := oddIndexMaximalCover_of_twoCore_of_radicalCover model_twoCore
    CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    oddIndexMaximalRadicalCover
  have hMtype : Nonempty (M ≃* max4) ∨ Nonempty (M ≃* max6) := hcover M hM hodd
  rcases hMtype with hfour | hsix
  · have hd := card_dvd_of_le hsecond
    rw [Nat.card_congr SylowInvariantPair.secondEquiv.toEquiv,
      Nat.card_congr hfour.some.toEquiv, max6_card, max4_card] at hd
    norm_num at hd
  · have hd := card_dvd_of_le hfirst
    rw [Nat.card_congr SylowInvariantPair.firstEquiv.toEquiv,
      Nat.card_congr hsix.some.toEquiv, max4_card, max6_card] at hd
    norm_num at hd

end CFSG.Quasithin.ChapterE.Rudvalis.LocalCover
