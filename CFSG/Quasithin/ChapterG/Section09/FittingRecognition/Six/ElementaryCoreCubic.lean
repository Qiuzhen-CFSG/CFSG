module
public import Theory.Representation.NormalNineDegreeSix
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeSectionSource

/-!
# A normal cubic from the elementary degree-six core

For an elementary three-core of order 27, its self-centralizing binary
six-space action identifies the generalized Fitting subgroup. A.1.31(3)
applied to the literal SQTK covering map supplies a proper nonzero normal
subgroup. Its order is three or nine; the degree-six fixed-space argument
settles the latter case.

Source: Aschbacher--Smith G.9.4, printed p.355, and A.1.31(3), pp.27--28.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual covering-group rank bound forces a normal cubic in the
self-centralizing elementary 27-core case. -/
theorem normal_cubic_of_elementary_core_centralizer
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2) (hd : finrank (ZMod 2) V = 6)
    [IsElementaryAbelian 3 (pCore 3 G)] (hB : Nat.card (pCore 3 G) = 27)
    (hcentral : centralizer (pCore 3 G : Set G) ≤ pCore 3 G) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  have hF : generalizedFitting G = pCore 3 G :=
    generalizedFitting_eq_pCore_of_selfCentralizing 3 hcentral
  have hr2 : 1 < primeRank 2 G := by
    by_contra hh
    have hc := (primeRank_le_iff_elementary_card_le G).mp (Nat.le_of_not_gt hh) A h.elementary
    rw [h.card_actor] at hc
    norm_num at hc
  obtain ⟨c⟩ := h.quotient
  obtain ⟨R,hRn,hRne,hRB⟩ := ChapterA.lemma_A_1_31_3_of_surjective
    c.projection c.surjective (c.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    hF inferInstance hB hr2
  let : R.Normal := hRn
  let : IsElementaryAbelian 3 R := IsElementaryAbelian.of_injective
    (Subgroup.inclusion hRB.le) (Subgroup.inclusion_injective hRB.le)
  obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hRB.le).exists_card_eq
  have hn0 : n ≠ 0 := by
    intro he
    exact hRne (card_eq_one.mp (by simpa [he] using hn))
  have hn3 : n < 3 := by
    by_contra hh
    have hc : Nat.card (pCore 3 G) ≤ Nat.card R := by
      rw [hB,hn]
      exact Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ n)
    exact hRB.ne (eq_of_le_of_card_ge hRB.le hc)
  have hnalt : n = 1 ∨ n = 2 := by omega
  rcases hnalt with rfl | rfl
  · exact ⟨R,hRn,by simpa using hn⟩
  · let := h.irreducible
    have hc : Nat.card R = 9 := by simpa using hn
    obtain ⟨C,_,hCn,hCc⟩ :=
      Representation.NormalNineDegreeSix.exists_normal_cubic_of_irreducible ρ h.faithful R hc hd
    exact ⟨C,hCn,hCc⟩

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
