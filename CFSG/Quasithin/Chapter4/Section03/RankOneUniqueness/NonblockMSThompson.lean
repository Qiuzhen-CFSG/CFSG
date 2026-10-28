module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreRigidity
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Stellmacher.MaxElementaryOffenderEquality

/-!
# The original MS3 witness for the larger-core rank argument

If the elementary Thompson subgroup of S lay in O₂(KS), heredity would
identify it with the Thompson groups of both O₂(KS) and R=O₂(I).
It would be characteristic in R and normal in KR, contradicting the
literal relative MS3 condition. Thus a maximum elementary subgroup E
of the original S lies outside O₂(KS).

For the existing elementary centralizer factor C, maximality gives
C_C(E)=C∩E and the multiplicative form of the source rank-deficit
inequality. If O₂(KS) differs from Q, C strictly contains its elementary
lift of order 2^(6n), forcing such an outside E to have larger order.
The remaining natural/dual fixed-space estimates and their equality case
must exclude this configuration; no bound on E is assumed here.

All subgroups and relative indices are those of the original MSData.
The full MS/secondary construction and endgame remain with
qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher–Smith C.1.35, printed pp.138–139, applied in original
4.3.11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The genuine MS3 condition forces the original Sylow Thompson group
outside O₂(KS). Normality is relative to KR throughout. -/
theorem MSData.thompson_not_le_joinCore (d : MSData c n) :
    ¬ elementaryAbelianMaxJ (S c) ≤ (K c ⊔ S c).pCoreIn 2 := by
  intro h
  let P := (K c ⊔ S c).pCoreIn 2
  let R := c.I.pCoreIn 2
  let J := K c ⊔ R
  have hPR : P ≤ R := c.block_join_core_le
  have hRS : R ≤ S c := c.core_sylow.le.trans inf_le_left
  have hPS : P ≤ S c := hPR.trans hRS
  have hRP := elementaryAbelianMaxJ_eq_of_intermediate (S c) R (h.trans hPR) hRS
  have hPP := elementaryAbelianMaxJ_eq_of_intermediate (S c) P h hPS
  let C : Subgroup R := elementaryAbelianMaxJ ⊤
  let : C.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hmap : C.map R.subtype = elementaryAbelianMaxJ (S c) := by
    change (elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype = _
    rw [←elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hRP
  have hnorm : (C.map R.subtype |>.subgroupOf J).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hmap,←hPP]
    have hJKS : J ≤ K c ⊔ S c := sup_le le_sup_left (hRS.trans le_sup_right)
    exact hJKS.trans (((K c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
        (pCore 2 (K c ⊔ S c : Subgroup G)))).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ P))
  have hC : C = ⊥ := d.pair.characteristic C inferInstance hnorm
  have hz : elementaryAbelianMaxJ (S c) = ⊥ := by rw [←hmap,hC,Subgroup.map_bot]
  apply elementaryAbelianMaxJ_ne_bot_of_finite_pGroup (S c)
    (T.isPGroup'.to_le inf_le_left) ?_ hz
  intro hs
  have hQ : Q c = ⊥ := bot_unique ((core_le_sylow c).trans hs.le)
  have hc := d.core_card
  rw [hQ,card_bot] at hc
  have hp : 1 < 2^(9*n) := one_lt_pow₀ (by decide) (by have := d.pair.positive; omega)
  omega

/-- The original Sylow contains a maximum elementary subgroup outside
the larger core; every elementary subgroup of that core is no larger. -/
theorem MSData.exists_maxElementary_outside_joinCore (d : MSData c n) :
    ∃ E : Subgroup G, E ∈ elementaryAbelianMaxSubgroups (S c) ∧
      ¬ E ≤ (K c ⊔ S c).pCoreIn 2 := by
  by_contra! hh
  exact d.thompson_not_le_joinCore (sSup_le hh)

omit [Finite G] in
private theorem card_inf_mul_relIndex (X Y : Subgroup G) :
    Nat.card (X ⊓ Y : Subgroup G) * X.relIndex Y = Nat.card Y := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (X ⊓ Y) Y bot_le inf_le_right

/-- Cardinal form of the source rank-deficit inequality, on the original
Sylow and larger core. The fixed subgroup is the literal intersection. -/
theorem MSData.maxElementary_joinCore_deficit (d : MSData c n)
    (A : invariantCoreLifts c) (E : Subgroup G)
    (hE : E ∈ elementaryAbelianMaxSubgroups (S c)) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    C ⊓ Subgroup.centralizer (E : Set G) = C ⊓ E ∧
      E.relIndex C ≤ C.relIndex (P ⊓ E) * P.relIndex E := by
  dsimp only
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let := d.joinCore_liftCentralizer_elementary A
  let : IsElementaryAbelian 2 E := hE.2.1
  have hCS : C ≤ S c := inf_le_left.trans
    (c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left))
  let : IsElementaryAbelian 2 (C ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le (show C ⊓ Subgroup.centralizer (E : Set G) ≤ C from inf_le_left)
  constructor
  · apply le_antisymm
    · exact le_inf inf_le_left (maxElementary_contains_elementary_centralizer
        (S c) E (C ⊓ Subgroup.centralizer (E : Set G)) hE
        (inf_le_left.trans hCS) inf_le_right)
    · exact le_inf inf_le_left (inf_le_right.trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  · have he : C.relIndex (P ⊓ E) * P.relIndex E = C.relIndex E := by
      rw [relIndex_inf_mul_relIndex,inf_eq_left.mpr (show C ≤ P from inf_le_left)]
    rw [he]
    have hcard : Nat.card C ≤ Nat.card E := hE.2.2 C hCS inferInstance
    have hCcard := card_inf_mul_relIndex E C
    have hEcard := card_inf_mul_relIndex C E
    rw [inf_comm E C] at hCcard
    apply Nat.le_of_mul_le_mul_left (c := Nat.card (C ⊓ E : Subgroup G)) _ Nat.card_pos
    rwa [hCcard,hEcard]

/-- Failure of the required larger-core identity forces an actual maximum
Sylow elementary subgroup outside the core to have order greater than 2^(6n).
This retains the concrete witness needed by the source rank calculation. -/
theorem MSData.joinCore_ne_core_forces_large_outside (d : MSData c n) (hn : 1 < n)
    (hne : (K c ⊔ S c).pCoreIn 2 ≠ Q c) :
    ∃ E : Subgroup G, E ∈ elementaryAbelianMaxSubgroups (S c) ∧
      ¬ E ≤ (K c ⊔ S c).pCoreIn 2 ∧ 2^(6*n) < Nat.card E := by
  obtain ⟨A,C,_,hAQ,_,hcard,_,hC,hCe,hP,hi⟩ :=
    d.exists_joinCore_elementary_factorization hn
  have hAC : A ≤ C := hi.ge.trans inf_le_right
  have hlt : Nat.card A < Nat.card C := by
    apply Nat.lt_of_not_ge
    intro hh
    have he := eq_of_le_of_card_ge hAC hh
    apply hne
    rw [hP,←he,sup_eq_left.mpr hAQ.le]
  obtain ⟨E,hE,hEP⟩ := d.exists_maxElementary_outside_joinCore
  refine ⟨E,hE,hEP,?_⟩
  rw [←hcard]
  exact hlt.trans_le (hE.2.2 C (by
    rw [hC]
    exact inf_le_left.trans (c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left))) hCe)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
