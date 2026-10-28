module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import Theory.GroupTheory.QuotientActionCentralizer
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Higher Thompson subgroups in a normal kernel

E.5.5 follows by comparing a member `A` of the higher Thompson family with
`V C_A(V)`, using the sharp cardinal bound proved for B.2.4. The quotient
`G/Q` may act nonfaithfully on `V`: its elementary image has order at least
that of the faithful image in `G/C_G(V)`. Fixed subgroups agree with the
centralizers of full preimages, by `quotientActionCentralizer_image`.

Ranks below are base-two logarithms of elementary group orders. The fixed
codimension is the logarithm of the actual subgroup index, identified with
the difference of ranks by `log_card_sub_log_card_eq_log_relIndex`. No rank-two
restriction is imposed on quotient subgroups: the source's `A²` means all
nonidentity elementary abelian two-subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma E.5.5, printed p.244. Its contrapositive is
used in the proof of 5.1.20 on printed p.644.
-/

open Subgroup Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem card_pow_log (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] : Nat.card E = 2 ^ Nat.log 2 (Nat.card E) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [hn, Nat.log_pow Nat.one_lt_two]

/-- The rank-deficit bound for a quotient whose kernel centralizes `V`.
Unlike the faithful B.2.4 formulation, `Q` may be smaller than `C_G(V)`. -/
public theorem quotient_fixedRank_le_of_thompsonFamily (Q V A : Subgroup G) [Q.Normal] [V.Normal]
    [IsElementaryAbelian 2 V] (hQ : Q ≤ centralizer (V : Set G))
    {j : ℕ} (hA : A ∈ thompsonFamily (⊤ : Subgroup G) j) :
    Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card ↥(V ⊓ centralizer (A : Set G))) ≤
      Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' Q))) + j := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hAj : Nat.card A * 2 ^ j = elementaryAbelianMaxOrder (⊤ : Subgroup G) := by
    rw [hA.2.2.2, ← pow_add, Nat.sub_add_cancel hA.2.2.1, maxOrder_eq_two_pow_rank]
  have hb := (maxElementary_card_bound_and_eq ⊤ V A le_top le_top j hAj
    (QuotientGroup.mk' (centralizer (V : Set G))) (QuotientGroup.ker_mk' _)).1
  have hi := card_map_le_card_map_of_ker_le A
    (QuotientGroup.mk' (centralizer (V : Set G))) (QuotientGroup.mk' Q)
    (by simpa only [QuotientGroup.ker_mk'] using hQ)
  have hc := hb.trans (Nat.mul_le_mul_right (2 ^ j) (Nat.mul_le_mul_left _ hi))
  let _ : IsElementaryAbelian 2 ↥(V ⊓ centralizer (A : Set G)) :=
    IsElementaryAbelian.of_le inf_le_left
  let _ : IsElementaryAbelian 2 (A.map (QuotientGroup.mk' Q)) :=
    IsElementaryAbelian.map _
  rw [card_pow_log V, card_pow_log ↥(V ⊓ centralizer (A : Set G)),
    card_pow_log (A.map (QuotientGroup.mk' Q)), ← pow_add, ← pow_add] at hc
  have hh := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hc
  omega

/-- E.5.5: strict displacement by every nonidentity elementary quotient
subgroup forces the higher Thompson subgroup into the normal kernel. -/
public theorem lemma_E_5_5 (_hG : IsPGroup 2 G) (Q V : Subgroup G) [Q.Normal] [V.Normal]
    (hV : V ≤ omegaOneCenterAmbient Q) (j : ℕ)
    (hbound : ∀ B : Subgroup (G ⧸ Q), IsElementaryAbelian 2 B → B ≠ ⊥ →
      Nat.log 2 (Nat.card B) + j <
        Nat.log 2 ((quotientActionCentralizer V Q B).relIndex V)) :
    thompsonJ (⊤ : Subgroup G) j ≤ Q := by
  let _ : IsElementaryAbelian 2 (omegaOneCenterAmbient Q) :=
    omegaOneCenterAmbient_elementaryAbelian Q
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hV
  have hQV : Q ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mp
    intro v hv
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff Q v).mp (hV hv)).2.2
  apply sSup_le
  intro A hA
  by_contra hn
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hne : A.map (QuotientGroup.mk' Q) ≠ ⊥ := by
    intro hh
    apply hn
    have hker := (Subgroup.map_eq_bot_iff A).mp hh
    simpa only [QuotientGroup.ker_mk'] using hker
  have hlt := hbound (A.map (QuotientGroup.mk' Q)) (IsElementaryAbelian.map _) hne
  rw [quotientActionCentralizer_image V Q A hQV] at hlt
  rw [← log_card_sub_log_card_eq_log_relIndex V _ inf_le_left] at hlt
  have hle := quotient_fixedRank_le_of_thompsonFamily Q V A hQV hA
  omega

/-- The contrapositive used in 5.1.20: a higher Thompson subgroup escaping
`Q` supplies a nonidentity elementary quotient subgroup with small displacement. -/
public theorem exists_quotient_elementary_of_thompson_not_le (hG : IsPGroup 2 G)
    (Q V : Subgroup G) [Q.Normal] [V.Normal]
    (hV : V ≤ omegaOneCenterAmbient Q) (j : ℕ)
    (hJ : ¬ thompsonJ (⊤ : Subgroup G) j ≤ Q) :
    ∃ B : Subgroup (G ⧸ Q), IsElementaryAbelian 2 B ∧ B ≠ ⊥ ∧
      Nat.log 2 ((quotientActionCentralizer V Q B).relIndex V) ≤
        Nat.log 2 (Nat.card B) + j := by
  classical
  by_contra hn
  apply hJ
  apply lemma_E_5_5 hG Q V hV j
  intro B he hne
  exact Nat.lt_of_not_ge (fun hle => hn ⟨B, he, hne, hle⟩)

end CFSG.Quasithin.ChapterE
