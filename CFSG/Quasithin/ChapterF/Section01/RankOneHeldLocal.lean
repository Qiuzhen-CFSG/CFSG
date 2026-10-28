module
public import CFSG.Quasithin.ChapterF.Section01.RankOneHeldSections
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Held.TwoLocalCandidates.OrderObstruction
public import Theory.SpecificGroups.Held.TwoLocalCandidates.SeventeenFree

/-!
# Held has no normalized source rank-one local component

The existing Held order bound restricts the intrinsic two-core quotient
to PSL₂(4), PSL₂(8), or PSL₂(16). A trivial two-core would make a full
Held Sylow act faithfully on that quotient; its automorphism order has
insufficient two-part. The nontrivial characteristic two-core puts both
the original local component and its full normalizing Sylow in a two-local.
The native 63 and 17 obstructions exclude the latter two fields, and the
proved local A₅ exclusion handles the first.

This supplies the smaller changed-Sylow containing-component application
in Chapter6 without a full Held order or simplicity certificate.
Source: Aschbacher–Smith A.3.12 and 5.2.2, pp.47–48 and 648–649,
and the native Held geometry in GLS3 Table 5.3p (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.HeldLocal
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

private theorem binary_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^k))
    (hE : IsEvenCharacteristicAt S) (h128 : 128 ∣ Nat.card S) : pCore 2 B ≠ ⊥ := by
  intro hc
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := k) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let a : B ≃* PSL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; rcases hk with rfl | rfl | rfl <;> decide)
  let : IsSimpleGroup B := a.isSimpleGroup
  let := hl.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hl hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨x.property,?_⟩
    change inclusion hn x ∈ B.normalizerMonoidHom.ker at hx
    rw [normalizerMonoidHom_ker] at hx
    exact hx
  have haut : Nat.card (MulAut B) ∣ (2^k * ((2^k)^2-1)) * k := by
    rw [Nat.card_congr (MulAut.congr a).toEquiv]
    exact Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd (n := k) hF
  have hh := h128.trans ((card_dvd_of_injective f hinj).trans haut)
  rcases hk with rfl | rfl | rfl <;> norm_num at hh

private theorem binary_card {X : Type*} [Group X] {k : ℕ}
    (hm : ClassicalGroup.IsPSL X 2 (2^k)) : Nat.card X = 2^k * ((2^k)^2-1) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := k) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1),mul_one,hF] at hc
  exact (Nat.card_congr e.toEquiv).trans hc

/-- No full-Sylow-normalized local C-component in the actual Held carrier
has a source rank-one intrinsic two-core quotient. -/
theorem not_rankOne_model (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He)) :
    ¬ IsRankOneModel (B ⧸ pCore 2 B) := by
  intro hm
  have hns : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
    let : Group.IsSolvable B := Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
      (QuotientGroup.mk' (pCore 2 B)) (by simp)
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup Held.He) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  have hd : Nat.card (B ⧸ pCore 2 B) ∣ 16121548800 :=
    (card_quotient_dvd_card _).trans (B.card_subgroup_dvd_card.trans
      (Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
        (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)))
  have h128 : 128 ∣ Nat.card S := by
    apply S.pow_dvd_card_of_pow_dvd_card (n := 7)
    apply dvd_trans (b := Nat.card Held.TwoLocalCandidates.max5)
    · rw [Held.InvolutionFixedData.TwoB.max5_card]; decide
    · exact card_subgroup_dvd_card _
  have hcore {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4)
      (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^k)) : pCore 2 B ≠ ⊥ :=
    binary_core_ne_bot S B hl hn hk hm (MainConverse.SporadicLocal.he_evenCharacteristic S) h128
  have hlocal (hc : pCore 2 B ≠ ⊥) :
      IsTwoLocal (normalizer (B.pCoreIn 2 : Set Held.He)) ∧
      (S : Subgroup Held.He) ≤ normalizer (B.pCoreIn 2 : Set Held.He) ∧
      B ≤ normalizer (B.pCoreIn 2 : Set Held.He) := by
    have hU : B.pCoreIn 2 ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
    have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
    exact ⟨⟨B.pCoreIn 2,hU,pCore_isPGroup.map B.subtype,rfl⟩,
      hn.trans hnorm,B.le_normalizer.trans hnorm⟩
  rcases hm.held_section hns hd with h4 | h8 | h16
  · have hc := hcore (.inl rfl) h4
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := h4
    exact FiveLocalFF.Held.not_section (MulEquiv.refl _) S B hl hn hc
      (e.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
  · obtain ⟨hN,hSN,hBN⟩ := hlocal (hcore (.inr (.inl rfl)) h8)
    apply Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal S _ hN hSN
    apply dvd_trans _ (card_dvd_of_le hBN)
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 B))
    rw [binary_card (k := 3) h8]; decide
  · obtain ⟨hN,hSN,hBN⟩ := hlocal (hcore (.inr (.inr rfl)) h16)
    apply Held.TwoLocalCandidates.not_seventeen_dvd_card_twoLocal S _ hN hSN
    apply dvd_trans _ (card_dvd_of_le hBN)
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 B))
    rw [binary_card (k := 4) h16]; decide

/-- Equivalence transport preserves the full Sylow, original local component,
and its intrinsic two-core quotient. -/
theorem not_rankOne (e : G ≃* Held.He) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) :
    ¬ IsRankOneModel (B ⧸ pCore 2 B) := by
  intro hm
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  let b := e.subgroupMap B
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact not_rankOne_model (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom)) (hm.of_equiv q.symm)

end CFSG.Quasithin.ChapterF.Source.HeldLocal
