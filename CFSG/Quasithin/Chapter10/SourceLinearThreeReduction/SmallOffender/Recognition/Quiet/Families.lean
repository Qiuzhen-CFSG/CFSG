module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.RankBound
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.BinaryDegree
public import Theory.Representation.SL2.MovedElementaryDegree
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import GorensteinWalter.PSL2Cardinality

/-!
# Quiet small-offender exclusions without module markings

For the actual J₁ quotient, innerness of automorphisms bounds their two-rank
by three, whereas a faithful binary action has degree at least ten. For
SL₂(2ⁿ), n≥4, the automorphism two-rank is at most n and the nonzero fully
moved subgroup has degree at least 2n. The general TI offender bound is
incompatible with either lower bound. No irreducibility or selected natural
module is assumed; all actions and two-core quotients are literal.

Quiet.FamilySelection applies these exclusions to the original survivor.
The independent half-Sylow source remains with its existing producer.
Source: Aschbacher--Smith 1.2.1(3), 10.1.1 and 10.2.12, pp.504,741,754--755.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem janko_one_automorphism_rank : primeRank 2 (MulAut Janko1.Model) ≤ 3 := by
  have hz : center Janko1.Model = ⊥ := by
    rcases (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp ht)).elim
  let e := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨MulAut.conj_injective_of_center_eq_bot hz,Janko1.OuterCertificate.aut_inner⟩
  rw [←primeRank_equiv 2 e]
  obtain ⟨E,_,hE⟩ := exists_elementaryAbelian_card_primeRank (G := Janko1.Model) (p := 2)
  have hd := E.card_subgroup_dvd_card
  rw [hE,Janko1.card_model] at hd
  by_contra! hn
  have h16 : 16 ∣ 175560 := (pow_dvd_pow 2 (by omega : 4 ≤ primeRank 2 Janko1.Model)).trans hd
  norm_num at h16

/-- The actual J₁ branch is impossible under the original quiet prefix. -/
theorem no_quiet_janko_one
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model) : False := by
  have hr : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ 3 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact janko_one_automorphism_rank
  have hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Janko1.card_model]
    decide
  have hu := quiet_moved_card_le_of_automorphism_rank D c hJ hNL hthree hr
  let := source_full_moved_elementary D
  obtain ⟨ρ,s,hf,_⟩ := exists_moved_quotient_action D c.nonnormal e
  have hd := Janko1.ten_le_binary_finrank ρ hf
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)
  have hcard : Nat.card Q = 2 ^ Module.finrank (ZMod 2) Q := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [←hcard] at hp
  have hc := Nat.card_le_card_of_surjective s.coordinates s.onto
  change Nat.card (Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)) ≤
      Nat.card (⁅D.fullModule,L⁆ : Subgroup G) at hc
  have htotal : 2 ^ 10 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := hp.trans hc
  norm_num at hu htotal
  omega

omit [Finite G] in
/-- Every binary rank-one quotient has order divisible by three. -/
theorem binary_rank_one_three_dvd
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {n : ℕ} (hF : Nat.card F = 2 ^ n) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hF]
  have hp : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul]
    rfl
  rw [hp]
  exact dvd_mul_of_dvd_right (Nat.sub_one_dvd_pow_sub_one 4 n) _

/-- The larger even-field rank-one branches are impossible without a natural marking. -/
theorem no_quiet_large_binary_rank_one
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2 ^ n) : False := by
  have hr : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ n := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le (by omega) hF
  have hu := quiet_moved_card_le_of_automorphism_rank D c hJ hNL
    (binary_rank_one_three_dvd e hF) hr
  let := source_full_moved_elementary D
  let : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hl := SL2.moved_subgroup_card_bound L ⁅D.fullModule,L⁆
    (source_full_moved_le_component D) (source_full_moved_ne_bot D)
    (source_full_moved_eq_commutator D) e (by omega : n ≠ 0) hF
  have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : n+3 < 2*n)
  exact (not_lt_of_ge (hl.trans hu)) hlt

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
