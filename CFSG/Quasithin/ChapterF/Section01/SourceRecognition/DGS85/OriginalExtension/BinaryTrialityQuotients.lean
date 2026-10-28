module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Overlap
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# Original local quotient filters for binary triality restoration

The literal inclusion of an original local factor into its full parabolic
induces an injection on two-core quotients. The same map in the DGS reduced
pair bounds the unchanged original local quotient. A source rank-one group
whose order divides 42 is PSL₂(2); a nonsolvable one whose order divides 504
is PSL₂(8). The proofs retain the small Suzuki, both unitary, and dihedral
alternatives until their actual order divisibilities exclude them.

These filters feed binary triality original restoration, recovering the
local odd field degrees from a marked reduced comparison rather than assuming
local-factor markings. Source: DGS (1985), (15.2), pp.226–228, especially the
binary triality obstruction on p.228; Aschbacher–Smith F.1.9–12, pp.261–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryTriality

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem linear_card {n : ℕ} (h : ClassicalGroup.IsPSL X 2 (2^n)) :
    Nat.card X = 2^n * ((2^n)^2 - 1) := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hcard := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hc] at hcard
  exact (Nat.card_congr e.toEquiv).trans hcard

omit [Finite X] in
/-- The central binary triality quotient order eliminates every source
rank-one family except PSL₂(2), including both unitary conventions. -/
theorem linear_one_of_card_dvd_42 (h : IsRankOneModel X)
    (hd : Nat.card X ∣ 42) : ClassicalGroup.IsPSL X 2 (2^1) := by
  cases h with
  | linear n hn he =>
    have hd2 : 2^n ∣ 42 := by
      rw [linear_card he] at hd
      exact (dvd_mul_right _ _).trans hd
    have hn1 : n = 1 := by
      by_contra hh
      have : 4 ∣ 42 := (pow_dvd_pow 2 (show 2 ≤ n by omega)).trans hd2
      norm_num at this
    simpa only [hn1] using he
  | suzuki m he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    by_cases hm : m = 0
    · subst m
      rw [BenderSuzuki.MatrixGroups.suzukiZero_card] at hd
      norm_num at hd
    · rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)] at hd
      have hh : 4 ∣ (2^(2*m+1))^2 := by
        change 2^2 ∣ (2^(2*m+1))^2
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      have : 4 ∣ 42 := (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hh _) _).trans hd
      norm_num at this
  | projective_unitary n hn he =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := he
    have hh := BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder.cube_dvd_card_projective
      J (by omega : n ≠ 0) hF hj
    rw [← Nat.card_congr e.toEquiv] at hh
    have h8 : 8 ∣ (2^n)^3 := by
      change 2^3 ∣ (2^n)^3
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have : 8 ∣ 42 := h8.trans (hh.trans hd)
    norm_num at this
  | special_unitary n hn he =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := he
    have hh := (BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder.cube_dvd_card_projective
      J (by omega : n ≠ 0) hF hj).trans
      (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)
    rw [← Nat.card_congr e.toEquiv] at hh
    have h8 : 8 ∣ (2^n)^3 := by
      change 2^3 ∣ (2^n)^3
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have : 8 ∣ 42 := h8.trans (hh.trans hd)
    norm_num at this
  | dihedral he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hd
    norm_num at hd

/-- Nonsolvability and the arm quotient order force precisely PSL₂(8). -/
theorem linear_three_of_card_dvd_504 (h : IsRankOneModel X)
    (hns : ¬ Group.IsSolvable X) (hd : Nat.card X ∣ 504) :
    ClassicalGroup.IsPSL X 2 (2^3) := by
  obtain ⟨n,hn,hn3,he⟩ := h.binary_of_small_twoPart hns
    (fun hh => (by decide : ¬ 16 ∣ 504) (hh.trans hd))
  have hn' : n = 3 := by
    by_contra hh
    have hn2 : n = 2 := by omega
    rw [linear_card he,hn2] at hd
    norm_num at hd
  simpa only [hn'] using he

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem local_core_mem (h : HypothesisF11 L S) (i : Fin 2) (x : L i) :
    inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) x ∈
      pCore 2 (parabolic L S i) ↔ x ∈ pCore 2 (L i) := by
  rw [← mem_map_iff_mem (f := (parabolic L S i).subtype) (parabolic L S i).subtype_injective,
    ← mem_map_iff_mem (f := (L i).subtype) (L i).subtype_injective]
  change x.val ∈ twoCore (parabolic L S i) ↔ x.val ∈ twoCore (L i)
  rw [← h.local_inf_parabolic_core i]
  exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩

/-- The original local core quotient injects into its full endpoint quotient,
through the literal inclusion and its unchanged intrinsic two-core. -/
def localQuotientMap (h : HypothesisF11 L S) (i : Fin 2) :
    (L i ⧸ pCore 2 (L i)) →* (parabolic L S i ⧸ pCore 2 (parabolic L S i)) :=
  QuotientGroup.map _ _ (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left))
    (fun x hx => (local_core_mem h i x).mpr hx)

theorem localQuotientMap_mk (h : HypothesisF11 L S) (i : Fin 2) (x : L i) :
    localQuotientMap h i (QuotientGroup.mk x) = QuotientGroup.mk
      (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) x) := by rfl

theorem localQuotientMap_injective (h : HypothesisF11 L S) (i : Fin 2) :
    Function.Injective (localQuotientMap h i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H x =>
    change localQuotientMap h i (QuotientGroup.mk x) = 1 at hz
    rw [localQuotientMap_mk,QuotientGroup.eq_one_iff,local_core_mem h i x] at hz
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hz)

/-- Reduced endpoint recognition bounds the same original local quotient;
the local factor is unchanged by the DGS reduction. -/
theorem local_quotient_card_dvd_reduced (h : HypothesisF11 L S) (i : Fin 2) :
    Nat.card (L i ⧸ pCore 2 (L i)) ∣ Nat.card
      (parabolic L (SuzukiContainment.reducedSylow L S) i ⧸
        pCore 2 (parabolic L (SuzukiContainment.reducedSylow L S) i)) :=
  card_dvd_of_injective _ (localQuotientMap_injective (SuzukiContainment.reduced_hypothesis h) i)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryTriality
