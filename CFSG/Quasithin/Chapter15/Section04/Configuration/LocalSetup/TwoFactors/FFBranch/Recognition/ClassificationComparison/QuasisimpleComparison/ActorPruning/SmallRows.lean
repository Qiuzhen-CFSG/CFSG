module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning.Models

/-!
# Excluding large binary actors in the first eight retained rows

SL₃(4), SL₄(2), and S₈ each contribute a factor 64 to the order of any
group containing them. Row (2) has order 36 or 108. In rows (3)–(9), the
common subgroup is Sylow and has order at most 16. This eliminates these
rows without identifying the normal offender subgroup with its overgroup.
The remaining rows retain every local and global clause, in either orientation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.18(2–9),
pp.309–310, compared with B.5.1/B.5.6 in the proof of 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.ActorPruning
open GoldschmidtAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D] {A : Type v} [Group A]
variable {G₁ G₂ : Subgroup D}

/-- The rows not eliminated merely by a factor 64 in the actor's order.
This abbreviation preserves every source clause of the original rows. -/
def LargeRowsOrdered (G₁ G₂ : Subgroup D) : Prop :=
  Case10 G₁ G₂ ∨ Case11 G₁ G₂ ∨ Case12 G₁ G₂ ∨ Case13 G₁ G₂

/-- Either source orientation remains available. -/
def LargeRows (G₁ G₂ : Subgroup D) : Prop :=
  LargeRowsOrdered G₁ G₂ ∨ LargeRowsOrdered G₂ G₁

private theorem small_intersection_contradiction
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hd : 64 ∣ Nat.card D)
    (hs : Nat.card (G₁ ⊓ G₂ : Subgroup D) < 64) : False := by
  obtain ⟨S, hS⟩ := ht.intersection_sylow
  have hd' := S.pow_dvd_card_of_pow_dvd_card (show 2 ^ 6 ∣ Nat.card D from hd)
  have hl := Nat.le_of_dvd (Nat.card_pos (α := S)) hd'
  rw [← Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv] at hl
  omega

omit [Finite D] in
private theorem not_case2 (hd : 64 ∣ Nat.card D) (h : Case2 D) : False := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv] at hd
    norm_num [S3, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_perm, Nat.factorial] at hd
  · rw [h.card, HeisenbergPrime.card] at hd
    norm_num [E4, C, Nat.card_prod] at hd

private theorem ordered_large_rows
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hd : 64 ∣ Nat.card D)
    (hr : RemainingOrdered G₁ G₂) : LargeRowsOrdered G₁ G₂ := by
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h
  · exact (not_case2 hd h).elim
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, _, _, _, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv]
    norm_num [E4, C, Nat.card_prod]
  · obtain ⟨_, _, _, _, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [C]
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    apply (small_intersection_contradiction ht hd ?_).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [C]
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A genuine embedding of a large actor rules out rows (2)–(9), retaining
the exact source alternatives and the actual common Sylow subgroup. -/
theorem LargeActorModel.large_rows (ha : LargeActorModel A)
    (i : A →* D) (hi : Function.Injective i)
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Remaining G₁ G₂) :
    LargeRows G₁ G₂ := by
  have hd := ha.sixtyFour_dvd.trans (card_dvd_of_injective i hi)
  rcases hr with hr | hr
  · exact Or.inl (ordered_large_rows ht hd hr)
  · exact Or.inr (ordered_large_rows ht.symm hd hr)

end QuasisimpleComparison.ActorPruning

universe u v
variable {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal

/-- Apply the row exclusion through the literal offender inclusion N → D. -/
theorem ProjectiveLine.ClassifiedAction.largeActor_rows
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : QuasisimpleComparison.ActorPruning.LargeActorModel (offenderSubgroup ρ)) :
    QuasisimpleComparison.ActorPruning.LargeRows G₁ G₂ :=
  ha.large_rows (offenderSubgroup ρ).subtype Subtype.val_injective h.triple h.goldschmidt

/-- Odd divisors pass through the literal quotient D/N because that quotient
is a two-group. This includes the prime cubes used in the degree-three rows. -/
theorem ProjectiveLine.ClassifiedAction.odd_dvd_offender_card_iff
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂) {m : ℕ} (hm : Odd m) :
    m ∣ Nat.card (offenderSubgroup ρ) ↔ m ∣ Nat.card D := by
  constructor
  · exact fun hd => hd.trans (offenderSubgroup ρ).card_subgroup_dvd_card
  · intro hd
    obtain ⟨k, hk⟩ := h.quotient_twoGroup.exists_card_eq
    have he : Nat.card D = Nat.card (offenderSubgroup ρ) * 2 ^ k := by
      rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
    rw [he] at hd
    exact ((Nat.coprime_two_right.mpr hm).pow_right k).dvd_of_dvd_mul_right hd

/-- The same odd-prime-cube obstruction holds in the actual overgroup D,
not only in its offender actor. This discharges the order side of comparisons
with the defining-prime cubes in the odd degree-three models. -/
theorem ProjectiveLine.ClassifiedAction.rankOne_not_odd_prime_cube
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : QuasisimpleComparison.ActorPruning.RankOneActorModel (offenderSubgroup ρ))
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : ¬ p ^ 3 ∣ Nat.card D := by
  intro hd
  exact ha.not_odd_prime_cube hp hne
    ((h.odd_dvd_offender_card_iff ((hp.odd_of_ne_two hne).pow)).mpr hd)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
