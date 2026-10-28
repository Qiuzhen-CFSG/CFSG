module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Cubic rank of Ree involution centralizers

The full linear parabolic has a two-group kernel over SL₂(q) times the
field units. Since q = 2^(2m+1), the units have order prime to three.
The Suzuki parabolic is itself prime to three. Borel–Tits containment
therefore bounds the cubic rank of an involution centralizer by one.
The proved innerness of two-power automorphisms gives the same bound
for their actual fixed groups. Simplicity and perfectness are inherited
from the source component; no model simplicity theorem is assumed.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832, using the
full parabolics of F.1.12 and the intrinsic GLS3 normalizer cover.
-/
public section
open Subgroup Theory.GroupTheory
namespace ReeF4

private theorem units_three_free (m : ℕ) : ¬ 3 ∣ Nat.card (CoefficientField m)ˣ := by
  rw [Nat.card_units,field_card]
  have hfour : 4^m % 3 = 1 := by
    change Nat.ModEq 3 (4^m) 1
    simpa only [one_pow] using (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq : 2^(2*m+1) % 3 = 2 := by
    rw [pow_succ,pow_mul]
    norm_num only [Nat.reducePow] at *
    rw [Nat.mul_mod,hfour]
  have hsub : (2^(2*m+1)-1) % 3 = 1 := by
    generalize 2^(2*m+1) = q at hq ⊢
    omega
  intro hd
  have hz := Nat.dvd_iff_mod_eq_zero.mp hd
  omega

/-- Both full parabolics, with their complementary tori, have cubic rank at most one. -/
theorem parabolic_threeRank_le_one {m : ℕ} (hm : 1 ≤ m) (s : LargeLocalSeeds.Side) :
    primeRank 3 (ConverseParabolics.parabolic m s) ≤ 1 := by
  cases s with
  | suzuki =>
    have hz : primeRank 3 (ConverseParabolics.parabolic m .suzuki) = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr (ConverseParabolics.suzuki_parabolic_three_free hm)
    omega
  | linear =>
    let q := ConverseParabolics.linearProjection hm
    obtain ⟨k,hk⟩ := (ConverseParabolics.linearProjection_ker_isPGroup hm).exists_card_eq
    have hb := primeRank_le_of_coprime_ker 3 q (by
      rw [hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k)
    have hu : primeRank 3 (CoefficientField m)ˣ = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr (units_three_free m)
    rw [primeRank_prod_eq_add,hu,add_zero] at hb
    exact hb.trans (Matrix.SL2.binary_odd_primeRank_le_one (by decide : Odd 3))

/-- Normalizer coverage bounds the actual element centralizer, without classifying involutions. -/
theorem involution_centralizer_threeRank_le_one {m : ℕ} (hm : 1 ≤ m)
    (x : Model m) (hx : orderOf x = 2) :
    primeRank 3 (centralizer ({x} : Set (Model m))) ≤ 1 := by
  have hn : zpowers x ≠ ⊥ := by
    intro h
    have he := zpowers_eq_bot.mp h
    simp [he] at hx
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨g,s,hg⟩ := ConverseParabolics.normalizer_cover hm (zpowers x) hn hp
  have hCN : centralizer ({x} : Set (Model m)) ≤ normalizer (zpowers x : Set (Model m)) := by
    rw [←centralizer_closure ({x} : Set (Model m)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  let C := centralizer ({x} : Set (Model m))
  have hle := (map_mono hCN).trans hg
  rw [primeRank_equiv 3 ((MulAut.conj g).subgroupMap C)]
  exact (primeRank_mono 3 hle).trans (parabolic_threeRank_le_one hm s)

/-- Every involutory automorphism of the large Ree carrier has fixed-group cubic rank at most one. -/
theorem involution_fixed_threeRank_le_one {m : ℕ} (hm : 1 ≤ m)
    [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)]
    (a : MulAut (Model m)) (ha : orderOf a = 2) : primeRank 3 a.fixedSubgroup ≤ 1 := by
  obtain ⟨x,hx⟩ := Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one hm a
    (by simpa only [ha] using pow_orderOf_eq_one a)
  rw [←hx,MulAut.fixedSubgroup_conj]
  apply involution_centralizer_threeRank_le_one hm
  rw [←hx,MulAut.conj_orderOf_of_center_eq_bot center_eq_bot_of_simple_perfect] at ha
  exact ha
end ReeF4
