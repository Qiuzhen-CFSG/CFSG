module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves


/-!
# A fixed positive word in the middle Ree root block

For the middle long and short simple roots α, β, put γ = α + β and
δ = α + 2β. The actual exceptional duality exchanges α with β and γ
with δ. Assuming the explicit B₂ root swap, the positive word
`x_α(1) x_β(1) x_γ(1)` also equals `x_β(1) x_α(1) x_δ(1)` and is fixed
by the Ree twist. Commutation of δ with α, β and γ then gives its square
`x_γ(1) x_δ(1)`. Those commutations are proved from the actual integral
root operators and absent root sums; only the B₂ swap remains a premise.

Source: the middle-node root calculation underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`. This is a
conditional root calculation in the full Ree group, including q = 2.
-/

@[expose] public section

namespace ReeF4.Parabolics.SeedGeneration.SuzukiWitness
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RadicalCoordinates.FixedCoordinates LargeLocalSeeds Subgroup
open WordRelations
noncomputable section

def alpha : F4Chevalley.Root := typeF4SimpleRootIndex 1
def beta : F4Chevalley.Root := typeF4SimpleRootIndex 2
def gamma : F4Chevalley.Root := typeF4RootPairing.reflectionPerm alpha beta
def delta : F4Chevalley.Root := typeF4RootPairing.reflectionPerm beta alpha

theorem alpha_pos : typeF4RootPairing_base.IsPos alpha :=
  typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv 1).property
theorem beta_pos : typeF4RootPairing_base.IsPos beta :=
  typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv 2).property
theorem alpha_long : IsLongRoot alpha :=
  (typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide)
theorem beta_short : IsShortRoot beta := by
  have h := (exceptionalRootPermutation_long_iff alpha).mp alpha_long
  simpa [alpha, beta, exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev] using h

theorem gamma_val : gamma.val = alpha.val + beta.val := by
  change (typeF4RootPairing.root (typeF4RootPairing.reflectionPerm alpha beta)) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4RootPairing_root, typeF4RootPairing_root]
  ext i
  fin_cases i <;> norm_num [alpha, beta, typeF4CorootScale_simpleRoot,
    typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]
theorem delta_val : delta.val = alpha.val + (2 : ℝ) • beta.val := by
  change (typeF4RootPairing.root (typeF4RootPairing.reflectionPerm beta alpha)) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4RootPairing_root, typeF4RootPairing_root]
  ext i
  fin_cases i <;> norm_num [alpha, beta, typeF4CorootScale_simpleRoot,
    typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]
theorem gamma_pos : typeF4RootPairing_base.IsPos gamma := alpha_pos.add beta_pos gamma_val
theorem delta_pos : typeF4RootPairing_base.IsPos delta :=
  gamma_pos.add beta_pos (by change delta.val = gamma.val + beta.val; rw [delta_val, gamma_val, two_smul]; abel)
theorem gamma_short : IsShortRoot gamma := by
  exact (not_congr (isLongRoot_reflection_iff alpha beta)).mpr beta_short
theorem delta_long : IsLongRoot delta := by
  exact (isLongRoot_reflection_iff beta alpha).mpr alpha_long
theorem dual_alpha : exceptionalRootPermutation alpha = beta := exceptionalRootPermutation_simple 1
theorem dual_gamma : exceptionalRootPermutation gamma = delta := by
  rw [gamma, exceptionalRootPermutation_reflection, dual_alpha]
  congr 1
  exact exceptionalRootPermutation_simple 2

theorem ab_dot : dot alpha.val beta.val = -1 := by
  norm_num [alpha, beta, typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
theorem dc_dot : dot delta.val gamma.val = 1 := by
  rw [delta_val, gamma_val]
  norm_num [alpha, beta, typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
theorem db_dot : dot delta.val beta.val = 1 := by
  rw [delta_val]
  norm_num [alpha, beta, typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem root_mul_self (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 1 * rootGeneratorInGroup m r 1 = 1 := by
  apply Subtype.ext
  change F4Chevalley.rootCurve r 1 * F4Chevalley.rootCurve r 1 = 1
  rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero, F4Chevalley.rootCurve_zero]

private theorem delta_alpha_commute (m : ℕ) :
    Commute (rootGeneratorInGroup m delta 1) (rootGeneratorInGroup m alpha 1) := by
  have hn : dot (delta.val + alpha.val) (delta.val + alpha.val) = 4 := by
    rw [delta_val]
    norm_num [alpha, beta, typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot,
      Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  have h0 : delta.val + alpha.val ≠ 0 := by
    intro he
    rw [he] at hn
    norm_num [dot] at hn
  have hs : delta.val + alpha.val ∉ Set.range typeF4RootPairing.root := by
    rintro ⟨r, hr⟩
    have hb : dot r.val r.val ≤ 2 := by
      by_cases h : IsLongRoot r
      · rw [isLongRoot_norm r h]
      · rw [isShortRoot_norm r h]; norm_num
    change r.val = delta.val + alpha.val at hr
    rw [hr, hn] at hb
    norm_num at hb
  apply Subtype.ext
  exact (MatrixRelations.rootCurves_commute_of_operators_commute delta alpha
    (MatrixRelations.positive_operators_commute delta alpha delta_pos alpha_pos h0 hs)
    (1 : CoefficientField m) 1).eq

private theorem delta_beta_commute (m : ℕ) :
    Commute (rootGeneratorInGroup m delta 1) (rootGeneratorInGroup m beta 1) :=
  mixedRootCommutation m delta beta delta_pos beta_pos delta_long beta_short
    (by rw [db_dot]; norm_num) 1 1

private theorem gamma_delta_commute (m : ℕ) :
    Commute (rootGeneratorInGroup m gamma 1) (rootGeneratorInGroup m delta 1) :=
  (mixedRootCommutation m delta gamma delta_pos gamma_pos delta_long gamma_short
    (by rw [dc_dot]; norm_num) 1 1).symm

/-- The positive middle-node word, with its B₂ correction. -/
def positiveWord (m : ℕ) : SplitGroup m :=
  rootGeneratorInGroup m alpha 1 * rootGeneratorInGroup m beta 1 *
    rootGeneratorInGroup m gamma 1

private theorem swap_one (m : ℕ) (hswap : B2RootSwap m) :
    rootGeneratorInGroup m beta 1 * rootGeneratorInGroup m alpha 1 =
      positiveWord m * rootGeneratorInGroup m delta 1 := by
  simpa only [one_mul, one_pow, positiveWord] using
    hswap alpha beta gamma delta alpha_pos beta_pos alpha_long beta_short
      ab_dot gamma_val delta_val 1 1

private theorem alternative_word (m : ℕ) (hswap : B2RootSwap m) :
    positiveWord m = rootGeneratorInGroup m beta 1 * rootGeneratorInGroup m alpha 1 *
      rootGeneratorInGroup m delta 1 := by
  rw [swap_one m hswap, mul_assoc, root_mul_self, mul_one]

/-- The actual Ree twist fixes the three-factor positive word. -/
theorem positiveWord_fixed (m : ℕ) (hswap : B2RootSwap m) :
    reeTwist m (positiveWord m) = positiveWord m := by
  rw [positiveWord, map_mul, map_mul,
    reeTwist_rootGenerator_long m _ alpha_long,
    reeTwist_rootGenerator_short m _ beta_short,
    reeTwist_rootGenerator_short m _ gamma_short, dual_alpha, dual_gamma]
  have hba : exceptionalRootPermutation beta = alpha := exceptionalRootPermutation_simple 2
  simp only [hba, map_one, one_pow]
  exact (alternative_word m hswap).symm

/-- Its square is the two central root factors of the middle B₂ block. -/
theorem positiveWord_sq (m : ℕ) (hswap : B2RootSwap m) :
    positiveWord m ^ 2 = rootGeneratorInGroup m gamma 1 * rootGeneratorInGroup m delta 1 := by
  let A := rootGeneratorInGroup m alpha 1
  let B := rootGeneratorInGroup m beta 1
  let C := rootGeneratorInGroup m gamma 1
  let D := rootGeneratorInGroup m delta 1
  have hDA : D * A = A * D := (delta_alpha_commute m).eq
  have hDB : D * B = B * D := (delta_beta_commute m).eq
  have hCD : C * D = D * C := (gamma_delta_commute m).eq
  have hAA : A * A = 1 := root_mul_self m alpha
  have hBB : B * B = 1 := root_mul_self m beta
  rw [pow_two]
  nth_rw 1 [alternative_word m hswap]
  change (B * A * D) * (A * B * C) = C * D
  calc
    (B * A * D) * (A * B * C) = B * A * (D * A) * B * C := by simp only [mul_assoc]
    _ = B * (A * A) * (D * B) * C := by rw [hDA]; simp only [mul_assoc]
    _ = (B * B) * D * C := by rw [hAA, mul_one, hDB]; simp only [mul_assoc]
    _ = C * D := by rw [hBB, one_mul, hCD]

theorem positiveWord_mem_unipotent (m : ℕ) : positiveWord m ∈ splitUnipotent m := by
  exact mul_mem (mul_mem (subset_closure ⟨_, _, alpha_pos, rfl⟩)
    (subset_closure ⟨_, _, beta_pos, rfl⟩)) (subset_closure ⟨_, _, gamma_pos, rfl⟩)

end
end ReeF4.Parabolics.SeedGeneration.SuzukiWitness
