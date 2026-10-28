module

public import
  Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.Relations
public import
  Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations
public import
  Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength

/-!
# Split-root calculus for the two long Ree commutators

The 24 slots name the actual positive F₄ roots occurring in the eight relative
root blocks. Their Euclidean coordinates establish the hypotheses of the
already proved equal-length and B₂ matrix exchanges. Nonnegative inner
products give commutation, including short orthogonal roots in characteristic
two. This is the same coordinate calculation as in `ShortCommutators`, kept
local to the independently compiled long-commutator development.

Source: GLS3, Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Theory.AlgebraicGroup StandardRootSystem
open scoped Matrix
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations
open RadicalCoordinates FixedCoordinates
namespace MatrixRelations.LongCommutators
noncomputable section

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]
private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

private def longVector : ℕ → Vec 4
  | 0 => ![0,0,1,-1]
  | 1 => ![0,1,1,0]
  | 2 => ![0,1,0,1]
  | 3 => ![1,0,0,1]
  | 4 => ![1,-1,0,0]
  | 5 => ![1,0,0,-1]
  | 6 => ![0,1,0,-1]
  | _ => ![0,1,-1,0]
private def shortVector : ℕ → Vec 4
  | 0 => ![0,0,0,1]
  | 1 => ![1/2,-1/2,1/2,1/2]
  | 2 => ![1/2,-1/2,1/2,-1/2]
  | 3 => ![1/2,1/2,1/2,-1/2]
  | 4 => ![0,1,0,0]
  | 5 => ![1/2,1/2,-1/2,1/2]
  | 6 => ![1/2,-1/2,-1/2,1/2]
  | _ => ![1/2,-1/2,-1/2,-1/2]
private theorem long_val (i : Fin 8) : (longRoot i).val = longVector i := by
  rw [longRoot_eq_sum]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [longRootCoefficients, longVector, typeF4SimpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]
private theorem short_val (i : Fin 8) : (shortRoot i).val = shortVector i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [shortRoot, longRoot, relativeRotation, middleReflection, endReflection,
      Equiv.Perm.mul_apply, pow_succ,
      WordRelations.exceptionalRootPermutation_simple_reflection,
      exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev,
      reflection_val, reflectedVector, typeF4SimpleRoot, shortVector,
      Matrix.cons_val_two, Matrix.cons_val_three]

-- The lookup names actual split roots, with four factors in each even block.
def R : Fin 24 → F4Chevalley.Root
  | ⟨0, _⟩ => longRoot 0
  | ⟨1, _⟩ => shortRoot 0
  | ⟨2, _⟩ => mixedRoot 0
  | ⟨3, _⟩ => highRoot 0
  | ⟨4, _⟩ => longRoot 1
  | ⟨5, _⟩ => shortRoot 1
  | ⟨6, _⟩ => longRoot 2
  | ⟨7, _⟩ => shortRoot 2
  | ⟨8, _⟩ => mixedRoot 2
  | ⟨9, _⟩ => highRoot 2
  | ⟨10, _⟩ => longRoot 3
  | ⟨11, _⟩ => shortRoot 3
  | ⟨12, _⟩ => longRoot 4
  | ⟨13, _⟩ => shortRoot 4
  | ⟨14, _⟩ => mixedRoot 4
  | ⟨15, _⟩ => highRoot 4
  | ⟨16, _⟩ => longRoot 5
  | ⟨17, _⟩ => shortRoot 5
  | ⟨18, _⟩ => longRoot 6
  | ⟨19, _⟩ => shortRoot 6
  | ⟨20, _⟩ => mixedRoot 6
  | ⟨21, _⟩ => highRoot 6
  | ⟨22, _⟩ => longRoot 7
  | _ => shortRoot 7
def V : ℕ → Vec 4
  | 0 => ![0,0,1,-1]
  | 1 => ![0,0,0,1]
  | 2 => ![0,0,1,0]
  | 3 => ![0,0,1,1]
  | 4 => ![0,1,1,0]
  | 5 => ![1/2,-1/2,1/2,1/2]
  | 6 => ![0,1,0,1]
  | 7 => ![1/2,-1/2,1/2,-1/2]
  | 8 => ![1/2,1/2,1/2,1/2]
  | 9 => ![1,0,1,0]
  | 10 => ![1,0,0,1]
  | 11 => ![1/2,1/2,1/2,-1/2]
  | 12 => ![1,-1,0,0]
  | 13 => ![0,1,0,0]
  | 14 => ![1,0,0,0]
  | 15 => ![1,1,0,0]
  | 16 => ![1,0,0,-1]
  | 17 => ![1/2,1/2,-1/2,1/2]
  | 18 => ![0,1,0,-1]
  | 19 => ![1/2,-1/2,-1/2,1/2]
  | 20 => ![1/2,1/2,-1/2,-1/2]
  | 21 => ![1,0,-1,0]
  | 22 => ![0,1,-1,0]
  | _ => ![1/2,-1/2,-1/2,-1/2]
private theorem rval (i : Fin 24) : (R i).val = V i := by
  fin_cases i
  · change (longRoot 0).val = V 0
    rw [long_val]; rfl
  · change (shortRoot 0).val = V 1
    rw [short_val]; rfl
  · change (mixedRoot 0).val = V 2
    rw [mixedRoot_eq_add _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (highRoot 0).val = V 3
    rw [highRoot_eq_add_two _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (longRoot 1).val = V 4
    rw [long_val]; rfl
  · change (shortRoot 1).val = V 5
    rw [short_val]; rfl
  · change (longRoot 2).val = V 6
    rw [long_val]; rfl
  · change (shortRoot 2).val = V 7
    rw [short_val]; rfl
  · change (mixedRoot 2).val = V 8
    rw [mixedRoot_eq_add _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (highRoot 2).val = V 9
    rw [highRoot_eq_add_two _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (longRoot 3).val = V 10
    rw [long_val]; rfl
  · change (shortRoot 3).val = V 11
    rw [short_val]; rfl
  · change (longRoot 4).val = V 12
    rw [long_val]; rfl
  · change (shortRoot 4).val = V 13
    rw [short_val]; rfl
  · change (mixedRoot 4).val = V 14
    rw [mixedRoot_eq_add _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (highRoot 4).val = V 15
    rw [highRoot_eq_add_two _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (longRoot 5).val = V 16
    rw [long_val]; rfl
  · change (shortRoot 5).val = V 17
    rw [short_val]; rfl
  · change (longRoot 6).val = V 18
    rw [long_val]; rfl
  · change (shortRoot 6).val = V 19
    rw [short_val]; rfl
  · change (mixedRoot 6).val = V 20
    rw [mixedRoot_eq_add _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (highRoot 6).val = V 21
    rw [highRoot_eq_add_two _ (by decide), long_val, short_val]
    ext k; fin_cases k <;> norm_num [longVector, shortVector, V]
  · change (longRoot 7).val = V 22
    rw [long_val]; rfl
  · change (shortRoot 7).val = V 23
    rw [short_val]; rfl

private theorem mixed_pos (i : Fin 8) (hi : i.val % 2 = 0) :
    typeF4RootPairing_base.IsPos (mixedRoot i) :=
  (longRoot_pos i).add (shortRoot_pos i) (mixedRoot_eq_add i hi)
private theorem high_pos (i : Fin 8) (hi : i.val % 2 = 0) :
    typeF4RootPairing_base.IsPos (highRoot i) := by
  apply (mixed_pos i hi).add (shortRoot_pos i)
  change (highRoot i).val = (mixedRoot i).val + (shortRoot i).val
  rw [highRoot_eq_add_two i hi, mixedRoot_eq_add i hi, two_smul, add_assoc]
private theorem rpos (i : Fin 24) : typeF4RootPairing_base.IsPos (R i) := by
  fin_cases i
  · exact longRoot_pos 0
  · exact shortRoot_pos 0
  · exact mixed_pos 0 (by decide)
  · exact high_pos 0 (by decide)
  · exact longRoot_pos 1
  · exact shortRoot_pos 1
  · exact longRoot_pos 2
  · exact shortRoot_pos 2
  · exact mixed_pos 2 (by decide)
  · exact high_pos 2 (by decide)
  · exact longRoot_pos 3
  · exact shortRoot_pos 3
  · exact longRoot_pos 4
  · exact shortRoot_pos 4
  · exact mixed_pos 4 (by decide)
  · exact high_pos 4 (by decide)
  · exact longRoot_pos 5
  · exact shortRoot_pos 5
  · exact longRoot_pos 6
  · exact shortRoot_pos 6
  · exact mixed_pos 6 (by decide)
  · exact high_pos 6 (by decide)
  · exact longRoot_pos 7
  · exact shortRoot_pos 7

private theorem norm_bounds (r : F4Chevalley.Root) :
    1 ≤ dot r.val r.val ∧ dot r.val r.val ≤ 2 := by
  by_cases h : IsLongRoot r
  · rw [isLongRoot_norm r h]; norm_num
  · rw [isShortRoot_norm r h]; norm_num

private theorem dot_add_self (v w : Vec 4) :
    dot (v + w) (v + w) = dot v v + 2 * dot v w + dot w w := by
  change (v + w) ⬝ᵥ (v + w) = v ⬝ᵥ v + 2 * (v ⬝ᵥ w) + w ⬝ᵥ w
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm w v]
  ring

private theorem curve_commute_nonneg (m : ℕ) (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hd : 0 ≤ dot r.val s.val) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b) := by
  have hn := dot_add_self r.val s.val
  by_cases hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨t, ht⟩ := hsum
    have hn' : dot t.val t.val = dot r.val r.val + 2 * dot r.val s.val + dot s.val s.val := by
      change t.val = r.val + s.val at ht
      rwa [← ht] at hn
    have hrs : IsShortRoot r := by
      intro h
      rw [isLongRoot_norm r h] at hn'
      linarith [(norm_bounds s).1, (norm_bounds t).2]
    have htl : IsLongRoot t := by
      by_contra h
      rw [isShortRoot_norm t h] at hn'
      linarith [(norm_bounds r).1, (norm_bounds s).1]
    exact Subtype.ext (rootCurve_commute_of_short_long_sum m r s t hr hs hrs htl ht a b).eq
  · have h0 : typeF4RootPairing.root r + typeF4RootPairing.root s ≠ 0 := by
      intro h
      change r.val + s.val = 0 at h
      rw [h] at hn
      have hz : dot (0 : Vec 4) 0 = 0 := by simp [dot]
      rw [hz] at hn
      linarith [(norm_bounds r).1, (norm_bounds s).1]
    exact Subtype.ext (rootCurve_commute_of_integralOperators r s
      (integralOperators_commute_of_no_sum r s hr hs h0 hsum) a b).eq

def X (m : ℕ) (i : Fin 24) (a : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (R i) a

theorem xc (m : ℕ) (i j : Fin 24) (h : 0 ≤ dot (V i) (V j))
    (a b : CoefficientField m) : Commute (X m i a) (X m j b) :=
  curve_commute_nonneg m (R i) (R j) (rpos i) (rpos j)
    (by simpa only [rval] using h) a b

theorem xa (m : ℕ) (i : Fin 24) (a b : CoefficientField m) :
    X m i a * X m i b = X m i (a + b) :=
  (Subtype.ext (F4Chevalley.rootCurve_add (R i) a b)).symm

theorem xx (m : ℕ) (i : Fin 24) (a : CoefficientField m) :
    X m i a * X m i a = 1 := by
  rw [xa, CharTwo.add_self_eq_zero]
  exact Subtype.ext (F4Chevalley.rootCurve_zero (R i))

theorem xs (m : ℕ) (i j k : Fin 24)
    (hlen : dot (V i) (V i) = dot (V j) (V j))
    (hminus : 2 < dot (V j - V i) (V j - V i))
    (hsum : V k = V i + V j) (a b : CoefficientField m) :
    X m i a * X m j b = X m j b * X m i a * X m k (a * b) := by
  have hl : IsLongRoot (R i) ↔ IsLongRoot (R j) := by
    constructor
    all_goals
      intro h
      by_contra hn
      first
      | have h1 := isLongRoot_norm (R i) h
        have h2 := isShortRoot_norm (R j) hn
        rw [rval] at h1 h2
        linarith
      | have h1 := isLongRoot_norm (R j) h
        have h2 := isShortRoot_norm (R i) hn
        rw [rval] at h1 h2
        linarith
  have hc : typeF4RootPairing.chainBotCoeff (R i) (R j) = 0 := by
    apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
    right
    rintro ⟨t, ht⟩
    change t.val = (R j).val - (R i).val at ht
    rw [rval, rval] at ht
    have hb := (norm_bounds t).2
    rw [ht] at hb
    linarith
  apply Subtype.ext
  change F4Chevalley.rootCurve (R i) a * F4Chevalley.rootCurve (R j) b =
    F4Chevalley.rootCurve (R j) b * F4Chevalley.rootCurve (R i) a *
      F4Chevalley.rootCurve (R k) (a * b)
  apply Units.ext
  simpa only [Units.val_mul, hc, Nat.cast_zero, zero_add, one_mul] using
    rootCurve_exchange_of_equal_length_sum m (R i) (R j) (R k) (rpos i) (rpos j) hl
      (by simpa only [typeF4RootPairing_root, rval] using hsum) a b

theorem xb (m : ℕ) (i j k l : Fin 24)
    (hi : dot (V i) (V i) = 2) (hj : dot (V j) (V j) = 1)
    (hd : dot (V i) (V j) = -1)
    (hk : V k = V i + V j) (hl : V l = V i + (2 : ℝ) • V j)
    (a b : CoefficientField m) :
    X m j b * X m i a = X m i a * X m j b * X m k (a*b) * X m l (a*b^2) := by
  apply FixedCoordinates.b2RootSwap m (R i) (R j) (R k) (R l) (rpos i) (rpos j)
  · by_contra h
    have hh := isShortRoot_norm (R i) h
    rw [rval, hi] at hh
    norm_num at hh
  · intro h
    have hh := isLongRoot_norm (R j) h
    rw [rval, hj] at hh
    norm_num at hh
  · simpa only [rval] using hd
  · simpa only [rval] using hk
  · simpa only [rval] using hl

theorem xi (m : ℕ) (i : Fin 24) (a : CoefficientField m) :
    (X m i a)⁻¹ = X m i a := inv_eq_of_mul_eq_one_right (xx m i a)

theorem xz (m : ℕ) (i : Fin 24) : X m i 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero (R i))

end
end MatrixRelations.LongCommutators
end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
