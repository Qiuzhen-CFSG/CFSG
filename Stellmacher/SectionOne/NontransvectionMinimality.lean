module
public import Stellmacher.SectionOne.LemmaOneFive

/-!
# The minimum bound when order-two actors are not transvections

Under the standing faithful solvable Section One hypotheses, let T be an
elementary abelian two-subgroup. If no order-two subgroup of T has fixed-point
index two on V, then every nontrivial subgroup Y of T has m(Y) at least two.
The assumption refers to the exact inherited action and fixed-point subgroup.

Choose a Sylow containing T. The relative order-two minimizer from (1.5)
supplies A inside Y with m(A) at most m(Y). Faithfulness, through the proved
order-two lower bound, makes the fixed-point index of A greater than one.
That index is a power of two because V is elementary abelian. Excluding index
two therefore makes it at least four; division by the actor order two gives
m(A) at least two, and minimality transfers the bound to Y.

Source: Stellmacher, Journal of Algebra 190 (1997), (1.5), and its application
in the proof of (9.1), p.47, relation (6). This numerical reduction supplies
the lower bound required by the bounded version of (1.6).
-/

namespace Stellmacher.SectionOne
universe u

public theorem m_ge_two_of_no_transvection
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (T : Subgroup G) (hT : IsElementaryAbelian 2 T)
    (hno : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 →
      (FixedPoints.subgroup A V).index ≠ 2)
    (Y : Subgroup G) (hYT : Y ≤ T) (hYne : Y ≠ ⊥) :
    2 ≤ m (G := G) (V := V) Y := by
  let _ := hT
  have hY : IsElementaryAbelian 2 Y := {
    toIsMulCommutative := .of_setLike_mul_comm fun _ hx _ hy =>
      setLike_mul_comm (hYT hx) (hYT hy)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun y =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := T) y (hYT y.property)) }
  obtain ⟨S,hTS⟩ := (IsElementaryAbelian.isPGroup 2 T).exists_le_sylow
  obtain ⟨A,hA,hcard⟩ := lemma_one_five_exists_oneAmax_card_two_relative
    h S Y (hYT.trans hTS) hY hYne
  apply le_trans ?_ hA.2.1
  have hindexne := hno A (hA.1.trans hYT) hcard
  have hone := lemma_one_five_m_ge_one_of_card_two h A hcard
  have hcount := (FixedPoints.subgroup A V).index_mul_card
  have hpos : 0 < Nat.card (FixedPoints.subgroup A V) := Nat.card_pos
  have hfixpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup A V) := by exact_mod_cast hpos
  have hnat : 2 * Nat.card (FixedPoints.subgroup A V) ≤ Nat.card V := by
    unfold m at hone
    rw [hcard] at hone
    have hh := (le_div_iff₀ (by positivity :
      (0 : ℚ) < (Nat.card (FixedPoints.subgroup A V) : ℚ) * 2)).mp hone
    have hhNat : Nat.card (FixedPoints.subgroup A V) * 2 ≤ Nat.card V := by
      exact_mod_cast (by simpa using hh :
        (Nat.card (FixedPoints.subgroup A V) : ℚ) * 2 ≤ Nat.card V)
    simpa only [Nat.mul_comm] using hhNat
  have hidxgt : 1 < (FixedPoints.subgroup A V).index := by nlinarith
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).index (FixedPoints.subgroup A V)
  have hn2 : 2 ≤ n := by
    by_contra hh
    interval_cases n <;> simp_all
  have hfour : 4 ≤ (FixedPoints.subgroup A V).index := by
    rw [hn]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hn2
  have hlarge : 4 * Nat.card (FixedPoints.subgroup A V) ≤ Nat.card V := by nlinarith
  unfold m
  rw [hcard]
  apply (le_div_iff₀ (by positivity :
    (0 : ℚ) < (Nat.card (FixedPoints.subgroup A V) : ℚ) * 2)).mpr
  have hh : (4 : ℚ) * Nat.card (FixedPoints.subgroup A V) ≤ Nat.card V := by
    exact_mod_cast hlarge
  nlinarith
end Stellmacher.SectionOne
