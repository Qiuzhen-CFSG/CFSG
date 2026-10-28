module
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions
public import Theory.ElementaryAbelian.Basic

/-!
# Residual centralizers for the two odd involutions of S₈

Odd-order elements of C_A₈(q) belong to its two-residual. Explicit cubic
elements give a transitive action on six letters and bound the full S₈
centralizer. For q=(01), it consists of 1 and q. For q=(01)(23)(45),
it consists of 1, q, (67), and q(67), and is elementary abelian of order four.
The lower bound uses that every permutation commuting with q preserves
its two fixed points and therefore commutes with their transposition.

Only finite calculations on points and the displayed permutations are
used; neither a subgroup enumeration nor a residual-isomorphism tag
replaces the actual embedded two-residual.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(8),(9), printed p.1171, and 16.4.9(1), printed p.1189.
-/

@[expose] public section
open Subgroup Equiv
open Theory.SpecificGroups.SymmetricEight.Involutions
open CFSG.Quasithin.Chapter16.LiePreliminaries
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.BinaryLinear.EightModel

noncomputable def residual (q : S) : Subgroup S :=
  (fixedTwoResidual A (permutationAutEquiv q)).map A.subtype
def fullCentralizer (q : S) : Subgroup S := centralizer (residual q : Set S)

private theorem cubic_mem {q x : S} (hx : x ∈ A) (hc : q * x = x * q)
    (h3 : x ^ 3 = 1) : x ∈ residual q := by
  let a : A := ⟨x, hx⟩
  have hf : a ∈ (permutationAutEquiv q).fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    change q * x * q⁻¹ = x
    rw [hc, mul_inv_cancel_right]
  refine ⟨a, ⟨⟨a, hf⟩, ?_, rfl⟩, rfl⟩
  apply mem_pResidual_of_orderOf_coprime
  have hp : (⟨a, hf⟩ : (permutationAutEquiv q).fixedSubgroup) ^ 3 = 1 := by
    apply Subtype.ext; apply Subtype.ext; exact h3
  exact (by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp)

private def first : S := swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5)
private def second : S := swap 0 2 * swap 2 5 * (swap 1 3 * swap 3 4)

private theorem first_mem : first ∈ residual threePairs :=
  cubic_mem (by rw [Perm.mem_alternatingGroup]; decide +kernel)
    (by decide +kernel) (by decide +kernel)
private theorem second_mem : second ∈ residual threePairs :=
  cubic_mem (by rw [Perm.mem_alternatingGroup]; decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def stabilizerWord : S := second * first * second * first * second * second
private theorem stabilizerWord_mem : stabilizerWord ∈ residual threePairs := by
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem second_mem first_mem) second_mem)
    first_mem) second_mem) second_mem

private def orbitWord (i : Fin 6) : S :=
  ![1, first * second * second, first, first * first * second * second,
    first * second, second * second] i
private theorem orbitWord_mem (i : Fin 6) : orbitWord i ∈ residual threePairs := by
  fin_cases i
  · exact one_mem _
  · exact mul_mem (mul_mem first_mem second_mem) second_mem
  · exact first_mem
  · exact mul_mem (mul_mem (mul_mem first_mem first_mem) second_mem) second_mem
  · exact mul_mem first_mem second_mem
  · exact mul_mem second_mem second_mem
private theorem orbitWord_zero : ∀ i : Fin 6, orbitWord i 0 = i.castLE (by decide) := by decide +kernel

private def fourWord (i : Fin 4) : S := ![1, threePairs, swap 6 7, threePairs * swap 6 7] i

private theorem residual_commutes (q : S) {x : S} (hx : x ∈ residual q) : q * x = x * q := by
  obtain ⟨a, ⟨b, _, rfl⟩, rfl⟩ := hx
  have h := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp b.property)
  change q * b.val.val * q⁻¹ = b.val.val at h
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem swap67_commutes {x : S} (hx : threePairs * x = x * threePairs) :
    swap 6 7 * x = x * swap 6 7 := by
  have hf (i : Fin 8) (hi : i = 6 ∨ i = 7) : x i = 6 ∨ x i = 7 := by
    have hh := congrArg (fun g : S => g i) hx
    change threePairs (x i) = x (threePairs i) at hh
    have hfix : threePairs i = i := by rcases hi with rfl | rfl <;> decide
    rw [hfix] at hh
    exact (by decide : ∀ j : Fin 8, threePairs j = j → j = 6 ∨ j = 7) _ hh
  have h6 := hf 6 (Or.inl rfl)
  have h7 := hf 7 (Or.inr rfl)
  have hne : x 6 ≠ x 7 := x.injective.ne (by decide)
  have hconj : swap (x 6) (x 7) = swap (6 : Fin 8) 7 := by
    rcases h6 with h6 | h6 <;> rcases h7 with h7 | h7 <;> simp_all [swap_comm]
  have hm := Equiv.symm_trans_swap_trans (6 : Fin 8) 7 x
  change x * (swap 6 7 * x⁻¹) = _ at hm
  rw [← mul_assoc] at hm
  exact (mul_inv_eq_iff_eq_mul.mp (hm.trans hconj)).symm

private theorem fourWord_mem (i : Fin 4) : fourWord i ∈ fullCentralizer threePairs := by
  have hr : threePairs ∈ fullCentralizer threePairs := by
    intro x hx; exact (residual_commutes _ hx).symm
  have hs : swap (6 : Fin 8) 7 ∈ fullCentralizer threePairs := by
    intro x hx; exact (swap67_commutes (residual_commutes _ hx)).symm
  fin_cases i
  · exact one_mem _
  · exact hr
  · exact hs
  · exact mul_mem hr hs

private theorem centralizer_cover {g : S} (hg : g ∈ fullCentralizer threePairs) :
    ∃ k : Fin 4, fourWord k = g := by
  have hc (w : S) (hw : w ∈ residual threePairs) (i : Fin 8) :
      w (g i) = g (w i) := congrArg (fun v : S => v i) (hg w hw)
  have h0 : g 0 = 0 ∨ g 0 = 1 := by
    have hs := hc stabilizerWord stabilizerWord_mem 0
    rw [show stabilizerWord 0 = 0 from by decide +kernel] at hs
    have hn : first (g 0) ≠ g 0 := by
      rw [hc first first_mem 0]
      exact g.injective.ne (by decide +kernel)
    exact (by decide +kernel : ∀ i : Fin 8,
      stabilizerWord i = i → first i ≠ i → i = 0 ∨ i = 1) _ hs hn
  have hfix (i : Fin 8) (hi : i = 6 ∨ i = 7) : g i = 6 ∨ g i = 7 := by
    have ha := hc first first_mem i
    have hb := hc second second_mem i
    have hia : first i = i := by rcases hi with rfl | rfl <;> decide +kernel
    have hib : second i = i := by rcases hi with rfl | rfl <;> decide +kernel
    rw [hia] at ha; rw [hib] at hb
    exact (by decide +kernel : ∀ j : Fin 8,
      first j = j → second j = j → j = 6 ∨ j = 7) _ ha hb
  obtain ⟨k, hk0, hk6⟩ := (by decide +kernel : ∀ i j : Fin 8,
    (i = 0 ∨ i = 1) → (j = 6 ∨ j = 7) →
      ∃ k : Fin 4, fourWord k 0 = i ∧ fourWord k 6 = j) _ _ h0 (hfix 6 (Or.inl rfl))
  refine ⟨k, Equiv.ext (fun i => ?_)⟩
  by_cases hi : i.val < 6
  · let j : Fin 6 := ⟨i.val, hi⟩
    have hj : orbitWord j 0 = i := orbitWord_zero j
    have hw := congrArg (fun v : S => v 0) ((fourWord_mem k) (orbitWord j) (orbitWord_mem j))
    change orbitWord j (fourWord k 0) = fourWord k (orbitWord j 0) at hw
    rw [← hj, ← hw, hk0]
    exact hc _ (orbitWord_mem j) 0
  · have hi' : i = 6 ∨ i = 7 := by omega
    rcases hi' with rfl | rfl
    · exact hk6
    · have hne : g 6 ≠ g 7 := g.injective.ne (by decide)
      exact (by decide +kernel : ∀ k : Fin 4, ∀ i j : Fin 8,
        fourWord k 6 = i → i ≠ j → (j = 6 ∨ j = 7) → fourWord k 7 = j)
        k _ _ hk6 hne (hfix 7 (Or.inr rfl))

private noncomputable def fourEquiv : Fin 4 ≃ fullCentralizer threePairs :=
  Equiv.ofBijective (fun i => ⟨fourWord i, fourWord_mem i⟩) ⟨by
    intro i j hij
    have h0 := congrArg (fun x : fullCentralizer threePairs => x.val 0) hij
    have h6 := congrArg (fun x : fullCentralizer threePairs => x.val 6) hij
    exact (by decide +kernel : ∀ i j : Fin 4,
      fourWord i 0 = fourWord j 0 → fourWord i 6 = fourWord j 6 → i = j) i j h0 h6,
    by
      intro g
      obtain ⟨i, hi⟩ := centralizer_cover g.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem threePairs_card : Nat.card (fullCentralizer threePairs) = 4 := by
  rw [← Nat.card_congr fourEquiv]; simp

theorem threePairs_elementary : IsElementaryAbelian 2 (fullCentralizer threePairs) := by
  refine {
    toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => ?_) }
  · obtain ⟨i, hi⟩ := centralizer_cover x.property
    obtain ⟨j, hj⟩ := centralizer_cover y.property
    apply Subtype.ext
    change x.val * y.val = y.val * x.val
    rw [← hi, ← hj]
    exact (by decide +kernel : ∀ i j : Fin 4, fourWord i * fourWord j = fourWord j * fourWord i) i j
  · obtain ⟨i, hi⟩ := centralizer_cover x.property
    apply Subtype.ext
    change x.val ^ 2 = 1
    rw [← hi]
    exact (by decide +kernel : ∀ i : Fin 4, fourWord i ^ 2 = 1) i

private def oneGenerator (i : Fin 4) : S := swap 2 3 * swap 3 (⟨i.val + 4, by omega⟩ : Fin 8)

private theorem oneGenerator_mem (i : Fin 4) : oneGenerator i ∈ residual onePair := by
  apply cubic_mem
  · rw [Perm.mem_alternatingGroup]
    exact (by decide +kernel : ∀ i : Fin 4, Perm.sign (oneGenerator i) = 1) i
  · exact (by decide +kernel : ∀ i : Fin 4,
      onePair * oneGenerator i = oneGenerator i * onePair) i
  · exact (by decide +kernel : ∀ i : Fin 4, oneGenerator i ^ 3 = 1) i

private def oneOrbit (i : Fin 6) : S :=
  ![oneGenerator 0, oneGenerator 0 * oneGenerator 0, 1,
    oneGenerator 1 * oneGenerator 0 * oneGenerator 0,
    oneGenerator 2 * oneGenerator 0 * oneGenerator 0,
    oneGenerator 3 * oneGenerator 0 * oneGenerator 0] i

private theorem oneOrbit_mem (i : Fin 6) : oneOrbit i ∈ residual onePair := by
  fin_cases i
  · exact oneGenerator_mem 0
  · exact mul_mem (oneGenerator_mem 0) (oneGenerator_mem 0)
  · exact one_mem _
  · exact mul_mem (mul_mem (oneGenerator_mem 1) (oneGenerator_mem 0)) (oneGenerator_mem 0)
  · exact mul_mem (mul_mem (oneGenerator_mem 2) (oneGenerator_mem 0)) (oneGenerator_mem 0)
  · exact mul_mem (mul_mem (oneGenerator_mem 3) (oneGenerator_mem 0)) (oneGenerator_mem 0)

private theorem oneOrbit_four : ∀ i : Fin 6, oneOrbit i 4 = (⟨i.val + 2, by omega⟩ : Fin 8) := by
  decide +kernel

private def twoWord (i : Fin 2) : S := ![1, onePair] i

private theorem twoWord_mem (i : Fin 2) : twoWord i ∈ fullCentralizer onePair := by
  fin_cases i
  · exact one_mem _
  · intro x hx; exact (residual_commutes _ hx).symm

private theorem transposition_cover {g : S} (hg : g ∈ fullCentralizer onePair) :
    ∃ k : Fin 2, twoWord k = g := by
  have hc (w : S) (hw : w ∈ residual onePair) (i : Fin 8) :
      w (g i) = g (w i) := congrArg (fun v : S => v i) (hg w hw)
  have h4 : g 4 = 4 := by
    have hm : oneGenerator 0 (g 4) ≠ g 4 := by
      rw [hc _ (oneGenerator_mem 0) 4]
      exact g.injective.ne (by decide +kernel)
    have hfixed (j : Fin 3) : oneGenerator (j.succ) (g 4) = g 4 := by
      rw [hc _ (oneGenerator_mem _) 4]
      congr 1
    exact (by decide +kernel : ∀ i : Fin 8, oneGenerator 0 i ≠ i →
      (∀ j : Fin 3, oneGenerator j.succ i = i) → i = 4) _ hm hfixed
  have hfix (i : Fin 8) (hi : 2 ≤ i.val) : g i = i := by
    let j : Fin 6 := ⟨i.val - 2, by omega⟩
    have hj : oneOrbit j 4 = i := (oneOrbit_four j).trans (Fin.ext (by dsimp [j]; omega))
    rw [← hj, ← hc _ (oneOrbit_mem j) 4, h4]
  have h01 (i : Fin 8) (hi : i.val < 2) : g i = 0 ∨ g i = 1 := by
    have hmove : (g i).val < 2 := by
      by_contra hh
      have he := g.injective (hfix (g i) (by omega))
      have hv := congrArg Fin.val he
      omega
    omega
  obtain ⟨k, hk⟩ := (by decide +kernel : ∀ j : Fin 8,
    (j = 0 ∨ j = 1) → ∃ k : Fin 2, twoWord k 0 = j) _ (h01 0 (by decide))
  refine ⟨k, Equiv.ext (fun i => ?_)⟩
  by_cases hi : 2 ≤ i.val
  · rw [hfix i hi]
    exact (by decide +kernel : ∀ k : Fin 2, ∀ i : Fin 8, 2 ≤ i.val → twoWord k i = i) k i hi
  · have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact hk
    · exact (by decide +kernel : ∀ k : Fin 2, ∀ j l : Fin 8,
        twoWord k 0 = j → j ≠ l → (l = 0 ∨ l = 1) → twoWord k 1 = l)
        k _ _ hk (g.injective.ne (by decide)) (h01 1 (by decide))

private noncomputable def twoEquiv : Fin 2 ≃ fullCentralizer onePair :=
  Equiv.ofBijective (fun i => ⟨twoWord i, twoWord_mem i⟩) ⟨by
    intro i j hij
    have h0 := congrArg (fun x : fullCentralizer onePair => x.val 0) hij
    exact (by decide +kernel : ∀ i j : Fin 2,
      twoWord i 0 = twoWord j 0 → i = j) i j h0,
    by
      intro g
      obtain ⟨i, hi⟩ := transposition_cover g.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem onePair_card : Nat.card (fullCentralizer onePair) = 2 := by
  rw [← Nat.card_congr twoEquiv]; simp

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.BinaryLinear.EightModel

