module
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.RootGeometry

/-!
# Short root strings in the F4 comparison

The Euclidean root lengths and integral Cartan pairings force any two-step
string with a long direction or short initial root to join opposite roots.
For a short direction whose one-step sum is long, the lower string coefficient
is one. Thus the corresponding Geck operator coefficient is two and vanishes
in characteristic two. These are the root-string inputs to the exceptional
quotient-to-ideal comparison, in the conventions of `RootDuality` and Geck's
integral construction.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators Matrix
namespace ReeF4.WordRelations

private lemma norm_le_two (r : typeF4Roots) : dot r.val r.val ≤ 2 := by
  by_cases hr : IsLongRoot r
  · rw [isLongRoot_norm r hr]
  · rw [isShortRoot_norm r hr]; norm_num

private lemma dot_add_two (i j : Vec 4) :
    dot (j + (2 : ℝ) • i) (j + (2 : ℝ) • i) =
      dot j j + 4 * dot i i + 4 * dot j i := by
  change (j + (2 : ℝ) • i) ⬝ᵥ (j + (2 : ℝ) • i) = _
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm i j]
  dsimp only [dot, dotProduct]
  ring

private lemma endpoints_opposite {i j k : typeF4Roots}
    (h : k.val = j.val + (2 : ℝ) • i.val)
    (hn : dot k.val k.val + dot j.val j.val ≤ 2 * dot i.val i.val) :
    j.val = -i.val ∧ k.val = i.val := by
  have hpar : dot (k.val - j.val) (k.val - j.val) +
      dot (k.val + j.val) (k.val + j.val) =
      2 * (dot k.val k.val + dot j.val j.val) := by
    change (k.val - j.val) ⬝ᵥ (k.val - j.val) +
      (k.val + j.val) ⬝ᵥ (k.val + j.val) = _
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add]
    dsimp only [dot, dotProduct]
    ring
  have hd : dot (k.val - j.val) (k.val - j.val) = 4 * dot i.val i.val := by
    have he : k.val - j.val = (2 : ℝ) • i.val := by rw [h]; abel
    rw [he]
    change ((2 : ℝ) • i.val) ⬝ᵥ ((2 : ℝ) • i.val) = _
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    dsimp only [dot, dotProduct]
    ring
  have hnonneg : 0 ≤ dot (k.val + j.val) (k.val + j.val) :=
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hz : dot (k.val + j.val) (k.val + j.val) = 0 := by linarith
  have he : k.val + j.val = 0 := dotProduct_self_eq_zero.mp hz
  have hj : j.val = -i.val := by
    ext q
    have hq := congrFun he q
    have hq' := congrFun h q
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at *
    linarith
  exact ⟨hj, by rw [h, hj]; module⟩

lemma root_add_two_of_long {i j k : typeF4Roots} (hi : IsLongRoot i)
    (h : k.val = j.val + (2 : ℝ) • i.val) :
    j.val = -i.val ∧ k.val = i.val := by
  apply endpoints_opposite h
  rw [isLongRoot_norm i hi]
  linarith [norm_le_two j, norm_le_two k]

lemma root_add_two_of_short_column {i j k : typeF4Roots} (hj : IsShortRoot j)
    (h : k.val = j.val + (2 : ℝ) • i.val) :
    j.val = -i.val ∧ k.val = i.val := by
  by_cases hi : IsLongRoot i
  · exact root_add_two_of_long hi h
  have hk : IsShortRoot k := by
    intro hk
    obtain ⟨z, hz⟩ := typeF4RootPairing_pairing_eq_intCast j i
    rw [typeF4RootPairing_pairing, typeF4CorootScale_of_not_pair i hi] at hz
    have he := dot_add_two i.val j.val
    rw [← h, isLongRoot_norm k hk, isShortRoot_norm j hj,
      isShortRoot_norm i hi] at he
    have hz' : (2 : ℝ) * z = -3 := by linarith
    have hz'' : (2 : ℤ) * z = -3 := by exact_mod_cast hz'
    omega
  apply endpoints_opposite h
  rw [isShortRoot_norm i hi, isShortRoot_norm j hj, isShortRoot_norm k hk]
  norm_num

lemma chainBotCoeff_short_add_long {i j k : typeF4Roots}
    (hi : IsShortRoot i) (hk : IsLongRoot k)
    (h : typeF4RootPairing.root k =
      typeF4RootPairing.root i + typeF4RootPairing.root j) :
    typeF4RootPairing.chainBotCoeff i j = 1 := by
  have hn : dot k.val k.val = dot i.val i.val + dot j.val j.val +
      2 * dot i.val j.val := by
    rw [show k.val = i.val + j.val from h]
    change (i.val + j.val) ⬝ᵥ (i.val + j.val) = _
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm j.val i.val]
    dsimp only [dot, dotProduct]
    ring
  rw [isLongRoot_norm k hk, isShortRoot_norm i hi] at hn
  have hj : IsShortRoot j := by
    intro hj
    obtain ⟨z, hz⟩ := typeF4RootPairing_pairing_eq_intCast i j
    rw [typeF4RootPairing_pairing, typeF4CorootScale_of_pair j hj, one_mul] at hz
    rw [isLongRoot_norm j hj] at hn
    have hz' : (2 : ℝ) * z = -1 := by linarith
    have hz'' : (2 : ℤ) * z = -1 := by exact_mod_cast hz'
    omega
  rw [isShortRoot_norm j hj] at hn
  have hdot : dot j.val i.val = 0 := by
    rw [show dot j.val i.val = dot i.val j.val from dotProduct_comm _ _]
    linarith
  have hpair : typeF4RootPairing.pairingIn ℤ j i = 0 := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    rw [Int.cast_zero]
    change algebraMap ℤ ℝ _ = 0
    rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing, hdot, mul_zero]
  have hmem : typeF4RootPairing.root i + typeF4RootPairing.root j ∈
      Set.range typeF4RootPairing.root := ⟨k, h⟩
  have hlin := typeF4RootPairing.linearIndependent_of_add_mem_range_root' hmem
  have htop := typeF4RootPairing.one_le_chainTopCoeff_of_root_add_mem hmem
  have hdiff := typeF4RootPairing.chainBotCoeff_sub_chainTopCoeff hlin
  rw [hpair] at hdiff
  have hle : typeF4RootPairing.chainBotCoeff i j ≤ 1 := by
    by_contra hn
    have htwo : 2 ≤ typeF4RootPairing.chainBotCoeff i j := by omega
    obtain ⟨l, hl⟩ := (typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff
      hlin).mpr htwo
    apply root_ne_add_three_nsmul i l k
    rw [h, hl]
    module
  omega

end ReeF4.WordRelations
