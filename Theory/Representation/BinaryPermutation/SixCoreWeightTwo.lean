module
public import Theory.Representation.BinaryPermutation.SixCoreWeightFour
/-!
# Weight-two displacements in the six-letter augmentation core

An involution moving the core only in weight two is either trivial or a
transposition. Sign is therefore faithful on any elementary actor with this
property. All its displacements lie in the single line supported on that
transposition. The small certificates test coordinate pairs and individual
core words; they do not enumerate subgroups.

Source: Aschbacher–Smith 13.4.17, rank-one commutator step, printed p.914,
refs/quasithin.pdf. The ambient application is in FixedCoreSource/Nonsolvable/
WeightTwoReturning.lean.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.SixCoreWeightTwo
abbrev S := Equiv.Perm (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := coreRepresentation (Fin 6)
private def pair (i j : Fin 6) : W :=
  ⟨Pi.single i 1 + Pi.single j 1, by simp [mem_core, Finset.sum_add_distrib, Pi.single_apply, CharTwo.add_self_eq_zero]⟩
private theorem involution_test : ∀ a : S, a ^ 2 = 1 →
    (∀ i j : Fin 6, wordWeight (rho a (pair i j) - pair i j).val ≠ 4) →
      a = 1 ∨ a.support.card = 2 := by
  decide +kernel

theorem eq_one_or_isSwap (a : S) (ha : a ^ 2 = 1)
    (hw : ∀ v : W, rho a v ≠ v → wordWeight (rho a v - v).val = 2) :
    a = 1 ∨ a.IsSwap := by
  apply Or.imp_right Equiv.Perm.card_support_eq_two.mp (involution_test a ha ?_)
  intro i j ht
  by_cases he : rho a (pair i j) = pair i j
  · rw [he,sub_self] at ht
    have hz : wordWeight (0 : W).val = 0 := by decide
    omega
  · have hh := hw (pair i j) he
    omega

theorem actor_eq_zpowers (A : Subgroup S) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥)
    (hw : ∀ a ∈ A, ∀ v : W, rho a v ≠ v → wordWeight (rho a v - v).val = 2) :
    ∃ t ∈ A, t.IsSwap ∧ A = zpowers t := by
  have hcases (a : A) : a.val = 1 ∨ a.val.IsSwap :=
    eq_one_or_isSwap a.val (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
      (hw a.val a.property)
  let f := Equiv.Perm.sign.comp A.subtype
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    rcases hcases a with he | hs
    · exact he
    · have hh := hs.sign_eq
      change Equiv.Perm.sign a.val = 1 at ha
      rw [ha] at hh
      contradiction)
  have hc : Nat.card A ≤ 2 := (Nat.card_le_card_of_injective f hf).trans
    (by rw [Nat.card_eq_fintype_card]; decide)
  obtain ⟨t,ht1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ht := t.property
  have ht1 : t.val ≠ 1 := fun he => ht1 (Subtype.ext he)
  have hs := (hcases ⟨t,ht⟩).resolve_left ht1
  refine ⟨t,ht,hs,?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
  rwa [Nat.card_zpowers,hs.orderOf]

private local instance : DecidablePred (fun v : Full (Fin 6) => v ∈ core (Fin 6)) :=
  fun v => inferInstanceAs (Decidable ((augmentation (Fin 6)) v = 0))
private local instance : Fintype W :=
  Fintype.ofFinset (Finset.univ.filter fun v => v ∈ core (Fin 6)) (by simp)

private theorem swap_displacement : ∀ i j : Fin 6, ∀ v : W,
    rho (Equiv.swap i j) v - v = 0 ∨ rho (Equiv.swap i j) v - v = pair i j := by
  decide +kernel

private theorem pair_weight : ∀ i j : Fin 6, i ≠ j → wordWeight (pair i j).val = 2 := by
  decide +kernel
/-- A nontrivial elementary actor with weight-two displacements moves the
entire core along one weight-two vector. -/
theorem common_displacement (A : Subgroup S) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥)
    (hw : ∀ a ∈ A, ∀ v : W, rho a v ≠ v → wordWeight (rho a v - v).val = 2) :
    ∃ w : W, wordWeight w.val = 2 ∧
      ∀ a ∈ A, ∀ v : W, rho a v - v = 0 ∨ rho a v - v = w := by
  obtain ⟨t,ht,hs,hA⟩ := actor_eq_zpowers A hne hw
  obtain ⟨i,j,hij,he⟩ := hs
  refine ⟨pair i j,pair_weight i j hij,?_⟩
  intro a ha v
  rw [hA,mem_zpowers_iff_mem_range_orderOf,Equiv.Perm.IsSwap.orderOf ⟨i,j,hij,he⟩] at ha
  have ha' : a = 1 ∨ a = t := by
    obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp ha
    have hn' := Finset.mem_range.mp hn
    interval_cases n <;> simp_all
  rcases ha' with rfl | rfl
  · left
    simp [rho]
  · rw [he]
    exact swap_displacement i j v
end BinaryPermutation.SixCoreWeightTwo
