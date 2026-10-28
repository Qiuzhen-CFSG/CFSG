module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional.Transport
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.OddExponent
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Genuine triality in the initial binary sieve

Inner–coefficient coverage and the mixed Sylow-fixer calculation imply
innerness of the marked four-group's action. Odd exponents use the proved
odd-order coefficient argument, including exponent one. At exponent one,
inner square-one fixers embed in the center of the actual unipotent Sylow,
whose order is two. This excludes a faithful four-group and forces m > 1.

Only Standard.BinaryCarrier is used. The coverage and even-exponent mixed
calculation remain intrinsic theorem premises, with existing owners
qt-triality-binary-automorphism-coverage and qt-16-triality-mixed-sylow-fixers.
All Sylow geometry, center orders, and inherited simplicity/perfectness are
discharged here; no involution-classification premise is needed.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, and 16.1.6,
printed p.1172; GLS3 §2.5 for the inner–coefficient convention.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module Triality.Standard Triality.Standard.Parabolics Triality.Standard.OuterOdd

private theorem involutive_fixers_of_standard {Q : Type*} [Group Q] [Finite Q]
    (P : Sylow 2 Q)
    (hP : ∀ α : MulAut Q, α ^ 2 = 1 → (∀ x ∈ P, α x = x) →
      ∃ x : Q, α = MulAut.conj x)
    (S : Sylow 2 Q) (α : MulAut Q) (hsq : α ^ 2 = 1)
    (hfix : ∀ x ∈ S, α x = x) : α ∈ MulAut.innerSubgroup Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P S
  let f : Q ≃* Q := MulAut.conj g
  let β := MulAut.congr f.symm α
  have hb : β ^ 2 = 1 := by
    rw [← map_pow, hsq, map_one]
  have hbfix : ∀ x ∈ P, β x = x := by
    intro x hx
    change f.symm (α (f x)) = x
    have hm : (P : Subgroup Q).map f.toMonoidHom = (S : Subgroup Q) :=
      congrArg Sylow.toSubgroup hg
    have hfx : f x ∈ S := by
      change f x ∈ (S : Subgroup Q)
      rw [← hm]
      exact mem_map_of_mem f.toMonoidHom hx
    rw [hfix (f x) hfx, f.symm_apply_apply]
  obtain ⟨x, hx⟩ := hP β hb hbfix
  refine ⟨f x, ?_⟩
  apply (MulAut.congr f.symm).injective
  rw [MulAut.congr_conj, f.symm_apply_apply]
  exact hx.symm

private theorem fixed_four_card_le_center {Q : Type*} [Group Q] [Finite Q]
    (hc : center Q = ⊥) (P : Sylow 2 Q) (A : Subgroup (MulAut Q))
    (hA : IsKleinFour A) (hfix : ∀ α ∈ A, ∀ x ∈ P, α x = x)
    (hinner : ∀ α : MulAut Q, α ^ 2 = 1 → (∀ x ∈ P, α x = x) →
      ∃ x : Q, α = MulAut.conj x) : 4 ≤ Nat.card (center P) := by
  classical
  let : IsKleinFour A := hA
  have hex (α : A) : ∃ z : center P, α.val = MulAut.conj z.val.val := by
    have hsq : α.val ^ 2 = 1 := congrArg Subtype.val
      (show α ^ 2 = 1 by rw [pow_two, IsKleinFour.mul_self])
    obtain ⟨x, hx⟩ := hinner α hsq (hfix α α.property)
    have hx2 : x ^ 2 = 1 := by
      apply MulAut.conj_injective_of_center_eq_bot hc
      rw [map_pow, ← hx, hsq, map_one]
    obtain ⟨hxP, hcomm⟩ := MulAut.involution_mem_sylow_of_centralizes P x hx2
      (hx ▸ hfix α α.property)
    refine ⟨⟨⟨x, hxP⟩, mem_center_iff.mpr ?_⟩, hx⟩
    intro y
    exact Subtype.ext (hcomm y y.property).eq.symm
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro α β he
    apply Subtype.ext
    rw [hf α, hf β, he]
  simpa only [hA.card_four] using Nat.card_le_card_of_injective f hinj

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The exponent-one exclusion needs coverage, but no even-exponent mixed
calculation or involution-classification theorem. -/
theorem triality_exponent_gt_one_of_coverage
    (coverage : ∀ (n : ℕ) (hn : 0 < n),
      IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
      ∀ α : MulAut (BinaryCarrier n hn), ∃ g : BinaryCarrier n hn,
        ∃ e : CoefficientAut (binaryParameters n hn),
          α = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 ≤ m)
    (hi : IsTrialityGroupAt (2 ^ m) (NormalizerAction.componentImage K)) : 1 < m := by
  by_contra h
  have hm1 : m = 1 := by omega
  have hm0 : 0 < m := by omega
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ m hm0).mp hi
  obtain ⟨hs, hp⟩ := exceptional_model_hypotheses K hK e
  let : IsSimpleGroup (BinaryCarrier m hm0) := hs
  let : Group.IsPerfect (BinaryCarrier m hm0) := hp
  let P := unipotentSylow (binaryParameters m hm0) rfl
  obtain ⟨A, hA, hfix⟩ := exists_model_fixed_four_on_sylow K hK a e P
  have hinner (α : MulAut (BinaryCarrier m hm0)) (hsq : α ^ 2 = 1)
      (_ : ∀ x ∈ P, α x = x) : ∃ x, α = MulAut.conj x :=
    EvenInvolutionGeometry.inner_of_odd_exponent m hm0 (hm1 ▸ (by decide : Odd 1)) α
      (k := 1) (by simpa only [pow_one] using hsq) (coverage m hm0 hs hp α)
  have hb := fixed_four_card_le_center center_eq_bot_of_simple_perfect P A hA hfix hinner
  have hc : Nat.card (center P) = 2 ^ m :=
    RadicalCoordinates.Centers.card_center_unipotent (binaryParameters m hm0) rfl
  rw [hc, hm1] at hb
  norm_num at hb

/-- The full triality field branch, conditional on the two independently
owned intrinsic automorphism calculations. Their hypotheses are discharged
on the actual central quotient, including at exponent one. -/
theorem largeField_of_triality_of_coverage_and_mixed_fixers
    (coverage : ∀ (n : ℕ) (hn : 0 < n),
      IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
      ∀ α : MulAut (BinaryCarrier n hn), ∃ g : BinaryCarrier n hn,
        ∃ e : CoefficientAut (binaryParameters n hn),
          α = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (mixed : ∀ (n : ℕ) (hn : 0 < n),
      IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
      Even n → ∀ (α : MulAut (BinaryCarrier n hn)) (k : ℕ), α ^ (2 ^ k) = 1 →
      (∃ g : BinaryCarrier n hn, ∃ e : CoefficientAut (binaryParameters n hn),
        α = MulAut.conj g * coefficientAction (binaryParameters n hn) e) →
      (∀ x ∈ unipotent (binaryParameters n hn), α x = x) →
      ∃ g : BinaryCarrier n hn, α = MulAut.conj g)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 ≤ m)
    (hi : IsTrialityGroupAt (2 ^ m) (NormalizerAction.componentImage K)) :
    LargeField K a := by
  have hm0 : 0 < m := by omega
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ m hm0).mp hi
  obtain ⟨hs, hp⟩ := exceptional_model_hypotheses K hK e
  let : IsSimpleGroup (BinaryCarrier m hm0) := hs
  let : Group.IsPerfect (BinaryCarrier m hm0) := hp
  let P := unipotentSylow (binaryParameters m hm0) rfl
  have hstandard (α : MulAut (BinaryCarrier m hm0)) (hsq : α ^ 2 = 1)
      (hfix : ∀ x ∈ P, α x = x) : ∃ x, α = MulAut.conj x := by
    have hpow : α ^ (2 ^ 1) = 1 := by simpa only [pow_one] using hsq
    have hform := coverage m hm0 hs hp α
    rcases Nat.even_or_odd m with heven | hodd
    · exact mixed m hm0 hs hp heven α 1 hpow hform hfix
    · exact EvenInvolutionGeometry.inner_of_odd_exponent m hm0 hodd α hpow hform
  have hmgt := triality_exponent_gt_one_of_coverage coverage K hK a hm hi
  refine ⟨m, hmgt, .triality m hm hi,
    EStar_le_component_of_model_involutive_fixers K hK a e ?_⟩
  exact involutive_fixers_of_standard P hstandard

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
