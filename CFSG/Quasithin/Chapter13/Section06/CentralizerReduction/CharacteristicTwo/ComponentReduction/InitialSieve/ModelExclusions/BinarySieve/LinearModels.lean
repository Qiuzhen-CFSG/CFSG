module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.ActionTransport
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Linear models in the binary component sieve

Pointwise Sylow fixers in binary PSL₂ and PSL₃ are inner. Applying this to
the literal marked action puts E* in K*. In degree three the fixer is the
image of the Sylow center, of order 2^m; a faithful four-group therefore
forces m > 1. In binary degrees four and five, the same center bound is
two, excluding both models entirely. All transports retain the actual
projective quotient and the defining field.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927. Intrinsic Sylow
fixer calculations are also used in E.6.8 and 16.1.6, pp.247–248 and 1172.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module

private theorem fixer_card_le_center {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (A : Subgroup (MulAut Q))
    (hconj : ∀ α ∈ A, ∃ z ∈ (center S).map (S : Subgroup Q).subtype,
      α = MulAut.conj z) : Nat.card A ≤ Nat.card (center S) := by
  classical
  let C := (center S).map (S : Subgroup Q).subtype
  have hex (α : A) : ∃ z : C, α.val = MulAut.conj z.val := by
    obtain ⟨z, hz, hα⟩ := hconj α α.property
    exact ⟨⟨z,hz⟩,hα⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro α β he
    apply Subtype.ext
    rw [hf α, hf β, he]
  have hb := Nat.card_le_card_of_injective f hinj
  let e := (center S).equivMapOfInjective (S : Subgroup Q).subtype Subtype.val_injective
  exact hb.trans_eq (Nat.card_congr e.toEquiv).symm

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- Binary PSL₂ has no outer pointwise Sylow fixers, so the marked four
lies in the component. Its source parameter already satisfies m ≥ 2. -/
theorem largeField_of_linear_two (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 2 ≤ m)
    (hi : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m)) :
    LargeField K a := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  refine ⟨m, by omega, .linear_two m hm ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩,
    EStar_le_component_of_model_fixers K hK a e ?_⟩
  intro S α hfix
  obtain ⟨z,_,hz⟩ := Theory.PSL2.aut_fixing_sylow_inner S α hfix
  exact ⟨z,hz.symm⟩

/-- The full linear-three branch, including exclusion of exponent one. -/
theorem largeField_of_linear_three (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 ≤ m)
    (hi : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 3 (2 ^ m)) :
    LargeField K a := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hi
  have hcontain := EStar_le_component_of_model_fixers K hK a e (by
    intro S α hfix
    obtain ⟨z, _, hz⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
      F (by omega : 0 < m) hF (MulEquiv.refl _) S α hfix
    exact ⟨z,hz.symm⟩)
  have hmgt : 1 < m := by
    by_contra h
    have he : m = 1 := by omega
    obtain ⟨S,A,hA,hfix⟩ := exists_fixed_four_of_equiv K hK a e
    have hb := fixer_card_le_center S A (by
      intro α hα
      exact Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv F
        (by omega : 0 < m) hF (MulEquiv.refl _) S α (hfix α hα))
    rw [hA.card_four, Matrix.PSL3.LinearThree.card_center_sylow F (by omega) hF S,
      he] at hb
    norm_num at hb
  exact ⟨m,hmgt,.linear_three m hm ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩,hcontain⟩

/-- Neither of the binary higher-linear models admits the marked four-group. -/
theorem not_binary_linear (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (NormalizerAction.componentImage K) n 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let eQ := (e.trans (Atlas.fieldEquivPSL n f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n))
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_injective eQ.symm eQ.symm.injective
  obtain ⟨S,A,hA,hfix⟩ := exists_fixed_four_of_equiv K hK a eQ
  have hb := fixer_card_le_center S A (by
    intro α hα
    obtain ⟨z,hz,he⟩ := BinaryLinear.OuterCyclic.sylow_fixing_inner hn S α (hfix α hα)
    refine ⟨z, ⟨⟨z,hz⟩,?_,rfl⟩, he⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hx := hfix α hα x x.property
    rw [he, MulAut.conj_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm)
  have hc := BinaryLinear.linear_sylow_center_card_le_two (by omega : 2 ≤ n) S
  rw [hA.card_four] at hb
  have hbad : 4 ≤ 2 := hb.trans hc
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
