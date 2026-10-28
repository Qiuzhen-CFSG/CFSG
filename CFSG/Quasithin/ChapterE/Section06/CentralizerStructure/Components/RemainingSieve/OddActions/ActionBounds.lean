module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.OddLinearFixed
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Sylow action bounds for the odd cases of E.6.8

The actual Sylow intersection is fixed pointwise by V. If its pointwise
fixers are conjugations by Sylow elements, the V-action embeds in the image
of the Sylow center. For Fermat or Mersenne PSL₂ models that center has
order at most two once p ≥ 7. Perfection excludes p = 3, and the actual
PSL₂(5) ≃ PSL₂(4) comparison excludes p = 5 in the non-Lie branch.

These theorems prove the PSL₂ action bound. They do not identify U with
C_V(L), and do not settle the PSL₂(4) branch in the Lie sieve.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8,
printed pp.247–248, and 1.1.5(3)(e), printed p.502.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
open Chapter15.Section04.LocalSetup
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

omit [Finite G] in
/-- Literal conjugation by V fixes the component's actual Sylow intersection. -/
theorem component_fixes_sylow (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {v : G} (hv : v ∈ V) (x : S) :
    v * ((x : L) : G) * v⁻¹ = ((x : L) : G) := by
  have hx := mem_map_of_mem L.subtype x.property
  rw [hS] at hx
  have hh : v * ((x : L) : G) = ((x : L) : G) * v :=
    mem_centralizer_iff.mp hx.2.2 v hv
  rw [hh, mul_inv_cancel_right]

/-- Pointwise Sylow innerness bounds the order of the actual induced action image. -/
theorem action_image_card_le_sylow_center (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hinner : ∀ a : MulAut L, (∀ x ∈ S, a x = x) → ∃ x ∈ S, a = MulAut.conj x) :
    Nat.card (inducedAutomizer L V) ≤ Nat.card (center S) := by
  let J := (inducedAutomizer L V).map (Automizer L).subtype
  let f : S →* MulAut L := MulAut.conj.comp (S : Subgroup L).subtype
  have hJ : J ≤ (center S).map f := by
    rintro a ⟨b, ⟨v, hv, rfl⟩, rfl⟩
    have hvfix : ∀ x ∈ S, L.normalizerMonoidHom v x = x := by
      intro x hx
      apply Subtype.ext
      exact hfix v hv ⟨x, hx⟩
    obtain ⟨x, hx, he⟩ := hinner (L.normalizerMonoidHom v) hvfix
    have hc : (⟨x, hx⟩ : S) ∈ center S := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hh := hvfix y y.property
      rw [he] at hh
      change x * (y : L) * x⁻¹ = (y : L) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact ⟨⟨x, hx⟩, hc, he.symm⟩
  calc
    Nat.card (inducedAutomizer L V) = Nat.card J :=
      (Subgroup.card_map_of_injective (Automizer L).subtype_injective).symm
    _ ≤ Nat.card ((center S).map f) :=
      Nat.card_le_card_of_injective (inclusion hJ) (inclusion_injective hJ)
    _ ≤ Nat.card (center S) := Nat.le_of_dvd Nat.card_pos ((center S).card_map_dvd f)

/-- A Sylow center of order at most two bounds the binary action corank by one. -/
theorem actionCorank_le_one_of_sylow_fixers
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hinner : ∀ a : MulAut L, (∀ x ∈ S, a x = x) → ∃ x ∈ S, a = MulAut.conj x)
    (hcard : Nat.card (center S) ≤ 2) : actionCorank V L ≤ 1 := by
  rw [actionCorank, ← rank_inducedAutomizer L V hN]
  exact (Nat.log_mono_right ((action_image_card_le_sylow_center S hfix hinner).trans hcard)).trans
    (by decide)

/-- Transport the proved prime-field pointwise-fixer theorem through the actual model. -/
theorem odd_linear_fixed_inner {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : ClassicalGroup.IsPSL X 2 p)
    (S : Sylow 2 X) (a : MulAut X) (ha : ∀ x ∈ S, a x = x) :
    ∃ x ∈ S, a = MulAut.conj x := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := odd_linear_equiv_prime_field hm
  exact Theory.PSL2.SylowFixedQuotients.fixed_inner_transport e (S : Subgroup X)
    (Theory.PSL2.primeField_sylow_fixed_inner (hp.odd_of_ne_two (by omega)) hp3
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)) a ha

omit [Finite G] in
/-- Small primes are excluded by perfection and the concrete characteristic-two comparison. -/
theorem seven_le_prime_of_nonLie [IsQuasisimple L]
    {p : ℕ} (hp : IsFermatOrMersennePrime p)
    (hm : ClassicalGroup.IsPSL L 2 p) (hn : ¬ LieTypeComponent L) : 7 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hb : 1 < (2 : ℕ) ^ (2 ^ k) := one_lt_pow' (by decide) (by positivity)
      omega
    · rcases k with _ | k
      · norm_num at hk
      · rw [pow_succ] at hk
        omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hF
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have hp5 : p ≠ 5 := by
    rintro rfl
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    apply hn
    apply Or.inl
    apply ClassificationModels.IsBenderModel.linear 2 (by decide)
    refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, ?_⟩
    · rw [GaloisField.card 2 2 (by decide)]
    · exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)⟩
  have hge := hp.1.two_le
  obtain ⟨k, hk⟩ := hp.1.odd_of_ne_two hp2
  omega

/-- The PSL₂ part of E.6.8(5) has action corank at most one in the non-Lie sieve. -/
theorem odd_linear_actionCorank_le_one
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (hn : ¬ LieTypeComponent L)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL L 2 p) :
    actionCorank V L ≤ 1 := by
  let _ := hL.2.2
  let _ := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)
  have hp7 := seven_le_prime_of_nonLie hp hm hn
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  exact actionCorank_le_one_of_sylow_fixers (component_normalized h hU hL) S
    (fun _ hv => component_fixes_sylow S hS hv)
    (fun a ha => odd_linear_fixed_inner hp.1 (by omega) hm S a ha)
    (odd_linear_sylow_center_card_le_two hp hp7 hm S)

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
