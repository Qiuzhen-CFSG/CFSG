module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import Theory.SpecificGroups.SL2.EvenBorelResidual.SemilinearCommutator
public import Theory.SpecificGroups.SL2.EvenBorelResidual.TwoPowerField
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Residual torus fixers and outer actors in binary PSL₂

For the specified Sylow two-subgroup S, the source B = O²(N(S)) is N(S)
and its embedded two-core is S. Sylow conjugacy identifies this Borel
with the standard upper triangular Borel. Universal semilinear coverage,
kept as the exact earlier automorphism-classification input, then gives an
inner Borel factor and a field factor for each actual actor.

The proved projection calculation identifies fixation of
O³(B)O₂(B)/O₂(B) with fixation of O³(Fˣ). Every power relation on the
actor holds on its field part. For actors in a two-group stabilizing S,
trivial field part is equivalent to membership in the inner image of S.
The finite-field calculation then forces degree two or six for any
noninner torus fixer. Outside those degrees, the full fixer set in A is
exactly the inner image of S. In degree six every outer actor has torus
displacement of order nine. The actual cyclic-action commutator projects
onto a group containing that displacement image, and this projection kills
its intrinsic two-core; hence its two-core quotient has order at least nine.
No involution or pure-field hypothesis is imposed on the actor.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
This completes the intrinsic L₂ calculation subject only to the explicitly
stated earlier semilinear automorphism-classification input. Degree two
remains the L₂(4) exception. On later ambient lifting the separate kernel
C_T(K) must still be retained, as in the imported residual module.
-/

public section

open Subgroup
open scoped MatrixGroups
open Atlas Matrix.ProjectiveSpecialLinearGroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearTwo
open OddBorel EvenBorelResidual EvenBorelResidual.Semilinear
variable {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem borelResidual_eq (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(2,F)) :
    borelResidual (normalizer (S : Set PSL(2,F))) = normalizer (S : Set PSL(2,F)) := by
  rw [borelResidual, residualIn, sylowNormalizer_twoResidual F hn hF S,
    ← MonoidHom.range_eq_map, range_subtype]

theorem borelResidual_twoCoreIn (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(2,F)) :
    (borelResidual (normalizer (S : Set PSL(2,F)))).pCoreIn 2 =
      (S : Subgroup PSL(2,F)) := by
  rw [borelResidual_eq hn hF, sylowNormalizer_twoCoreIn F hF]

/-- Reduction of every actual two-power actor, including its inner twist,
to a field action on the units. The chosen Sylow and source residual are retained. -/
theorem actor_field_reduction (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F))) (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hcoverage : ∀ β : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      β = MulAut.conj g * fieldEquivPSL 2 σ)
    (a : MulAut PSL(2,F)) (ha : a ∈ A) :
    ∃ (c : PSL(2,F)) (g : borel F) (σ : F ≃+* F) (k : ℕ),
      (kernel F).map (MulAut.conj c).toMonoidHom = S ∧
      (borel F).map (MulAut.conj c).toMonoidHom =
        borelResidual (normalizer (S : Set PSL(2,F))) ∧
      MulAut.congr (MulAut.conj c).symm a =
        MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ ∧
      σ ^ (2 ^ k) = 1 ∧
      (FixesResidualTorus (borelResidual (normalizer (S : Set PSL(2,F)))) a ↔
        ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u) ∧
      (σ = 1 ↔ a ∈ (S : Subgroup PSL(2,F)).map MulAut.conj) := by
  obtain ⟨c, g, σ, hcU, hcB, he⟩ :=
    aligned_semilinear_of_coverage F S a (hstable a ha) hcoverage
  let e := MulAut.conj c
  obtain ⟨k, hk⟩ := hA (⟨a, ha⟩ : A)
  have hak : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hpow : (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) ^ (2 ^ k) = 1 := by
    rw [← he, ← map_pow, hak, map_one]
  refine ⟨c, g, σ, k, hcU, ?_, he, field_pow_eq_one_of_actor_pow F g σ (2 ^ k) hpow, ?_, ?_⟩
  · rwa [borelResidual_eq hn hF]
  · have hback : MulAut.congr e (MulAut.congr e.symm a) = a := by
      ext x
      simp [MulAut.congr]
    have ht := fixesResidualTorus_map_iff e (borel F) (MulAut.congr e.symm a)
    rw [hback, hcB, he] at ht
    rw [borelResidual_eq hn hF]
    exact ht.trans (fixesResidualTorus_iff F hF g σ)
  · constructor
    · intro hσ
      have hfield : fieldEquivPSL 2 σ = 1 := by
        change RankOneFieldAutomorphisms.pslFieldAction σ = 1
        rw [hσ, map_one]
      have hi : MulAut.conj (g : PSL(2,F)) ^ (2 ^ k) = 1 := by
        simpa only [hfield, mul_one] using hpow
      have hg := inner_mem_kernel_of_pow F hF g k hi
      have hS : e (g : PSL(2,F)) ∈ (S : Subgroup PSL(2,F)) := by
        rw [← hcU]
        exact mem_map_of_mem _ hg
      refine ⟨e (g : PSL(2,F)), hS, ?_⟩
      apply (MulAut.congr e.symm).injective
      rw [MulAut.congr_conj, e.symm_apply_apply]
      simpa only [hfield, mul_one] using he.symm
    · rintro ⟨x, hx, rfl⟩
      apply (semilinear_inner_iff F (g : PSL(2,F)) σ).mp
      exact ⟨e.symm x, he.symm.trans (MulAut.congr_conj e.symm x)⟩

/-- A torus-fixing two-power actor is inner on the specified Sylow, unless
the field has degree two or six. -/
theorem inner_or_exception_of_fixesResidualTorus
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F))) (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hcoverage : ∀ β : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      β = MulAut.conj g * fieldEquivPSL 2 σ)
    (a : MulAut PSL(2,F)) (ha : a ∈ A)
    (hfix : FixesResidualTorus (borelResidual (normalizer (S : Set PSL(2,F)))) a) :
    a ∈ (S : Subgroup PSL(2,F)).map MulAut.conj ∨ n = 2 ∨ n = 6 := by
  obtain ⟨c, g, σ, k, _, _, _, hpow, hfixσ, hinner⟩ :=
    actor_field_reduction hn hF S A hA hstable hcoverage a ha
  by_cases hσ : σ = 1
  · exact Or.inl (hinner.mp hσ)
  · exact Or.inr (FiniteField.BinaryTorusTwoPower.degree_eq_two_or_six_of_fixed_residual
      σ hn hF hσ hpow (hfixσ.mp hfix))

/-- Outside degrees two and six, fixation of the actual residual torus is
equivalent to membership in the inner image of the specified Sylow subgroup. -/
theorem actor_fixesResidualTorus_iff
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F))) (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hcoverage : ∀ β : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      β = MulAut.conj g * fieldEquivPSL 2 σ)
    (a : MulAut PSL(2,F)) (ha : a ∈ A) :
    FixesResidualTorus (borelResidual (normalizer (S : Set PSL(2,F)))) a ↔
      a ∈ (S : Subgroup PSL(2,F)).map MulAut.conj := by
  constructor
  · intro hfix
    rcases inner_or_exception_of_fixesResidualTorus hn hF S A hA hstable hcoverage
      a ha hfix with h | h | h
    · exact h
    · exact (hn2 h).elim
    · exact (hn6 h).elim
  · intro haS
    obtain ⟨c, g, σ, k, _, _, _, _, hfixσ, hinner⟩ :=
      actor_field_reduction hn hF S A hA hstable hcoverage a ha
    apply hfixσ.mpr
    rw [hinner.mpr haS]
    intro u _
    rfl

/-- The full set of actors in A fixing O³(B)O₂(B)/O₂(B) is the inner
image of S. Containment of that image in A is retained explicitly. -/
theorem residualTorus_fixers_eq
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F))) (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hinner : (S : Subgroup PSL(2,F)).map MulAut.conj ≤ A)
    (hcoverage : ∀ β : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      β = MulAut.conj g * fieldEquivPSL 2 σ) :
    {a | a ∈ A ∧ FixesResidualTorus
      (borelResidual (normalizer (S : Set PSL(2,F)))) a} =
        ((S : Subgroup PSL(2,F)).map MulAut.conj : Set (MulAut PSL(2,F))) := by
  ext a
  constructor
  · rintro ⟨ha, hfix⟩
    exact (actor_fixesResidualTorus_iff hn hF hn2 hn6 S A hA hstable hcoverage a ha).mp hfix
  · intro haS
    exact ⟨hinner haS,
      (actor_fixesResidualTorus_iff hn hF hn2 hn6 S A hA hstable hcoverage a
        (hinner haS)).mpr haS⟩

/-- In degree six, an arbitrary outer actor has commutator quotient order
at least nine. The quotient uses the intrinsic two-core of the entire cyclic
action commutator; no involution or pure-field assumption is needed. -/
theorem outer_commutator_quotient_card_ge_nine
    (hF : Nat.card F = 2 ^ 6)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F))) (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hcoverage : ∀ β : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      β = MulAut.conj g * fieldEquivPSL 2 σ)
    (a : MulAut PSL(2,F)) (ha : a ∈ A)
    (houter : a ∉ (MulAut.conj : PSL(2,F) →* MulAut PSL(2,F)).range) :
    let C := commutatorSubgroup (zpowers a) PSL(2,F)
      (borelResidual (normalizer (S : Set PSL(2,F))))
    9 ≤ Nat.card (C ⧸ pCore 2 C) := by
  obtain ⟨c, g, σ, k, _, hB, he, hpow, _, hinner⟩ :=
    actor_field_reduction (by decide : 1 < 6) hF S A hA hstable hcoverage a ha
  have hσ : σ ≠ 1 := by
    intro h
    obtain ⟨x, _, hx⟩ := hinner.mp h
    exact houter ⟨x, hx⟩
  have hbound := SemilinearCommutator.displacement_card_le_commutator_quotient F g σ
  rw [FiniteField.BinaryTorusTwoPower.card_displacement_of_card_two_pow_six
    σ hF hσ hpow] at hbound
  let e := MulAut.conj c
  have hback : MulAut.congr e (MulAut.congr e.symm a) = a := by
    ext x
    simp [MulAut.congr]
  have hcard := SemilinearCommutator.cyclic_commutator_quotient_card
    e (borel F) (MulAut.congr e.symm a) 2
  dsimp only at hcard ⊢
  rw [hback, hB, he] at hcard
  exact hcard ▸ hbound

/-- The degree-six outer-actor bound in the proof of 13.8.20. Degree two
remains the L₂(4) exception. -/
theorem outer_commutator_quotient_card_gt_three
    (hF : Nat.card F = 2 ^ 6)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup (MulAut PSL(2,F))) (hA : IsPGroup 2 A)
    (hstable : ∀ a ∈ A, (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hcoverage : ∀ β : MulAut PSL(2,F), ∃ (g : PSL(2,F)) (σ : F ≃+* F),
      β = MulAut.conj g * fieldEquivPSL 2 σ)
    (a : MulAut PSL(2,F)) (ha : a ∈ A)
    (houter : a ∉ (MulAut.conj : PSL(2,F) →* MulAut PSL(2,F)).range) :
    let C := commutatorSubgroup (zpowers a) PSL(2,F)
      (borelResidual (normalizer (S : Set PSL(2,F))))
    3 < Nat.card (C ⧸ pCore 2 C) :=
  lt_of_lt_of_le (by decide : 3 < 9)
    (outer_commutator_quotient_card_ge_nine hF S A hA hstable hcoverage a ha houter)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearTwo
