module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Stellmacher.Recognition.LyonsU3Four.OrderFourFusionFromAutomizer
public import Stellmacher.Recognition.LyonsU3Four.SylowQuarticCharacters
public import Theory.Character.IntegralRestriction
public import Theory.Character.Multiplicity

/-!
# Character constraints on the Lyons Sylow subgroup

This file records the arithmetic part of Lyons's Lemmas 3 and 5.  The
`integer_t` and `integer_z` fields below are deliberately witnesses in `ℤ`,
rather than assertions that a complex number is ``morally integral''.  This
makes the interface usable for actual ambient characters and keeps the
restriction multiplicity visible.  No ambient decomposition table is used.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 374 and
382, Lemmas 3 and 5(a,b).
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace Stellmacher.Recognition.LyonsU3Four

/- The integer witnesses and the two local arithmetic identities used by the
   printed proof.  The `pairing` identity is the quartic-character pairing
   (its numerator is a multiple of 64, hence `χ(1)-χ(z)` is a multiple of 16).
   The `average` identity is the principal multiplicity of the restriction. -/
public structure SylowCharacterConstraintData
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (χ : ClassFunction G) (t : S) : Prop where
  t_order : orderOf (t : G) = 4
  integer_t : ∃ a : ℤ, χ (t : G) = (a : ℂ)
  integer_z : ∃ b : ℤ, χ ((t : G) ^ 2) = (b : ℂ)
  pairing : ∀ a b : ℤ, χ (t : G) = (a : ℂ) →
    χ ((t : G) ^ 2) = (b : ℂ) → ∃ q : ℤ, a - b = 16 * q
  average : ∃ n : ℕ,
    χ 1 + 3 * χ ((t : G) ^ 2) + 60 * χ (t : G) = (64 * n : ℕ)

/- A compact form of Lemma 3, retaining the integer witnesses in the result. -/
public theorem lyons_lemma3
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {χ : ClassFunction G} {t : S}
    (_hχ : IsCharacter χ) (d : SylowCharacterConstraintData S χ t) :
    ∃ a b : ℤ, χ (t : G) = (a : ℂ) ∧
      χ ((t : G) ^ 2) = (b : ℂ) ∧ Int.ModEq 4 b a := by
  obtain ⟨a, ha⟩ := d.integer_t
  obtain ⟨b, hb⟩ := d.integer_z
  obtain ⟨q, hq'⟩ := d.pairing a b ha hb
  refine ⟨a, b, ha, hb, ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨4 * q, ?_⟩
  rw [hq']
  ring

/- The restriction average is the actual principal multiplicity.  This is
   separated from the class-counting identity so callers can provide the
   genuine restriction calculation from their local module. -/
public theorem lyons_lemma5b
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {χ : ClassFunction G} {t : S}
    (_hχ : IsCharacter χ) (d : SylowCharacterConstraintData S χ t) :
    ∃ n : ℕ,
      χ 1 + 3 * χ ((t : G) ^ 2) + 60 * χ (t : G) = (64 * n : ℕ) :=
  d.average

/- Restriction multiplicities for the three quartic constituents.  Equality of
   the three multiplicities is the fusion statement; positivity is the
   faithfulness statement in Lemma 5(a). -/
public theorem nonprincipal_degree_ge_twelve
    {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G} (_hχ : IsIrreducibleCharacter χ)
    (m : Fin 3 → ℕ)
    (hm : ∀ i, 0 < m i) {n : ℕ}
    (_hdegree : χ 1 = (n : ℂ))
    (hn : n = ∑ i : Fin 3, (4 * m i : ℕ)) :
    12 ≤ n := by
  have hsum : 12 ≤ ∑ i : Fin 3, (4 * m i : ℕ) := by
    have hone : ∀ i : Fin 3, 4 ≤ 4 * m i := by
      intro i
      have hi : 1 ≤ m i := Nat.succ_le_iff.mp (hm i)
      nlinarith
    calc
      12 = 4 + 4 + 4 := by norm_num
      _ ≤ 4 * m ⟨0, by decide⟩ + 4 * m ⟨1, by decide⟩ +
          4 * m ⟨2, by decide⟩ := by
        gcongr <;> apply hone
      _ = ∑ i : Fin 3, (4 * m i : ℕ) := by
        simp [Fin.sum_univ_succ, Nat.add_assoc]
  simpa [hn] using hsum

/- Public names matching the two constraints used by downstream assembly. -/
public theorem lyons_lemma5a
    {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (m : Fin 3 → ℕ) (hm : ∀ i, 0 < m i) {n : ℕ}
    (hdegree : χ 1 = (n : ℂ))
    (hn : n = ∑ i : Fin 3, (4 * m i : ℕ)) :
    12 ≤ n :=
  nonprincipal_degree_ge_twelve hχ m hm hdegree hn

public theorem equation3_4
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {χ : ClassFunction G} {t : S}
    (_hχ : IsCharacter χ) (d : SylowCharacterConstraintData S χ t) :
    ∃ a b : ℤ, χ (t : G) = (a : ℂ) ∧
      χ ((t : G) ^ 2) = (b : ℂ) ∧ Int.ModEq 4 b a :=
  lyons_lemma3 _hχ d

/- A single package is convenient for consumers which already have the local
   multiplicity calculation. -/
public structure GenuineSylowCharacterConstraints
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (χ : ClassFunction G) (t : S) : Prop where
  character : IsCharacter χ
  irreducible : IsIrreducibleCharacter χ
  values : SylowCharacterConstraintData S χ t
  irreducible_degree : ∀ (m : Fin 3 → ℕ),
    (∀ i, 0 < m i) → ∃ n : ℕ, χ 1 = (n : ℂ) ∧
      n = ∑ i : Fin 3, (4 * m i : ℕ)

public theorem GenuineSylowCharacterConstraints.mod_four
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {χ : ClassFunction G} {t : S}
    (h : GenuineSylowCharacterConstraints χ t) :
    ∃ a b : ℤ, χ (t : G) = (a : ℂ) ∧
    χ ((t : G) ^ 2) = (b : ℂ) ∧ Int.ModEq 4 b a :=
  lyons_lemma3 h.character h.values

public theorem GenuineSylowCharacterConstraints.degree_ge_twelve
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {χ : ClassFunction G} {t : S}
    (h : GenuineSylowCharacterConstraints χ t)
    (m : Fin 3 → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ n : ℕ, χ 1 = (n : ℂ) ∧ 12 ≤ n := by
  obtain ⟨n, hnχ, hn⟩ := h.irreducible_degree m hm
  exact ⟨n, hnχ, nonprincipal_degree_ge_twelve
    (by
      exact h.irreducible) m hm hnχ hn⟩

end Stellmacher.Recognition.LyonsU3Four
