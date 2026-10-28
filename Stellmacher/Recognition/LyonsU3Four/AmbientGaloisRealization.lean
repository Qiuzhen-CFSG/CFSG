module

public import Stellmacher.Recognition.LyonsU3Four.AmbientGaloisSymmetry
public import Stellmacher.Recognition.LyonsU3Four.BrauerDegreeIdentities
public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeData
public import Theory.Character.UniqueDegreeRationality
public import Theory.Character.ModularBlock.PrincipalGalois
public import Theory.Character.CyclotomicPrimeBound

/-!
# Realizable local Galois transport for the ambient Lyons rows

The ordered exponents are `[0,1,2,4,3]`, and the displayed column cycle
multiplies exponents by three modulo five. Thus it is the automorphism
`μ ↦ μ³` which realizes that cycle. The inverse exponent two does not satisfy
the same forward transport identity.

Independence of the five powers on odd-order elements makes every coefficient
identity a consequence of the actual section expansions. An automorphism
fixing fifth roots fixes all six columns. If a row is separated by these
columns and its degree, whole-character transport therefore fixes that row
at every group element. Separately, uniqueness of a degree in the principal
block implies integer values once arbitrary whole-character block actions
are available.

The final assembly constructs these actions using principal congruence block
closure. The separated-row fixed-value theorem then supplies the hypothesis
of the cyclotomic prime bound. All inputs are actual characters and their
section expansions, independently of the numerical constraints being proved.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), p. 374 and pp. 385–386.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]
open GeneralizedDecompositionData

/-- The actual permutation of the five local exponents. -/
@[expose] def galoisColumnEquiv : Equiv.Perm (Fin 5) where
  toFun := galoisColumn
  invFun i := galoisColumn (galoisColumn (galoisColumn i))
  left_inv := galoisColumn_four
  right_inv := galoisColumn_four

/-- Section independence also allows any reindexing of the five powers. -/
theorem fivePowers_coefficients_unique {H : Type*} [Group H] [Finite H]
    (μ : H →* ℂ) (hμ : orderOf μ = 5) (e : Equiv.Perm (Fin 5))
    (x y : Fin 5 → ℤ)
    (heq : ∀ v : H, Odd (orderOf v) →
      (∑ i, (x i : ℂ) * μ v ^ basicExponent (e i)) =
        ∑ i, (y i : ℂ) * μ v ^ basicExponent i) :
    ∀ i, x i = y (e i) := by
  have hli := (fivePowers_independent_on_odd μ hμ).comp e e.injective
  have he : ∀ i, (x i : ℂ) = (y (e i) : ℂ) := by
    apply Fintype.linearIndependent_iffₛ.mp hli
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rw [heq v.val v.property]
    exact (Equiv.sum_comp e (fun i => (y i : ℂ) * μ v.val ^ basicExponent i)).symm
  intro i
  exact_mod_cast he i

/-- The homomorphism's order controls every value. -/
theorem fifthPower_eq_one_of_order_five {H : Type*} [Group H]
    (μ : H →* ℂ) (hμ : orderOf μ = 5) (v : H) : μ v ^ 5 = 1 := by
  have hh := DFunLike.congr_fun
    (show μ ^ 5 = 1 by rw [← hμ]; exact pow_orderOf_eq_one μ) v
  simpa using hh

/-- The column cycle uses the exponent three, inverse to two modulo five. -/
theorem galoisColumn_exponent_three (i : Fin 5) :
    (3 * basicExponent i) % 5 = basicExponent (galoisColumn i) := by
  fin_cases i <;> rfl

/-- Applying an actual whole-character automorphism transports the integral
section coefficients by the same permutation as its action on local powers. -/
theorem PrincipalBlockGaloisAction.column_transport
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    {σ : ℂ ≃+* ℂ} (a : PrincipalBlockGaloisAction b σ)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5) (e : Equiv.Perm (Fin 5))
    (hpow : ∀ v i, σ (μ v ^ basicExponent i) = μ v ^ basicExponent (e i))
    (j : {i // i ∈ b.block}) :
    c.dT j = c.dT (a.perm j) ∧
      ∀ i, c.iDz i j = c.iDz (e i) (a.perm j) := by
  constructor
  · have he := a.character_eq j t
    rw [h31.at_t, h31.at_t, map_intCast] at he
    exact_mod_cast he
  · apply fivePowers_coefficients_unique μ hμ e (fun i => c.iDz i j)
      (fun i => c.iDz i (a.perm j))
    intro v hv
    have he := a.character_eq j (z * (v : G))
    have hj := h31.2 j v hv
    have hk := h31.2 (a.perm j) v hv
    dsimp only at hj hk
    rw [hj, hk, map_sum] at he
    simpa only [map_mul, map_intCast, hpow] using he

/-- A correctly oriented replacement for the older power-two contract. -/
theorem galoisSymmetry_of_principalBlockAction_cube
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5) {σ : ℂ ≃+* ℂ}
    (a : PrincipalBlockGaloisAction b σ)
    (hσ : ∀ v, σ (μ v) = μ v ^ 3) : c.GaloisSymmetry := by
  refine ⟨a.perm, a.column_transport c h31 hμ galoisColumnEquiv ?_⟩
  intro v i
  rw [map_pow, hσ, ← pow_mul]
  change μ v ^ (3 * basicExponent i) = μ v ^ basicExponent (galoisColumn i)
  rw [← galoisColumn_exponent_three i]
  exact pow_eq_pow_mod _ (fifthPower_eq_one_of_order_five μ hμ v)

/-- The positive degree of an actual principal-block row, independently of
any of the numerical constraints on the supplied integral columns. -/
@[expose] def ambientRowDegree (b : PrincipalCongruenceBlockData G)
    (j : {i // i ∈ b.block}) : ℕ :=
  (ofConj_irreducible (b.complete.1 j.val)).degree

/-- A separated row is fixed as a whole character whenever the automorphism
fixes the local fifth roots. This uses actual character transport and degree
preservation, not merely a permutation of the six integral arrays. -/
theorem PrincipalBlockGaloisAction.fixes_separatedRow
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    {σ : ℂ ≃+* ℂ} (a : PrincipalBlockGaloisAction b σ)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5)
    (hσ : ∀ w : ℂ, w ^ 5 = 1 → σ w = w)
    (j : {i // i ∈ b.block})
    (hsep : c.RowSeparated (fun k => (ambientRowDegree b k : ℤ)) j) :
    a.perm j = j := by
  have hc := a.column_transport c h31 hμ (Equiv.refl _) (by
    intro v i
    simp only [map_pow, hσ (μ v) (fifthPower_eq_one_of_order_five μ hμ v),
      Equiv.refl_apply]) j
  apply hsep (a.perm j) 1 (by norm_num)
  · simpa only [one_mul, ambientRowDegree] using congrArg (fun n : ℕ => (n : ℤ)) (a.degree_eq j)
  · simpa only [one_mul] using hc.1.symm
  · intro i
    simpa only [one_mul, Equiv.refl_apply] using (hc.2 i).symm

/-- Whole-character invariance under the fifth-root fixing subgroup. -/
theorem PrincipalBlockGaloisAction.character_fixed_of_separated
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    {σ : ℂ ≃+* ℂ} (a : PrincipalBlockGaloisAction b σ)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5)
    (hσ : ∀ w : ℂ, w ^ 5 = 1 → σ w = w)
    (j : {i // i ∈ b.block})
    (hsep : c.RowSeparated (fun k => (ambientRowDegree b k : ℤ)) j) (g : G) :
    σ (b.chi j.val (ConjClasses.mk g)) = b.chi j.val (ConjClasses.mk g) := by
  rw [a.character_eq, a.fixes_separatedRow c h31 hμ hσ j hsep]

/-- The local cube action is realizable over the complex numbers. -/
theorem exists_fifthRoot_cube_automorphism :
    ∃ σ : ℂ ≃+* ℂ, ∀ w : ℂ, w ^ 5 = 1 → σ w = w ^ 3 := by
  obtain ⟨σ, hσ⟩ := Section1.complex_galois_aut_pow_on_roots
    (show Nat.Coprime 3 5 by decide)
  exact ⟨σ.toRingEquiv, hσ⟩

/-- Final column transport, conditional only on constructing the actual
principal-block actions. The owner discharges this premise by block closure. -/
theorem galoisSymmetry_of_actions
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5)
    (ha : ∀ σ : ℂ ≃+* ℂ, Nonempty (PrincipalBlockGaloisAction b σ)) :
    c.GaloisSymmetry := by
  obtain ⟨σ, hσ⟩ := exists_fifthRoot_cube_automorphism
  obtain ⟨a⟩ := ha σ
  exact galoisSymmetry_of_principalBlockAction_cube c h31 hμ a
    (fun v => hσ (μ v) (fifthPower_eq_one_of_order_five μ hμ v))

/-- Degree-preserving version used by the signed numerical constraints. -/
theorem signedGaloisSymmetry_of_actions
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5)
    (ha : ∀ σ : ℂ ≃+* ℂ, Nonempty (PrincipalBlockGaloisAction b σ)) :
    c.SignedGaloisSymmetry (fun j => (ambientRowDegree b j : ℤ)) := by
  obtain ⟨σ, hσ⟩ := exists_fifthRoot_cube_automorphism
  obtain ⟨a⟩ := ha σ
  have hc := a.column_transport c h31 hμ galoisColumnEquiv (by
    intro v i
    rw [map_pow, hσ (μ v) (fifthPower_eq_one_of_order_five μ hμ v), ← pow_mul]
    change μ v ^ (3 * basicExponent i) = μ v ^ basicExponent (galoisColumn i)
    rw [← galoisColumn_exponent_three i]
    exact pow_eq_pow_mod _ (fifthPower_eq_one_of_order_five μ hμ v))
  refine ⟨a.perm, fun j => ⟨1, by norm_num, ?_, ?_, ?_⟩⟩
  · simpa only [one_mul, ambientRowDegree] using congrArg (fun n : ℕ => (n : ℤ)) (a.degree_eq j).symm
  · simpa only [one_mul] using (hc j).1
  · simpa [galoisColumnEquiv] using (hc j).2

/-- Uniqueness of the degree inside the principal block suffices for integer
values once whole-character closure under arbitrary automorphisms is proved. -/
theorem principalBlock_integer_of_unique_degree_of_actions
    (b : PrincipalCongruenceBlockData G)
    (ha : ∀ σ : ℂ ≃+* ℂ, Nonempty (PrincipalBlockGaloisAction b σ))
    (j : {i // i ∈ b.block})
    (hunique : ∀ k, ambientRowDegree b k = ambientRowDegree b j → k = j) :
    ∀ g : G, ∃ n : ℤ, b.chi j.val (ConjClasses.mk g) = (n : ℂ) := by
  apply (ofConj_irreducible (b.complete.1 j.val)).integer_of_fixed
  intro σ g
  obtain ⟨a⟩ := ha σ
  have hj : a.perm j = j := hunique (a.perm j) (a.degree_eq j)
  change σ (b.chi j.val (ConjClasses.mk g)) = b.chi j.val (ConjClasses.mk g)
  rw [a.character_eq, hj]

/-- Every complex automorphism preserves the actual principal block. -/
theorem principalBlock_galois_stable
    (b : PrincipalCongruenceBlockData G) (σ : ℂ ≃+* ℂ) (i : b.I) :
    i ∈ b.block ↔ galoisPermutation b.chi b.complete σ i ∈ b.block :=
  b.mem_block_iff_of_galois σ i (galoisPermutation b.chi b.complete σ i)
    (fun g => (galoisPermutation_spec b.chi b.complete σ i g).symm)

/-- The whole-character action, constructed without a block-closure premise. -/
@[expose] def actualPrincipalBlockGaloisAction
    (b : PrincipalCongruenceBlockData G) (σ : ℂ ≃+* ℂ) :
    PrincipalBlockGaloisAction b σ :=
  principalBlockGaloisAction b σ (principalBlock_galois_stable b σ)

/-- Actual principal-block characters admit every complex automorphism. -/
theorem principalBlock_actions (b : PrincipalCongruenceBlockData G)
    (σ : ℂ ≃+* ℂ) : Nonempty (PrincipalBlockGaloisAction b σ) :=
  ⟨actualPrincipalBlockGaloisAction b σ⟩

/-- Genuine section expansions give the correctly oriented column symmetry. -/
theorem ambient_galoisSymmetry
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5) : c.GaloisSymmetry :=
  galoisSymmetry_of_actions c h31 hμ (principalBlock_actions b)

/-- The same actual action preserves the positive character degrees. -/
theorem ambient_signedGaloisSymmetry
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5) :
    c.SignedGaloisSymmetry (fun j => (ambientRowDegree b j : ℤ)) :=
  signedGaloisSymmetry_of_actions c h31 hμ (principalBlock_actions b)

/-- Separation of a genuine row implies invariance of its whole character
under every automorphism fixing fifth roots. -/
theorem ambient_character_fixed_of_separated
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5) (j : {i // i ∈ b.block})
    (hsep : c.RowSeparated (fun k => (ambientRowDegree b k : ℤ)) j)
    (σ : ℂ ≃+* ℂ) (hσ : ∀ w : ℂ, w ^ 5 = 1 → σ w = w) (g : G) :
    σ (b.chi j.val (ConjClasses.mk g)) = b.chi j.val (ConjClasses.mk g) :=
  (actualPrincipalBlockGaloisAction b σ).character_fixed_of_separated
    c h31 hμ hσ j hsep g

/-- The separated-row prime bound from the genuine ambient characters.
Small primes follow directly from the degree threshold; larger primes use
the fifth-cyclotomic fixed-value argument and faithfulness in a simple group. -/
theorem ambient_primeConstraints [IsSimpleGroup G]
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (hμ : orderOf μ = 5) :
    c.PrimeConstraints (fun j => (ambientRowDegree b j : ℤ)) (Nat.card G) := by
  constructor
  · intro j
    simpa only [Int.natAbs_natCast, ambientRowDegree] using
      (ofConj_irreducible (b.complete.1 j.val)).degree_dvd_card
  · intro j hj hsep p hp hdiv
    simp only [Int.natAbs_natCast] at hj ⊢
    by_cases hp5 : 5 < p
    · apply (ofConj_irreducible (b.complete.1 j.val)).prime_le_degree_add_one_of_fixed_fifth_roots
        (by change 1 < ambientRowDegree b j; omega) _ hp hp5 hdiv
      intro σ hσ g
      exact ambient_character_fixed_of_separated c h31 hμ j hsep σ hσ g
    · omega

/-- A unique-degree principal-block row is integer-valued. In particular this
applies to the final degree-twelve row once its degree uniqueness is proved. -/
theorem principalBlock_integer_of_unique_degree
    (b : PrincipalCongruenceBlockData G) (j : {i // i ∈ b.block})
    (hunique : ∀ k, ambientRowDegree b k = ambientRowDegree b j → k = j) :
    ∀ g : G, ∃ n : ℤ, b.chi j.val (ConjClasses.mk g) = (n : ℂ) :=
  principalBlock_integer_of_unique_degree_of_actions b (principalBlock_actions b) j hunique

/-- Rational-valued form of the unique-degree conclusion. -/
theorem principalBlock_rational_of_unique_degree
    (b : PrincipalCongruenceBlockData G) (j : {i // i ∈ b.block})
    (hunique : ∀ k, ambientRowDegree b k = ambientRowDegree b j → k = j) :
    ∀ g : G, ∃ q : ℚ, b.chi j.val (ConjClasses.mk g) = (q : ℂ) := by
  intro g
  obtain ⟨n, hn⟩ := principalBlock_integer_of_unique_degree b j hunique g
  exact ⟨(n : ℚ), by simpa using hn⟩

end Stellmacher.Recognition.LyonsU3Four
