module

public import Theory.Character.CharacterValues
public import Theory.FieldTheory.CyclotomicGalois

/-!
# Galois action on character values

A cyclotomic automorphism acting by the exponent `e` on roots of unity sends
a character value at `g` to its value at `g ^ e`. The trace is a sum of
finite-order eigenvalues; integer linearity extends the formula to virtual
characters.

Extracted from Peterfalvi (1.9), for Suzuki VI §2.2, Example 3.
The historical `Section1` names are retained for compatibility.
-/

noncomputable section
open scoped Cyclotomic
namespace Section1

/--
The exponent form of the cyclotomic Galois action on a representation
character.  The automorphism corresponding to an exponent `e` sends the
character value at `g` to the value at `g ^ e`.
-/
@[expose] public noncomputable def characterGaloisConjugateByExponent
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (e : ℕ) : G → ℂ :=
  fun g => ρ.character (g ^ e)

@[expose] public noncomputable def characterGaloisConjugateByAutomorphism
    {G : Type*} (τ : Gal(ℂ/ℚ)) (χ : G → ℂ) : G → ℂ :=
  fun g => τ (χ g)

public theorem representation_character_apply_galois_eq_argumentPow
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {N e : ℕ} {τ : Gal(ℂ/ℚ)}
    (hτroot : ∀ z : ℂ, z ^ N = 1 → τ z = z ^ e)
    (ρ : Representation ℂ G V)
    (hdivGN : Nat.card G ∣ N) :
    ∀ g : G, τ (ρ.character g) = ρ.character (g ^ e) := by
  intro g
  let f : Module.End ℂ V := ρ g
  let n : ℕ := orderOf g
  have hn : n ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
  have hpow : f ^ n = 1 := by
    dsimp [f, n]
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have hdiv : n ∣ N := by
    exact dvd_trans (by simpa [n] using orderOf_dvd_natCard g) hdivGN
  calc
    τ (ρ.character g) = τ (LinearMap.trace ℂ V (f ^ 1)) := by
      simp [Representation.character, f]
    _ =
        τ (∑ μ : f.Eigenvalues,
          ((μ : ℂ) ^ 1 * Module.finrank ℂ (f.eigenspace (μ : ℂ)))) := by
        rw [Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow]
    _ =
        ∑ μ : f.Eigenvalues,
          τ (((μ : ℂ) ^ 1) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
        simp
    _ =
        ∑ μ : f.Eigenvalues,
          ((μ : ℂ) ^ e * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
        refine Finset.sum_congr rfl ?_
        intro μ _hμ
        have hμn : (μ : ℂ) ^ n = 1 :=
          Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
        have hμN : (μ : ℂ) ^ N = 1 := by
          rcases hdiv with ⟨m, rfl⟩
          rw [pow_mul, hμn, one_pow]
        simp [map_mul, hτroot (μ : ℂ) hμN]
    _ = LinearMap.trace ℂ V (f ^ e) := by
        symm
        rw [Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := e) hn hpow]
    _ = ρ.character (g ^ e) := by
      simp [Representation.character, f]

/--
The exponent form of the cyclotomic Galois action extends from representation
characters to virtual characters by integer linearity.
-/
public theorem virtualCharacter_apply_galois_eq_argumentPow
    {G : Type*} [Group G] [Finite G]
    {χ : G → ℂ} {N e : ℕ} {τ : Gal(ℂ/ℚ)}
    (hτroot : ∀ z : ℂ, z ^ N = 1 → τ z = z ^ e)
    (hχ : IsVirtualCharacter χ)
    (hdivGN : Nat.card G ∣ N) :
    ∀ g : G, τ (χ g) = χ (g ^ e) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  intro g
  rw [hχeq, virtualCharacterOfRepresentations]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hρg :=
    representation_character_apply_galois_eq_argumentPow
      (N := N) (e := e) (τ := τ) hτroot (ρ i) hdivGN g
  simp [map_mul, hρg]


end Section1
