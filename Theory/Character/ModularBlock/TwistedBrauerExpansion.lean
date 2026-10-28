module

public import Theory.Character.ModularBlock.Cartan
public import Theory.Character.CentralTwist
public import Theory.Character.ScalarProductMultiplicity

/-!
# Twisted expansions in genuine principal-block Brauer characters

An explicit local projection identity isolates the principal ordinary block.
Central translation multiplies each ordinary irreducible by its central scalar;
its genuine decomposition row then gives the desired Brauer expansion.
Evaluation at one gives the degree-weighted coefficient sum. Independence of
the supplied Brauer family makes the expansion unique.

If the central element has fourth power one, its scalars are fourth roots of
unity and their real parts are integers. Ordinary character multiplicities and
decomposition numbers are integers as well. Taking real parts of the expansion
therefore gives integral coefficients when both the translated character and
the Brauer values are real. Uniqueness identifies these with the original
complex coefficients. This avoids any assumption about global section support;
the projection identity is an explicit input.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
pp. 73–74, and the standard central-element generalized decomposition argument.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

namespace ModularBlock.TwistedBrauerExpansion
open PrincipalBlockConstruction
variable {G : Type*} [Group G] [Finite G]
  (d : PrincipalCongruenceBlockData G) {m : ℕ} (a : Cartan.PrincipalDecompositionData d m)

private theorem re_int_of_fourth_root {c : ℂ} (hc : c ^ 4 = 1) : ∃ k : ℤ, c.re = (k : ℝ) := by
  have hs : (c ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hc
  rcases sq_eq_one_iff.mp hs with hs | hs
  · rcases sq_eq_one_iff.mp hs with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  · have hprod : (c - Complex.I) * (c + Complex.I) = 0 := by
      calc
        _ = c ^ 2 + 1 := by ring_nf; simp [add_comm]
        _ = 0 := by rw [hs]; ring
    rcases mul_eq_zero.mp hprod with h | h
    · have : c = Complex.I := sub_eq_zero.mp h
      exact ⟨0, by simp [this]⟩
    · have : c = -Complex.I := eq_neg_of_add_eq_zero_left h
      exact ⟨0, by simp [this]⟩

private theorem exists_scalars (z : G) (hz : z ∈ Subgroup.center G) :
    ∃ scalar : d.I → ℂ,
      (∀ i v, d.chi i (ConjClasses.mk (z * v)) = scalar i * d.chi i (ConjClasses.mk v)) ∧
      (∀ i n, z ^ n = 1 → scalar i ^ n = 1) := by
  have h (i : d.I) : ∃ c : ℂ,
      (∀ v, d.chi i (ConjClasses.mk (z * v)) = c * d.chi i (ConjClasses.mk v)) ∧
      (∀ n, z ^ n = 1 → c ^ n = 1) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    have hirr : Representation.IsIrreducible ρ := by
      apply (irreducible_iff_character_norm_one (ρ := ρ)).2
      simpa [← hρ] using (d.complete.1 i).2
    simpa only [hρ, characterClassFunction, conjClassFunctionOfInvariant, ConjClasses.mk, Quotient.lift_mk] using IsIrreducibleCharacter.exists_central_scalar (⟨n, ρ, hirr, rfl⟩ :
      IsIrreducibleCharacter ρ.character) hz
  choose scalar hscalar hp using h
  exact ⟨scalar, hscalar, hp⟩

private theorem expansion (θ : ClassFunction G) (z : G) (scalar : d.I → ℂ)
    (hscalar : ∀ i v, d.chi i (ConjClasses.mk (z * v)) = scalar i * d.chi i (ConjClasses.mk v))
    (hp : ∀ v : G, Odd (orderOf v) → θ (z * v) =
      ∑ i ∈ d.block, scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk (z * v)))
    (v : G) (hv : Odd (orderOf v)) :
    θ (z * v) = ∑ j, (∑ i ∈ d.block,
      scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) * scalar i *
        (a.decomposition i j : ℂ)) * BrauerCharacter.value d (a.family.rep j) v := by
  rw [hp v hv]
  calc
    _ = ∑ i ∈ d.block, ∑ j,
        (scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) * scalar i *
          (a.decomposition i j : ℂ)) * BrauerCharacter.value d (a.family.rep j) v := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hscalar, a.restriction i hi v hv, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]

/-- The local projection identity gives actual coefficients in the prescribed
Brauer family for the central translate, including its value at the identity.
No character hypothesis on `θ` is needed for this complex expansion. -/
theorem exists_complex (θ : ClassFunction G) (z : G) (hz : z ∈ Subgroup.center G)
    (hp : ∀ v : G, Odd (orderOf v) → θ (z * v) =
      ∑ i ∈ d.block, scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk (z * v))) :
    ∃ c : Fin m → ℂ,
      (∀ v : G, Odd (orderOf v) → θ (z * v) =
        ∑ j, c j * BrauerCharacter.value d (a.family.rep j) v) ∧
      θ z = ∑ j, c j * (a.family.degree j : ℂ) := by
  obtain ⟨scalar, hscalar, _⟩ := exists_scalars d z hz
  refine ⟨_, expansion d a θ z scalar hscalar hp, ?_⟩
  simpa using expansion d a θ z scalar hscalar hp 1 (by simp)

/-- Equality on odd-order elements determines the coefficients in the supplied
genuine Brauer family uniquely. -/
theorem coefficients_unique (c b : Fin m → ℂ)
    (h : ∀ v : G, Odd (orderOf v) →
      (∑ j, c j * BrauerCharacter.value d (a.family.rep j) v) =
        ∑ j, b j * BrauerCharacter.value d (a.family.rep j) v) : c = b := by
  have hsum :
      ∑ j, c j • BrauerCharacter.character d (a.family.rep j) =
        ∑ j, b j • BrauerCharacter.character d (a.family.rep j) := by
    funext cls
    obtain ⟨g, hg, hc⟩ := cls.property
    have heq : cls = BrauerCharacter.twoRegularClass g hg := Subtype.ext hc.symm
    subst cls
    simpa using h g hg
  exact funext (Fintype.linearIndependent_iffₛ.mp a.family.independent c b hsum)

/-- For a central element whose fourth power is one, an integer-valued ordinary
character has integral twisted coefficients whenever the supplied Brauer values
are real. These are expansion coefficients in the actual Brauer family. -/
theorem exists_int (θ : ClassFunction G) (hθ : IsCharacter θ)
    (z : G) (hz : z ∈ Subgroup.center G) (hz4 : z ^ 4 = 1)
    (hθint : ∀ g, ∃ k : ℤ, θ g = (k : ℂ))
    (hreal : ∀ j v, Odd (orderOf v) →
      star (BrauerCharacter.value d (a.family.rep j) v) =
        BrauerCharacter.value d (a.family.rep j) v)
    (hp : ∀ v : G, Odd (orderOf v) → θ (z * v) =
      ∑ i ∈ d.block, scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk (z * v))) :
    ∃ c : Fin m → ℤ,
      (∀ v : G, Odd (orderOf v) → θ (z * v) =
        ∑ j, (c j : ℂ) * BrauerCharacter.value d (a.family.rep j) v) ∧
      θ z = ∑ j, (c j : ℂ) * (a.family.degree j : ℂ) := by
  obtain ⟨scalar, hscalar, hpow⟩ := exists_scalars d z hz
  have hmult (i : d.I) : ∃ n : ℕ,
      scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) = (n : ℂ) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    apply hθ.scalarProduct_nat
    exact ⟨n, ρ, by funext g; rw [hρ]; rfl⟩
  choose mult hmult using hmult
  choose k hk using fun i => re_int_of_fourth_root (hpow i 4 hz4)
  let c : Fin m → ℂ := fun j => ∑ i ∈ d.block,
    scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) * scalar i *
      (a.decomposition i j : ℂ)
  let b : Fin m → ℤ := fun j => ∑ i ∈ d.block,
    (mult i : ℤ) * k i * (a.decomposition i j : ℤ)
  have hcb (j : Fin m) : (c j).re = (b j : ℝ) := by
    simp [c, b, Complex.re_sum, Complex.mul_re, hmult, hk]
  have heval (v : G) (hv : Odd (orderOf v)) :
      θ (z * v) = ∑ j, (b j : ℂ) * BrauerCharacter.value d (a.family.rep j) v := by
    have he := expansion d a θ z scalar hscalar hp v hv
    change θ (z * v) = ∑ j, c j * BrauerCharacter.value d (a.family.rep j) v at he
    have he' := congrArg (fun x : ℂ => (x.re : ℂ)) he
    obtain ⟨t, ht⟩ := hθint (z * v)
    have hvim (j : Fin m) : (BrauerCharacter.value d (a.family.rep j) v).im = 0 :=
      Complex.conj_eq_iff_im.mp (hreal j v hv)
    have hvre (j : Fin m) :
        ((BrauerCharacter.value d (a.family.rep j) v).re : ℂ) =
          BrauerCharacter.value d (a.family.rep j) v :=
      Complex.conj_eq_iff_re.mp (hreal j v hv)
    simpa only [ht, Complex.intCast_re, Complex.ofReal_intCast, Complex.re_sum,
      Complex.mul_re, hvim, mul_zero, sub_zero, hcb, Complex.ofReal_sum,
      Complex.ofReal_mul, hvre] using he'
  exact ⟨b, heval, by simpa using heval 1 (by simp)⟩

end ModularBlock.TwistedBrauerExpansion
