module

public import Theory.Character.ModularBlock.CyclicSevenIntegralData
public import Theory.Character.CyclicSevenExceptional
public import Theory.Character.CyclicSevenRestrictionFourier

/-!
# Integral restrictions of the three exceptional characters

Embed the ambient exceptional rows in the supplied complete character family.
Frobenius reciprocity and orthogonality say that their nonprincipal restriction
multiplicities differ by the signed Kronecker delta; other rows have equal
multiplicities. Fourier inversion gives integer shifts and integer constant
restrictions. The exceptional difference formula makes the three shifts equal.
This constructs `IntegralValues` without any block-membership or column assumptions.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.ModularBlock.CyclicThirteenIntegralRestrictions`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction CyclicSevenNormalizer
variable {G : Type*} [Group G] [Finite G]

private theorem sp_sub_right {A : Type*} [Fintype A] (f g h : A → ℂ) :
    scalarProduct A f (g - h) = scalarProduct A f g - scalarProduct A f h := by
  simp only [scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib]

private theorem coefficient_difference (d : PrimeCongruenceBlockData 7 G)
    {P : Subgroup G} {s : Rows P} (t : AmbientRows s)
    (e : Fin 3 ↪ d.I) (he : ∀ k, d.chi (e k) = t.chi k)
    (j : d.I) (k l : Fin 3) :
    scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G))) (s.linear k) -
      scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G))) (s.linear l) =
      t.sign * ((if j = e k then 1 else 0) - (if j = e l then 1 else 0)) := by
  let f := ofConjClassFunction (d.chi j)
  have hf := ofConjClassFunction_isClassFunction (d.chi j)
  change scalarProduct P (fun u => f u) (s.linear k) -
    scalarProduct P (fun u => f u) (s.linear l) = _
  rw [s.coefficient_induction f hf, s.coefficient_induction f hf, ← sp_sub_right]
  have hi : inducedClassFunction (Normalizer P) (s.localClass k) -
      inducedClassFunction (Normalizer P) (s.localClass l) =
      inducedClassFunction (Normalizer P) (s.localClass k - s.localClass l) :=
    (map_sub (inducedClassFunctionIntLinear (Normalizer P)) _ _).symm
  rw [hi, t.difference, scalarProduct_smul_right, sp_sub_right, ← he k, ← he l]
  change (scalarProduct G (ofConjClassFunction (d.chi j)) (ofConjClassFunction (d.chi (e k))) -
    scalarProduct G (ofConjClassFunction (d.chi j)) (ofConjClassFunction (d.chi (e l)))) *
    star t.sign = _
  rw [scalarProduct_ofConjClassFunction, scalarProduct_ofConjClassFunction,
    completeFamily_orthonormal d.complete, completeFamily_orthonormal d.complete]
  have hs : star t.sign = t.sign := by
    rcases t.sign_unit with h | h <;> simp [h]
  rw [hs, mul_comm]

private theorem coefficient_nat (d : PrimeCongruenceBlockData 7 G)
    (P : Subgroup G) (j : d.I) (ψ : P →* ℂ) :
    ∃ n : ℕ, scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G))) ψ = (n : ℂ) := by
  obtain ⟨n, ρ, hρ⟩ := (d.complete.1 j).1
  have hc : IsCharacter (ofConjClassFunction (d.chi j)) := by
    refine ⟨n, ρ, ?_⟩
    rw [hρ]
    rfl
  obtain ⟨m, σ, _, hσ⟩ := ψ.isLinearCharacter.1
  obtain ⟨a, ha⟩ := (isCharacter_comp_hom P.subtype hc).scalarProduct_nat ⟨m, σ, hσ⟩
  refine ⟨a, ?_⟩
  convert ha using 1
  congr 1
  exact Subsingleton.elim _ _

/-- The ambient exceptional rows have integral shifts and all other rows have
integral constant values on the punctured subgroup. -/
theorem nonempty_integralValues (d : PrimeCongruenceBlockData 7 G)
    (P : Sylow 7 G) (hP : Nat.card P = 7)
    (s : PeriodRows (P : Subgroup G)) : Nonempty (IntegralValues d P s) := by
  classical
  obtain ⟨t⟩ := s.toRows.nonempty_ambientRows hP
  obtain ⟨e, he⟩ := t.exists_embedding d.complete
  obtain ⟨ε, hε, hεt⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (ε : ℂ) = t.sign := by
    rcases t.sign_unit with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h.symm⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h.symm⟩
  choose n hn using coefficient_nat d (P : Subgroup G)
  let q (j : d.I) : ℤ := (n j (s.linear 0) : ℤ) - ε * (if j = e 0 then 1 else 0)
  let c (j : d.I) : ℤ := (n j 1 : ℤ) - q j
  have hcoeff (j : d.I) (k : Fin 3) :
      scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G))) (s.linear k) =
        (q j : ℂ) + (ε : ℂ) * (if j = e k then 1 else 0) := by
    have hh := coefficient_difference d t e he j k 0
    rw [← hεt, hn j (s.linear 0)] at hh
    have hq : (q j : ℂ) = (n j (s.linear 0) : ℂ) -
        (ε : ℂ) * (if j = e 0 then 1 else 0) := by
      simp [q]
    rw [hq]
    linear_combination hh
  have hv (j : d.I) (u : P) (hu : u ≠ 1) :
      d.chi j (ConjClasses.mk (u : G)) = (c j : ℂ) +
        (ε : ℂ) * ∑ k : Fin 3, (if j = e k then 1 else 0) *
          s.chi k (ConjClasses.mk (inclusion (P : Subgroup G) u)) := by
    have hf := s.toRows.fourier_restriction hP (ofConjClassFunction (d.chi j))
      (ofConjClassFunction_isClassFunction (d.chi j)) u
    change d.chi j (ConjClasses.mk (u : G)) = _ at hf
    have hprincipal : scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G))) 1 =
        (n j 1 : ℂ) := by
      convert hn j 1 using 1
      congr 1
    change d.chi j (ConjClasses.mk (u : G)) =
      scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G))) 1 +
      ∑ k : Fin 3, scalarProduct P (fun u => d.chi j (ConjClasses.mk (u : G)))
        (s.linear k) * s.chi k (ConjClasses.mk (inclusion (P : Subgroup G) u)) at hf
    rw [hprincipal] at hf
    simp_rw [hcoeff, add_mul] at hf
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, s.toRows.sum_restriction hP u hu] at hf
    simp only [mul_assoc, ← Finset.mul_sum] at hf
    simpa [c, sub_eq_add_neg, add_assoc] using hf
  have hvex (k : Fin 3) (u : P) (hu : u ≠ 1) :
      d.chi (e k) (ConjClasses.mk (u : G)) = (c (e k) : ℂ) +
        (ε : ℂ) * s.chi k (ConjClasses.mk (inclusion (P : Subgroup G) u)) := by
    simpa only [e.injective.eq_iff, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] using hv (e k) u hu
  have hc (k : Fin 3) : c (e k) = c (e 0) := by
    have hh := t.restriction_difference hP k 0 s.generator s.generator_ne_one
    rw [← he k, ← he 0, ← hεt, hvex k _ s.generator_ne_one,
      hvex 0 _ s.generator_ne_one] at hh
    have hc' : (c (e k) : ℂ) = (c (e 0) : ℂ) := by
      rcases hε with h | h
      · rw [h] at hh
        push_cast at hh
        linear_combination hh
      · rw [h] at hh
        push_cast at hh
        linear_combination -hh
    exact_mod_cast hc'
  refine ⟨{
    exceptionalRows := e
    commonDegree := t.commonDegree
    degree_pos := t.degree_pos
    degree := fun k => by rw [he k]; exact t.degree k
    sign := ε
    sign_unit := hε
    shift := c (e 0)
    exceptional_value := ?_
    remainder := fun j => c j.val
    remainder_value := ?_ }⟩
  · intro k u hu
    rw [hvex k u hu, hc k]
  · intro j u hu
    have hne (k : Fin 3) : j.val ≠ e k := fun h => j.property ⟨k, h.symm⟩
    simpa [hne] using hv j.val u hu

end ModularBlock.CyclicSeven
