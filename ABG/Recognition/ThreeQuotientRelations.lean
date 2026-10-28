module

public import ABG.Recognition.ThreeQuotientInduction

/-!
# Odd-order relations in the induced character catalog

The five functions induced from the odd-core quotient vanish on odd-order
elements. Consequently their single seven-character decomposition gives the
signed odd-order relations and equal degrees for the three exceptional rows.
We adjoin the principal character and reindex the actual irreducibles in the
order used by `ThreePrincipalData`: principal, χ₁, χ₂, χ₃, χ₄, χ⁽²⁾, χ⁽¹⁾, χ⁽⁻¹⁾.
This construction records distinctness and the odd relations before proving
membership in the ambient principal block or resolving the signs.

Source: Wong (1964), equation (3), p.98; ABG III.2 Proposition 4.
-/

namespace ABG
open BenderGlauberman
noncomputable section
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G] (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)

/-- An odd-order element cannot be conjugate to a cyclic root of an involution. -/
public theorem threeQuotientInducedGenerator_odd (hx : orderOf x = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5)
    (r : G) (hr : Odd (orderOf r)) : threeQuotientInducedGenerator x e k r = 0 := by
  apply threeQuotientInducedGenerator_eq_zero x hx e k
  intro g hg
  have hd := orderOf_dvd_of_mem_zpowers hg
  rw [hx] at hd
  have he : orderOf (g⁻¹ * r * g) = orderOf r := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective r
  exact hr.not_two_dvd_nat (he ▸ hd)

namespace ThreeCharacterDecomposition
variable {Ψ : Fin 5 → ClassFunction G} (d : ThreeCharacterDecomposition Ψ)

/-- Reindex Wong's actual characters in the ABG principal-block order. -/
@[expose] public def principalCandidate : Fin 8 → ClassFunction G :=
  ![1, d.χ 1, d.χ 6, d.χ 4, d.χ 5, d.χ 0, d.χ 2, d.χ 3]

/-- Every candidate is an actual irreducible, including the principal row. -/
public theorem principalCandidate_irreducible (i : Fin 8) :
    IsIrreducibleCharacter (d.principalCandidate i) := by
  fin_cases i
  · exact isLinearCharacter_one.1
  all_goals exact d.irreducible _

omit [Finite G] in
/-- The eight candidates are pairwise distinct. -/
public theorem principalCandidate_injective : Function.Injective d.principalCandidate := by
  intro i j hij
  have hn (k : Fin 7) := d.nontrivial k
  have hd (k l : Fin 7) (h : k ≠ l) : d.χ k ≠ d.χ l := fun he => h (d.distinct he)
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals simp only [principalCandidate, Matrix.cons_val, Fin.reduceFinMk] at hij
  all_goals first
    | exact (hn _ hij).elim
    | exact (hn _ hij.symm).elim
    | exact (hd _ _ (by decide) hij).elim

/-- The candidate family on conjugacy classes, as used by block data. -/
@[expose] public def principalConjCandidate (i : Fin 8) : ConjClassFunction G :=
  toConjClassFunction (d.principalCandidate i)
    (irreducibleCharacter_isClassFunction (d.principalCandidate_irreducible i))

public theorem principalConjCandidate_irreducible (i : Fin 8) :
    IsIrreducibleConjCharacter (d.principalConjCandidate i) :=
  isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19
    (d.principalCandidate_irreducible i)

public theorem principalConjCandidate_injective : Function.Injective d.principalConjCandidate := by
  intro i j hij
  apply d.principalCandidate_injective
  funext g
  exact congrFun hij (ConjClasses.mk g)

omit [Finite G] in
/-- Vanishing of the five induced functions gives the signed odd-order relations. -/
public theorem principalCandidate_relations_at (r : G) (hΨ : ∀ k, Ψ k r = 0) :
    (d.sign 0 : ℂ) * d.principalCandidate 1 r +
        (d.sign 3 : ℂ) * d.principalCandidate 2 r +
        (d.sign 1 : ℂ) * d.principalCandidate 3 r = 1 ∧
      (d.sign 2 : ℂ) * d.principalCandidate 4 r + 1 =
        (d.sign 3 : ℂ) * d.principalCandidate 2 r ∧
      ∀ j : Fin 3, d.principalCandidate ⟨j.val + 5, by omega⟩ r + (d.sign 0 : ℂ) =
        d.principalCandidate 1 r := by
  have h0 := congrFun d.first r
  have h1 := congrFun d.second r
  have h2 := congrFun d.third r
  have h3 := congrFun d.fourth r
  have h4 := congrFun d.fifth r
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, hΨ]
    at h0 h1 h2 h3 h4
  constructor
  · change (d.sign 0 : ℂ) * d.χ 1 r + (d.sign 3 : ℂ) * d.χ 6 r +
      (d.sign 1 : ℂ) * d.χ 4 r = 1
    linear_combination h0 - h4
  constructor
  · change (d.sign 2 : ℂ) * d.χ 5 r + 1 = (d.sign 3 : ℂ) * d.χ 6 r
    linear_combination h4 - h3 - h0
  · intro j
    fin_cases j
    · change d.χ 0 r + (d.sign 0 : ℂ) = d.χ 1 r
      rcases d.sign_unit 0 with hs | hs <;> simp only [hs, Int.cast_one, Int.cast_neg] at *
      · linear_combination -h0
      · linear_combination h0
    · change d.χ 2 r + (d.sign 0 : ℂ) = d.χ 1 r
      rcases d.sign_unit 0 with hs | hs <;> simp only [hs, Int.cast_one, Int.cast_neg] at *
      · linear_combination -h0 + h1
      · linear_combination h0 - h1
    · change d.χ 3 r + (d.sign 0 : ℂ) = d.χ 1 r
      rcases d.sign_unit 0 with hs | hs <;> simp only [hs, Int.cast_one, Int.cast_neg] at *
      · linear_combination -h0 + h1 + h2
      · linear_combination h0 - h1 - h2

end ThreeCharacterDecomposition

/-- The relations apply to the same quotient-induced catalog on every odd-order element. -/
public theorem threeQuotient_principalCandidate_odd_relations (hx : orderOf x = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (r : G) (hr : Odd (orderOf r)) :
    (d.sign 0 : ℂ) * d.principalCandidate 1 r +
        (d.sign 3 : ℂ) * d.principalCandidate 2 r +
        (d.sign 1 : ℂ) * d.principalCandidate 3 r = 1 ∧
      (d.sign 2 : ℂ) * d.principalCandidate 4 r + 1 =
        (d.sign 3 : ℂ) * d.principalCandidate 2 r ∧
      ∀ j : Fin 3, d.principalCandidate ⟨j.val + 5, by omega⟩ r + (d.sign 0 : ℂ) =
        d.principalCandidate 1 r :=
  d.principalCandidate_relations_at r (fun k => threeQuotientInducedGenerator_odd x hx e k r hr)

end
end ABG
