module

public import Theory.Character.ModularBlock.TwoElementRestriction
public import Theory.Character.ModularBlock.TwistedBrauerExpansion
public import Theory.Character.ModularBlock.SmallQuotientBrauerNorm
public import Theory.Character.TwoSectionMass
public import Theory.Character.Transport

/-!
# Actual local contributions from genuine Brauer expansions

An ambient principal-block character agrees with its compatible local
principal projection on each two-section. Central translation of its ordinary
restriction therefore expands in the supplied genuine Brauer family. At an
element whose fourth power is one, integer character values and real Brauer
values give integral generalized decomposition coefficients.

The actual section mass is the normalized odd-element norm of that expansion.
The small quotient computations consequently give the singleton value-square
formula and the two-character quadratic form for an odd-normal quotient that
is a central order-four extension of S₄. No global section budget is used.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
printed pp. 73–74; the compatible projection is the associated-block support
argument of Alperin--Brauer--Gorenstein III.5–6.
-/

public section

noncomputable section
open scoped BigOperators
open ModularBlock PrincipalBlockConstruction ModularBlock.Cartan
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.TwoSectionContribution
variable {G : Type*} [Group G] [Finite G]

private def base (y : G) : Subgroup.centralizer ({y} : Set G) :=
  ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y)⟩

omit [Finite G] in
private theorem base_central (y : G) :
    base y ∈ Subgroup.center (Subgroup.centralizer ({y} : Set G)) := by
  apply Subgroup.mem_center_iff.mpr
  intro v
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp v.property)

private theorem projection (d : PrincipalCongruenceBlockData G)
    (χ : ClassFunction G) (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (y : G) (hy : ∃ k, y ^ (2 ^ k) = 1)
    (v : Subgroup.centralizer ({y} : Set G)) (hv : Odd (orderOf v)) :
    let C := Subgroup.centralizer ({y} : Set G)
    let l := CompatibleBrauerBlock.localData d C
    χ (y * (v : G)) = ∑ i ∈ l.block,
      scalarProduct C (fun g => χ (g : G)) (fun g => l.chi i (ConjClasses.mk g)) *
        l.chi i (ConjClasses.mk (base y * v)) := by
  obtain ⟨i, hi, hχ⟩ := hm
  simpa only [hχ, base] using
    TwoElementRestriction.principal_restriction_on_twoElement_section d y hy i hi v hv

/-- Genuine Brauer expansion on a two-section of an ambient principal row. -/
theorem exists_complex (d : PrincipalCongruenceBlockData G)
    (χ : ClassFunction G) (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (y : G) (hy : ∃ k, y ^ (2 ^ k) = 1) {m : ℕ}
    (a : PrincipalDecompositionData
      (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({y} : Set G))) m) :
    ∃ c : Fin m → ℂ,
      (∀ v : Subgroup.centralizer ({y} : Set G), Odd (orderOf v) →
        χ (y * (v : G)) = ∑ j, c j * BrauerCharacter.value
          (CompatibleBrauerBlock.localData d _) (a.family.rep j) v) ∧
      χ y = ∑ j, c j * (a.family.degree j : ℂ) := by
  exact TwistedBrauerExpansion.exists_complex _ a (fun g => χ (g : G))
    (base y) (base_central y) (projection d χ hm y hy)

/-- Integral generalized decomposition coefficients at a fourth root of one. -/
theorem exists_int (d : PrincipalCongruenceBlockData G)
    (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ k : ℤ, χ g = (k : ℂ))
    (y : G) (hy : y ^ 4 = 1) {m : ℕ}
    (a : PrincipalDecompositionData
      (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({y} : Set G))) m)
    (hreal : ∀ j v, Odd (orderOf v) →
      (BrauerCharacter.value (CompatibleBrauerBlock.localData d _) (a.family.rep j) v).im = 0) :
    ∃ c : Fin m → ℤ,
      (∀ v : Subgroup.centralizer ({y} : Set G), Odd (orderOf v) →
        χ (y * (v : G)) = ∑ j, (c j : ℂ) * BrauerCharacter.value
          (CompatibleBrauerBlock.localData d _) (a.family.rep j) v) ∧
      χ y = ∑ j, (c j : ℂ) * (a.family.degree j : ℂ) := by
  apply TwistedBrauerExpansion.exists_int _ a (fun g => χ (g : G))
    (isCharacter_comp_hom (Subgroup.centralizer ({y} : Set G)).subtype hχ) (base y) (base_central y)
  · exact Subtype.ext hy
  · exact fun g => hint (g : G)
  · exact fun j v hv => Complex.conj_eq_iff_im.mpr (hreal j v hv)
  · exact projection d χ hm y ⟨2, hy⟩

/-- A supplied expansion computes the actual local sum. -/
theorem mass_eq_normalizedOddNorm (χ : ClassFunction G) (y : G)
    (f : Subgroup.centralizer ({y} : Set G) → ℂ)
    (hf : ∀ v : Subgroup.centralizer ({y} : Set G), Odd (orderOf v) → χ (y * (v : G)) = f v) :
    Theory.Character.twoSectionMass χ y = normalizedOddNorm f := by
  apply OddElementSum.normalized_congr
  intro v hv
  rw [hf v hv]

/-- Singleton local principal families give the value-square divided by the
order of the odd-normal quotient. -/
theorem mass_of_oddNormal_twoGroup (d : PrincipalCongruenceBlockData G)
    (χ : ClassFunction G) (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (y : G) (hy : ∃ k, y ^ (2 ^ k) = 1)
    (a : PrincipalDecompositionData
      (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({y} : Set G))) 1)
    (N : Subgroup (Subgroup.centralizer ({y} : Set G))) [N.Normal]
    (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 (_ ⧸ N))
    (hd : a.family.degree 0 = 1) (b : ℤ) (hb : χ y = (b : ℂ)) :
    Theory.Character.twoSectionMass χ y = (b : ℝ) ^ 2 / (Nat.card (_ ⧸ N) : ℝ) := by
  obtain ⟨c, hc, he⟩ := exists_complex d χ hm y hy a
  have hc0 : c 0 = (b : ℂ) := by simpa [hd, hb] using he.symm
  rw [mass_eq_normalizedOddNorm χ y
    (fun v => (b : ℂ) * BrauerCharacter.value _ (a.family.rep 0) v)
    (fun v hv => by simpa [hc0] using hc v hv)]
  exact normalizedOddNorm_of_oddNormal_twoGroup _ a.family N hN hQ hd b

/-- The central-four symmetric-four local model gives genuine integral
coefficients and the actual quadratic contribution. -/
theorem contribution_of_oddNormal_centralFour_symmetricFour
    (d : PrincipalCongruenceBlockData G) (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ k : ℤ, χ g = (k : ℂ)) (y : G) (hy : y ^ 4 = 1)
    (a : PrincipalDecompositionData
      (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({y} : Set G))) 2)
    (N : Subgroup (Subgroup.centralizer ({y} : Set G))) [N.Normal]
    (hN : Odd (Nat.card N))
    (Z : Subgroup (_ ⧸ N)) [Z.Normal]
    (hc : Z ≤ Subgroup.center (_ ⧸ N)) (hcard : Nat.card Z = 4)
    (e : ((_ ⧸ N) ⧸ Z) ≃* Equiv.Perm (Fin 4))
    (hd0 : a.family.degree 0 = 1) (hd1 : a.family.degree 1 = 2) :
    ∃ u w : ℤ,
      (∀ v : Subgroup.centralizer ({y} : Set G), Odd (orderOf v) →
        χ (y * (v : G)) =
          (u : ℂ) * BrauerCharacter.value (CompatibleBrauerBlock.localData d _) (a.family.rep 0) v +
          (w : ℂ) * BrauerCharacter.value (CompatibleBrauerBlock.localData d _) (a.family.rep 1) v) ∧
      χ y = ((u + 2 * w : ℤ) : ℂ) ∧
      32 * Theory.Character.twoSectionMass χ y = ((2 * u ^ 2 + (u - 2 * w) ^ 2 : ℤ) : ℝ) := by
  obtain ⟨c, hexp, he⟩ := exists_int d χ hχ hm hint y hy a
    (brauerValues_real_of_oddNormal_centralFour_symmetricFour _ a.family
      N hN Z hc hcard e hd0 hd1)
  have hexp' := fun v hv => (by simpa [Fin.sum_univ_two] using hexp v hv)
  refine ⟨c 0, c 1, hexp', ?_, ?_⟩
  · simpa [Fin.sum_univ_two, hd0, hd1, mul_comm] using he
  · rw [mass_eq_normalizedOddNorm χ y _ hexp']
    exact normalizedOddNorm_of_oddNormal_centralFour_symmetricFour _ a.family
      N hN Z hc hcard e hd0 hd1 (c 0) (c 1)
end ModularBlock.TwoSectionContribution
