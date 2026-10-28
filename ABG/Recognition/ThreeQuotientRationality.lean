module

public import ABG.Recognition.ThreeQuotientRelations
public import Theory.Character.GaloisScalarProduct
public import Theory.Character.UniqueDegreeRationality

/-!
# Rational rows in the odd-core quotient induced catalog

The first, fourth, and fifth supported generators have integer values on
GL₂(3), so every field automorphism fixes their inflations and inductions.
The scalar products with these three functions distinguish Wong's rows
0, 1, 4, 5, and 6 from every other nonprincipal irreducible. Galois transport
therefore fixes those rows. Algebraic integrality makes their values integers,
and in particular the first five ABG principal candidates are rational-valued.
This argument does not require ambient principal-block membership or the
vanishing of the centralizer's odd core.

Source: ABG III.2 Corollary 2; Wong (1964), Table 1 and equation (3).
-/

namespace ABG
open BenderGlauberman Matrix Matrix.GeneralLinearGroup
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

omit [Group G] [Finite G] in
/-- The three rational supported generators are fixed by all field automorphisms. -/
public theorem glTwoThreeSupportedGenerator_ringEquiv
    (σ : ℂ ≃+* ℂ) (k : Fin 5) (hk : k = 0 ∨ k = 3 ∨ k = 4)
    (g : GL (Fin 2) (ZMod 3)) :
    σ (glTwoThreeSupportedGenerator k g) = glTwoThreeSupportedGenerator k g := by
  rw [three_classFunction_apply _ (isClassFunction_of_isGeneralizedCharacter
    (glTwoThreeSupportedGenerator_generalized k)) g, glTwoThreeSupportedGenerator_values]
  fin_cases k <;> norm_num [Fin.ext_iff] at hk
  all_goals generalize threeClassIndex g = j
  all_goals fin_cases j <;> norm_num [Matrix.cons_val, Fin.reduceFinMk, map_ofNat, map_neg]

private theorem irr_product {a b : ClassFunction G}
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b) :
    scalarProduct G a b = if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b; simp [irreducible_scalarProduct_self ha]
  · rw [if_neg h]; exact irreducible_scalarProduct_of_ne ha hb h

private theorem distinguish {Ψ : Fin 5 → ClassFunction G}
    (d : ThreeCharacterDecomposition Ψ) {θ : ClassFunction G}
    (hθ : IsIrreducibleCharacter θ) (hn : θ ≠ 1) (j : Fin 7)
    (hj : j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6)
    (h0 : scalarProduct G (Ψ 0) θ = scalarProduct G (Ψ 0) (d.χ j))
    (h3 : scalarProduct G (Ψ 3) θ = scalarProduct G (Ψ 3) (d.χ j))
    (h4 : scalarProduct G (Ψ 4) θ = scalarProduct G (Ψ 4) (d.χ j)) : θ = d.χ j := by
  classical
  have ho (k l : Fin 7) : scalarProduct G (d.χ k) (d.χ l) = if k = l then 1 else 0 := by
    rw [irr_product (d.irreducible k) (d.irreducible l)]
    simp only [d.distinct.eq_iff]
  have ht : scalarProduct G 1 θ = 0 :=
    irreducible_scalarProduct_of_ne isLinearCharacter_one.1 hθ (Ne.symm hn)
  have hp (k : Fin 7) : scalarProduct G 1 (d.χ k) = 0 :=
    irreducible_scalarProduct_of_ne isLinearCharacter_one.1 (d.irreducible k)
      (Ne.symm (d.nontrivial k))
  simp only [d.first, d.fourth, d.fifth, scalarProduct_add_left,
    _root_.scalarProduct_sub_left, scalarProduct_smul_left, ho, ht, hp,
    irr_product (d.irreducible _) hθ] at h0 h3 h4
  by_cases he0 : d.χ 0 = θ
  · subst θ
    simp only [d.distinct.eq_iff] at h0 h3 h4
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rfl
    all_goals rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
  by_cases he1 : d.χ 1 = θ
  · subst θ
    simp only [d.distinct.eq_iff] at h0 h3 h4
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rfl
    all_goals rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
  by_cases he4 : d.χ 4 = θ
  · subst θ
    simp only [d.distinct.eq_iff] at h0 h3 h4
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rfl
    · rcases d.sign_unit 1 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h4
    · rcases d.sign_unit 1 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h3
  by_cases he5 : d.χ 5 = θ
  · subst θ
    simp only [d.distinct.eq_iff] at h0 h3 h4
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rcases d.sign_unit 1 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h4
    · rfl
    · rcases d.sign_unit 2 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h3
  by_cases he6 : d.χ 6 = θ
  · subst θ
    simp only [d.distinct.eq_iff] at h0 h3 h4
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
    · rcases d.sign_unit 1 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h3
    · rcases d.sign_unit 2 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h3
    · rfl
  simp only [if_neg he0, if_neg he1, if_neg he4, if_neg he5, if_neg he6] at h0 h3 h4
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
  · rcases d.sign_unit 0 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h0
  · rcases d.sign_unit 1 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h3
  · rcases d.sign_unit 2 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h3
  · rcases d.sign_unit 3 with hs | hs <;> norm_num [hs, Fin.ext_iff] at h4

private theorem catalog_fixed {Ψ : Fin 5 → ClassFunction G}
    (d : ThreeCharacterDecomposition Ψ)
    (hgen : ∀ k, IsGeneralizedCharacter (Ψ k))
    (hfixed : ∀ (σ : ℂ ≃+* ℂ) (k : Fin 5), k = 0 ∨ k = 3 ∨ k = 4 →
      ∀ g, σ (Ψ k g) = Ψ k g)
    (j : Fin 7) (hj : j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6)
    (σ : ℂ ≃+* ℂ) (g : G) : σ (d.χ j g) = d.χ j g := by
  have hc (k : Fin 5) (hk : k = 0 ∨ k = 3 ∨ k = 4) :
      scalarProduct G (Ψ k) (fun a => σ (d.χ j a)) = scalarProduct G (Ψ k) (d.χ j) := by
    have hf : (fun a => σ (Ψ k a)) = Ψ k := funext (hfixed σ k hk)
    have he := (d.irreducible j).scalarProduct_comp_ringEquiv σ (Ψ k)
    rw [hf] at he
    obtain ⟨n, hn⟩ := multiplicity_int (d.irreducible j) (Ψ k) (hgen k)
    have hn' : scalarProduct G (Ψ k) (d.χ j) = (n : ℂ) := by
      rw [← scalarProduct_conj, hn, star_intCast]
    rw [he, hn', map_intCast]
  have hne : (fun a => σ (d.χ j a)) ≠ 1 := by
    intro h
    apply d.nontrivial j
    funext a
    apply σ.injective
    simpa using congrFun h a
  exact congrFun (distinguish d ((d.irreducible j).comp_ringEquiv σ) hne j hj
    (hc 0 (Or.inl rfl)) (hc 3 (Or.inr (Or.inl rfl)))
    (hc 4 (Or.inr (Or.inr rfl)))) g

variable (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)

/-- The same three ambient induced functions are Galois-fixed, even above an odd core. -/
public theorem threeQuotientInducedGenerator_ringEquiv
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (σ : ℂ ≃+* ℂ) (k : Fin 5) (hk : k = 0 ∨ k = 3 ∨ k = 4) (g : G) :
    σ (threeQuotientInducedGenerator x e k g) = threeQuotientInducedGenerator x e k g := by
  rw [threeQuotientInducedGenerator, ringEquiv_inducedClassFunction]
  have hf : (fun a => σ (threeQuotientGenerator x e k a)) = threeQuotientGenerator x e k := by
    funext a
    exact glTwoThreeSupportedGenerator_ringEquiv σ k hk _
  rw [hf]

/-- Five nonprincipal rows in Wong's catalog are integer-valued. -/
public theorem threeQuotientCharacter_integer
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (j : Fin 7) (hj : j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6)
    (g : G) : ∃ n : ℤ, d.χ j g = (n : ℂ) :=
  (d.irreducible j).integer_of_fixed
    (catalog_fixed d (threeQuotientInducedGenerator_generalized x e)
      (threeQuotientInducedGenerator_ringEquiv x e) j hj) g

/-- Rationality of exactly the first five rows requested by the principal-section interface. -/
public theorem threeQuotient_principalCandidate_rational
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (i : Fin 5) (g : G) : ∃ q : ℚ, d.principalCandidate ⟨i.val, by omega⟩ g = (q : ℂ) := by
  have hint (j : Fin 7) (hj : j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6) :
      ∃ n : ℤ, d.χ j g = (n : ℂ) :=
    threeQuotientCharacter_integer x e d j hj g
  fin_cases i
  · exact ⟨1, by simp [ThreeCharacterDecomposition.principalCandidate]⟩
  all_goals
    simp only [ThreeCharacterDecomposition.principalCandidate, Matrix.cons_val, Fin.reduceFinMk]
  · obtain ⟨n, hn⟩ := hint 1 (by decide)
    exact ⟨(n : ℚ), by simpa using hn⟩
  · obtain ⟨n, hn⟩ := hint 6 (by decide)
    exact ⟨(n : ℚ), by simpa using hn⟩
  · obtain ⟨n, hn⟩ := hint 4 (by decide)
    exact ⟨(n : ℚ), by simpa using hn⟩
  · obtain ⟨n, hn⟩ := hint 5 (by decide)
    exact ⟨(n : ℚ), by simpa using hn⟩

/-- The rationality statement in the conjugacy-class convention of actual block data. -/
public theorem threeQuotient_principalConjCandidate_rational
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (i : Fin 5) (g : G) :
    ∃ q : ℚ, d.principalConjCandidate ⟨i.val, by omega⟩ (ConjClasses.mk g) = (q : ℂ) :=
  threeQuotient_principalCandidate_rational x e d i g

end
end ABG
