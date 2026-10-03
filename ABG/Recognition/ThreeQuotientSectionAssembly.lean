module

public import ABG.Recognition.ThreeQuotientPrincipalSections
public import Theory.Character.IrreducibleDegrees

/-!
# Assembly of the signed principal sections

The odd-core quotient construction already supplies actual ambient block rows,
their rationality, a compatible local character, and both section formulas.
Here the odd-order relations identify the three exceptional degrees and put
Wong's signs in ABG's convention. Block cardinality eight promotes the supplied
embedding to an equivalence; the two signed degree congruences then complete
`ThreePrincipalSectionData` without a degree-product assumption.

The cardinality and congruences are explicit inputs, so this module does not
assert their existence. Source: ABG III.2 Propositions 1--4 and 6, and III.6
Corollaries 3--6; Wong (1964), equation (3).
-/

namespace ABG
open BenderGlauberman ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace ThreeCharacterDecomposition
variable {G : Type*} [Group G] {Ψ : Fin 5 → ClassFunction G}

/-- The five actual degrees in the principal-section convention. -/
@[expose] public def principalSectionDegree (d : ThreeCharacterDecomposition Ψ) : Fin 5 → ℕ :=
  ![(d.irreducible 1).degree, (d.irreducible 6).degree,
    (d.irreducible 4).degree, (d.irreducible 5).degree, (d.irreducible 0).degree]

end ThreeCharacterDecomposition

variable {G : Type*} [Group G] [Finite G] (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)

/-- Evaluation at the identity gives the five natural degrees, with a common
degree for all three exceptional characters. -/
public theorem threeQuotient_principalCandidate_degree (hx : orderOf x = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e)) (i : Fin 8) :
    d.principalCandidate i 1 =
      ((![1, d.principalSectionDegree 0, d.principalSectionDegree 1,
        d.principalSectionDegree 2, d.principalSectionDegree 3,
        d.principalSectionDegree 4, d.principalSectionDegree 4,
        d.principalSectionDegree 4] i : ℕ) : ℂ) := by
  have he := (threeQuotient_principalCandidate_odd_relations x hx e d 1 (by simp)).2.2
  have he2 : d.χ 2 1 = d.χ 0 1 := by
    have h0 := he 0
    have h1 := he 1
    change d.χ 0 1 + (d.sign 0 : ℂ) = d.χ 1 1 at h0
    change d.χ 2 1 + (d.sign 0 : ℂ) = d.χ 1 1 at h1
    linear_combination h1 - h0
  have he3 : d.χ 3 1 = d.χ 0 1 := by
    have h0 := he 0
    have h2 := he 2
    change d.χ 0 1 + (d.sign 0 : ℂ) = d.χ 1 1 at h0
    change d.χ 3 1 + (d.sign 0 : ℂ) = d.χ 1 1 at h2
    linear_combination h2 - h0
  fin_cases i
  · simp [ThreeCharacterDecomposition.principalCandidate]
  · exact (d.irreducible 1).degree_eq
  · exact (d.irreducible 6).degree_eq
  · exact (d.irreducible 4).degree_eq
  · exact (d.irreducible 5).degree_eq
  · exact (d.irreducible 0).degree_eq
  · exact he2.trans (d.irreducible 0).degree_eq
  · exact he3.trans (d.irreducible 0).degree_eq

/-- The odd-order identities with the three unresolved ABG signs. -/
public theorem threeQuotient_principalCandidate_signed_odd_relations
    (hx : orderOf x = 2) (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (r : G) (hr : Odd (orderOf r)) :
    (1 + (-d.sign 0 : ℤ) * d.principalCandidate 1 r +
        (-d.sign 3 : ℤ) * d.principalCandidate 2 r +
        (-d.sign 1 : ℤ) * d.principalCandidate 3 r = 0) ∧
      (d.principalCandidate 4 r = d.principalCandidate 2 r + (-d.sign 3 : ℤ)) ∧
      ∀ j : Fin 3, d.principalCandidate ⟨j.val + 5, by omega⟩ r =
        d.principalCandidate 1 r + (-d.sign 0 : ℤ) := by
  obtain ⟨h1, h4, he⟩ := threeQuotient_principalCandidate_odd_relations x hx e d r hr
  rw [threeQuotientCharacter_last_signs x e d hx] at h4
  push_cast
  refine ⟨by linear_combination -h1, ?_, fun j => ?_⟩
  · rcases d.sign_unit 3 with hs | hs
    · simp only [hs, Int.cast_one, one_mul] at h4 ⊢
      linear_combination h4
    · simp only [hs, Int.cast_neg, Int.cast_one, neg_one_mul] at h4 ⊢
      linear_combination -h4
  · linear_combination he j

/-- Assemble the actual signed section data from block exhaustion and the two
Sylow restriction congruences. No degree product or resolved signs are used. -/
public def threeQuotientPrincipalSectionData (hx : orderOf x = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hcard : b.block.card = 8)
    (hfirst : 16 ∣ -d.sign 0 * (d.principalSectionDegree 0 : ℤ) - 5)
    (hsecond : 16 ∣ -d.sign 3 * (d.principalSectionDegree 1 : ℤ) - 3) :
    ThreePrincipalSectionData G x := Classical.choice <| by
  classical
  obtain ⟨f, hf0, hf, hrat, k, hk, _, hkd, hinv, u, hu, hfour, ζ, hζ, hcyc⟩ :=
    threeQuotient_principalBlock_sections x hx e d b
  let row : Fin 8 ≃ {i : b.I // i ∈ b.block} := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨f.injective, by simpa using hcard.symm⟩)
  have hrow (i : Fin 8) (g : G) :
      b.chi (row i).val (ConjClasses.mk g) = d.principalCandidate i g :=
    congrFun (hf i) (ConjClasses.mk g)
  refine ⟨{
    blockData := b
    row := row
    principal := hf0
    degree := d.principalSectionDegree
    degree_value := ?_
    sign := ![-d.sign 0, -d.sign 3, -d.sign 1]
    sign_unit := ?_
    rational := hrat
    localRow := k
    local_mem := hk
    local_degree := hkd
    involution_section := hinv
    generator := u
    generator_order := hu
    generator_four := hfour
    root := ζ
    root_primitive := hζ
    cyclic_section := hcyc
    odd_relations := ?_
    odd_fourth := ?_
    odd_exceptional := ?_
    degree_first_congruence := hfirst
    degree_second_congruence := hsecond }⟩
  · intro i
    rw [hrow]
    exact threeQuotient_principalCandidate_degree x hx e d i
  · intro i
    have hs (j : Fin 4) : -d.sign j = 1 ∨ -d.sign j = -1 := by
      rcases d.sign_unit j with h | h <;> simp [h]
    fin_cases i <;> exact hs _
  · intro r hr
    simp only [hrow, Matrix.cons_val]
    exact (threeQuotient_principalCandidate_signed_odd_relations x hx e d r hr).1
  · intro r hr
    simp only [hrow, Matrix.cons_val]
    exact (threeQuotient_principalCandidate_signed_odd_relations x hx e d r hr).2.1
  · intro r hr j
    simp only [hrow, Matrix.cons_val]
    exact (threeQuotient_principalCandidate_signed_odd_relations x hx e d r hr).2.2 j

end
end ABG
