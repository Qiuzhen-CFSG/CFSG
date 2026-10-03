module

public import ABG.Recognition.ThreeQuotientCharacters
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# The full principal two-block above an odd core with quotient GL₂(3)

For any principal congruence-block data on `H`, all eight characters inflated
from `H/O₂′(H) ≃ GL₂(3)` belong to its principal block. Together with the
odd-core descent theorem this identifies the actual block, gives eight rows,
and computes the sum of squared degrees as 48.

The central scalars in the concrete table have the form `class size + 2a + bω`,
with integral `a,b` and `ω² = -2`. The actual inflated faithful character puts
`ω` in the prescribed cyclotomic order; primality puts it in the prescribed
prime above two. Class-size divisibility under the quotient homomorphism then
transfers these congruences to `H`. Thus the construction uses the arbitrary
supplied modular place, including one obtained by compatible restriction.

Source: ABG III.2 Proposition 7, pp.69–70, and its odd-core reduction;
Wong (1964), Table 1, p.97, as proved in `ThreeCharacterTable`.
-/

open scoped BigOperators
open Matrix.GeneralLinearGroup BenderGlauberman
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockPreliminaries
namespace ABG
noncomputable section
private theorem class_size (k : Fin 8) :
    Nat.card (ConjClasses.mk (threeClassRepr k)).carrier = ![1,1,6,8,8,12,6,6] k := by
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
  have h := (Subgroup.centralizer ({threeClassRepr k} : Set (GL (Fin 2) (ZMod 3)))).index_mul_card
  rw [three_conjugacy_data.2.2.1, Matrix.card_GL_field] at h
  norm_num [Fin.prod_univ_two] at h
  fin_cases k <;> norm_num at h ⊢ <;> omega

private theorem table_congruence (i k : Fin 8) :
    ∃ a b : ℤ, (![1,1,6,8,8,12,6,6] k : ℂ) * glTwoThreeCharacterTable i k /
      (![1,1,2,3,3,4,2,2] i : ℂ) =
      (![1,1,6,8,8,12,6,6] k : ℂ) + 2 * a + b * glTwoThreeOmega := by
  let a : Fin 8 → Fin 8 → ℤ :=
    ![![0,0,0,0,0,0,0,0], ![0,0,0,0,0,-12,-6,-6],
      ![0,0,0,-6,-6,-6,-3,-3], ![0,0,-4,-4,-4,-8,-2,-2],
      ![0,0,-4,-4,-4,-4,-4,-4], ![0,-1,-3,-3,-5,-6,-3,-3],
      ![0,-1,-3,-6,-2,-6,-3,-3], ![0,-1,-3,-6,-2,-6,-3,-3]]
  let b : Fin 8 → Fin 8 → ℤ :=
    ![![0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0],
      ![0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0],
      ![0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0],
      ![0,0,0,0,0,0,3,-3], ![0,0,0,0,0,0,-3,3]]
  refine ⟨a i k, b i k, ?_⟩
  fin_cases i <;> fin_cases k <;> norm_num [a, b, glTwoThreeCharacterTable] <;> ring

variable {H : Type*} [Group H] [Finite H]
private theorem omega_mem (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) : glTwoThreeOmega ∈ cyclotomicOrder d.eta := by
  obtain ⟨h, hh⟩ := threeOddCoreQuotientMap_surjective e (threeClassRepr 6)
  obtain ⟨n, ρ, hρ⟩ := (threeOddCoreCharacter_irreducible e 6).1
  have hv : ρ.character h = glTwoThreeOmega := by
    have he := congrFun hρ (ConjClasses.mk h)
    rw [threeOddCoreCharacter_apply, hh, glTwoThreeCharacter_values] at he
    exact he.symm
  rw [← hv]
  exact representation_character_mem_cyclotomicOrder d.eta_spec ρ h

private theorem omega_in_prime (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) :
    (⟨glTwoThreeOmega, omega_mem e d⟩ : cyclotomicOrder d.eta) ∈ d.primeIdeal := by
  apply d.primeIdeal_maximal.isPrime.mem_of_pow_mem 2
  have hw : (⟨glTwoThreeOmega, omega_mem e d⟩ : cyclotomicOrder d.eta) ^ 2 = -2 := by
    apply Subtype.ext
    exact glTwoThreeOmega_sq
  rw [hw]
  exact d.primeIdeal.neg_mem (two_mem_of_liesOver d.primeIdeal d.primeIdeal_liesOverTwo)

private theorem inflated_congruence
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) (i : Fin 8) :
    SameTwoBlock d.eta_spec d.primeIdeal
      (threeOddCoreCharacter e i) (ordinaryPrincipalCharacter H)
      (threeOddCoreCharacter_irreducible e i) ordinaryPrincipalCharacter_irreducible := by
  classical
  apply (sameTwoBlock_iff _ _ _ _ _ _).mpr
  intro c
  obtain ⟨h, rfl⟩ := ConjClasses.exists_rep c
  let f := threeOddCoreQuotientMap e
  let k := threeClassIndex (f h)
  have hk : ConjClasses.mk (f h) = ConjClasses.mk (threeClassRepr k) :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (three_isConj_classIndex (f h))
  have hd := ConjClasses.nat_card_carrier_map_dvd f (threeOddCoreQuotientMap_surjective e) h
  rw [hk, class_size] at hd
  obtain ⟨n, hn⟩ := hd
  obtain ⟨a, b, hab⟩ := table_congruence i k
  let w : cyclotomicOrder d.eta := ⟨glTwoThreeOmega, omega_mem e d⟩
  have heq :
      centralCharacterInCyclotomicOrder d.eta_spec (threeOddCoreCharacter e i)
          (threeOddCoreCharacter_irreducible e i) (ConjClasses.mk h) -
        centralCharacterInCyclotomicOrder d.eta_spec (ordinaryPrincipalCharacter H)
          ordinaryPrincipalCharacter_irreducible (ConjClasses.mk h) =
      2 * ((n : cyclotomicOrder d.eta) * a) + ((n : cyclotomicOrder d.eta) * b) * w := by
    apply Subtype.ext
    change ordinaryCentralCharacterValue (threeOddCoreCharacter e i) (ConjClasses.mk h) -
      ordinaryCentralCharacterValue (ordinaryPrincipalCharacter H) (ConjClasses.mk h) =
      2 * ((n : ℂ) * a) + ((n : ℂ) * b) * glTwoThreeOmega
    rw [ordinaryCentralCharacterValue, ordinaryCentralCharacterValue,
      threeOddCoreCharacter_degree, threeOddCoreCharacter_apply,
      ordinaryPrincipalCharacter_apply, ordinaryPrincipalCharacter_apply]
    have hval : glTwoThreeCharacter i (threeOddCoreQuotientMap e h) =
        glTwoThreeCharacterTable i k :=
      (three_classFunction_apply _
        (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i)) (f h)).trans
        (glTwoThreeCharacter_values i k)
    rw [hval, hn, Nat.cast_mul]
    push_cast
    calc
      _ = (n : ℂ) * ((![1,1,6,8,8,12,6,6] k : ℂ) * glTwoThreeCharacterTable i k /
          (![1,1,2,3,3,4,2,2] i : ℂ)) - (![1,1,6,8,8,12,6,6] k : ℂ) * n := by
        have hcast (l : Fin 8) : ((![1,1,6,8,8,12,6,6] l : ℕ) : ℂ) =
            (![1,1,6,8,8,12,6,6] l : ℂ) := by fin_cases l <;> norm_num
        rw [hcast]
        ring
      _ = _ := by rw [hab]; ring
  rw [heq]
  exact d.primeIdeal.add_mem
    (d.primeIdeal.mul_mem_right _ (two_mem_of_liesOver d.primeIdeal d.primeIdeal_liesOverTwo))
    (d.primeIdeal.mul_mem_left _ (omega_in_prime e d))

/-- Every actual inflated row belongs to the principal block at the prescribed place. -/
public theorem threeOddCoreCharacter_mem_principalBlock
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) (i : Fin 8) :
    ∃ j : d.I, j ∈ d.block ∧ d.chi j = threeOddCoreCharacter e i := by
  obtain ⟨j, hj⟩ := d.complete.2.1 _ (threeOddCoreCharacter_irreducible e i)
  refine ⟨j, ?_, hj⟩
  rw [d.mem_block_iff]
  have hi := inflated_congruence e d i
  simpa only [hj, d.principal_eq] using hi

/-- The actual inflated table parametrizes all rows of any principal congruence block. -/
public def threeOddCorePrincipalBlockEquiv
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) : Fin 8 ≃ {j : d.I // j ∈ d.block} := by
  classical
  let f : Fin 8 → {j : d.I // j ∈ d.block} := fun i =>
    ⟨Classical.choose (threeOddCoreCharacter_mem_principalBlock e d i),
      (Classical.choose_spec (threeOddCoreCharacter_mem_principalBlock e d i)).1⟩
  have hf (i : Fin 8) : d.chi (f i).val = threeOddCoreCharacter e i :=
    (Classical.choose_spec (threeOddCoreCharacter_mem_principalBlock e d i)).2
  exact Equiv.ofBijective f ⟨by
    intro i k hik
    apply threeOddCoreCharacter_injective e
    rw [← hf i, ← hf k, hik], by
    intro j
    obtain ⟨i, hi, _⟩ := threeOddCoreCharacter_complete_on_principalBlock e d j.property
    refine ⟨i, Subtype.ext (d.complete.2.2 ?_)⟩
    exact (hf i).trans hi⟩

public theorem threeOddCorePrincipalBlockEquiv_character
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) (i : Fin 8) :
    d.chi (threeOddCorePrincipalBlockEquiv e d i).val = threeOddCoreCharacter e i :=
  (Classical.choose_spec (threeOddCoreCharacter_mem_principalBlock e d i)).2

/-- There are exactly eight principal-block rows above the odd core. -/
public theorem threeOddCore_principalBlock_card
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) : d.block.card = 8 := by
  simpa using (Fintype.card_congr (threeOddCorePrincipalBlockEquiv e d)).symm

/-- The squared degrees of the actual principal-block rows sum to 48. -/
public theorem threeOddCore_principalBlock_degree_square_sum
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) :
    ∑ j ∈ d.block, (d.chi j (ConjClasses.mk 1)) ^ 2 = 48 := by
  classical
  rw [← Finset.sum_coe_sort, ← (threeOddCorePrincipalBlockEquiv e d).sum_comp]
  simp only [threeOddCorePrincipalBlockEquiv_character, threeOddCoreCharacter_degree]
  norm_num [Fin.sum_univ_succ]

/-- In particular the local principal block contains an actual degree-three row. -/
public theorem threeOddCore_principalBlock_exists_degree_three
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) :
    ∃ j : d.I, j ∈ d.block ∧ d.chi j = threeOddCoreCharacter e 3 ∧
      d.chi j (ConjClasses.mk 1) = 3 := by
  obtain ⟨j, hj, he⟩ := threeOddCoreCharacter_mem_principalBlock e d 3
  exact ⟨j, hj, he, he ▸ threeOddCoreCharacter_degree e 3⟩

end
end ABG
