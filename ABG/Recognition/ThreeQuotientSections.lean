module
public import ABG.Recognition.ThreeQuotientPrincipalBlock
public import ABG.Recognition.ThreeQuotientRationality
public import Theory.Character.ModularBlock.InvolutionRootRestriction
public import ABG.ChapterIII.Section2.ThreePrincipalSectionData
public import Theory.GroupTheory.PrimePowerDecomposition

/-!
# Ambient principal characters from the GL₂(3) odd-core quotient

All seven Wong constituents belong to any prescribed ambient principal
congruence two-block. On cyclic roots of the involution their values are
signed inflated rows of the concrete GL₂(3) table. This gives the full
involution section with the degree-three local row, while retaining the
odd core and the arbitrary modular place. Rationality is re-exported from
`ThreeQuotientRationality` for the same character witnesses.

Project the ordinary restriction onto the eight inflated local principal
rows. Frobenius reciprocity identifies its five supported coefficients.
The table's vanishing criterion recovers its root values, which are nonzero
at the involution for every Wong constituent. The compatible principal
restriction theorem then forces ambient membership and transfers all root
values. Positivity of degrees identifies the final two Wong signs.

Source: Alperin--Brauer--Gorenstein III.5--6, especially III.6 preceding
(4), and Wong (1964), Table 1 and equation (3).
-/

open scoped BigOperators
open BenderGlauberman Matrix Matrix.GeneralLinearGroup
open ModularBlock.PrincipalBlockConstruction
namespace ABG
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)
local notation "L" => GL (Fin 2) (ZMod 3)

private def projection (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (f : ClassFunction C) : ClassFunction L :=
  ∑ j : Fin 8, (scalarProduct C f
    (fun a => glTwoThreeCharacter j (threeOddCoreQuotientMap e a))) • glTwoThreeCharacter j

private theorem projection_class (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (f : ClassFunction C) : IsClassFunction (projection x e f) := by
  intro a g
  simp only [projection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible _) a g]

private theorem projection_coeff (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (f : ClassFunction C) (k : Fin 5) :
    scalarProduct L (projection x e f) (glTwoThreeSupportedGenerator k) =
      scalarProduct C f (threeQuotientGenerator x e k) := by
  have hp (j : Fin 8) : scalarProduct L (projection x e f) (glTwoThreeCharacter j) =
      scalarProduct C f (fun a => glTwoThreeCharacter j (threeOddCoreQuotientMap e a)) := by
    simp [projection, scalarProduct_sum_left, scalarProduct_smul_left,
      glTwoThreeCharacter_orthonormal]
  have hg : threeQuotientGenerator x e k =
      ![(fun a => glTwoThreeCharacter 0 (threeOddCoreQuotientMap e a)) +
          (fun a => glTwoThreeCharacter 2 (threeOddCoreQuotientMap e a)) -
          (fun a => glTwoThreeCharacter 4 (threeOddCoreQuotientMap e a)),
        (fun a => glTwoThreeCharacter 2 (threeOddCoreQuotientMap e a)) -
          (fun a => glTwoThreeCharacter 6 (threeOddCoreQuotientMap e a)),
        (fun a => glTwoThreeCharacter 6 (threeOddCoreQuotientMap e a)) -
          (fun a => glTwoThreeCharacter 7 (threeOddCoreQuotientMap e a)),
        (fun a => glTwoThreeCharacter 1 (threeOddCoreQuotientMap e a)) +
          (fun a => glTwoThreeCharacter 4 (threeOddCoreQuotientMap e a)) -
          (fun a => glTwoThreeCharacter 5 (threeOddCoreQuotientMap e a)),
        (fun a => glTwoThreeCharacter 1 (threeOddCoreQuotientMap e a)) +
          (fun a => glTwoThreeCharacter 2 (threeOddCoreQuotientMap e a)) -
          (fun a => glTwoThreeCharacter 3 (threeOddCoreQuotientMap e a))] k := by
    fin_cases k <;> rfl
  rw [hg]
  fin_cases k <;>
    simp only [glTwoThreeSupportedGenerator, Matrix.cons_val, Fin.reduceFinMk,
      scalarProduct_add_right, scalarProduct_sub_right, hp]

private theorem projection_transfer
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (i : b.I) (a : C) (ha : x ∈ Subgroup.zpowers (a : G)) :
    projection x e (fun c => b.chi i (ConjClasses.mk (c : G)))
        (threeOddCoreQuotientMap e a) =
      if i ∈ b.block then b.chi i (ConjClasses.mk (a : G)) else 0 := by
  have h := ModularBlock.InvolutionRootRestriction.restriction_projection_on_involution_roots
    b x hx i a ha
  dsimp only at h
  rw [← Finset.sum_coe_sort,
    ← (threeOddCorePrincipalBlockEquiv e (ModularBlock.CompatibleBrauerBlock.localData b C)).sum_comp]
    at h
  simp only [threeOddCorePrincipalBlockEquiv_character, threeOddCoreCharacter_apply,
    projection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg (fun I : Fintype C => @scalarProduct C I
    (fun c => b.chi i (ConjClasses.mk (c : G)))
    (fun c => glTwoThreeCharacter j (threeOddCoreQuotientMap e c)))
    (Subsingleton.elim _ _)

private def localRow : Fin 7 → Fin 8 := ![2,4,6,7,1,5,3]
private def localSign {Ψ : Fin 5 → ClassFunction G} (d : ThreeCharacterDecomposition Ψ) :
    Fin 7 → ℤ := ![d.sign 0,d.sign 0,d.sign 0,d.sign 0,d.sign 1,-d.sign 2,-d.sign 3]

private theorem catalog_coeff
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (j : Fin 7) (k : Fin 5) :
    scalarProduct G (d.χ j) (threeQuotientInducedGenerator x e k) =
      scalarProduct L ((localSign d j : ℂ) • glTwoThreeCharacter (localRow j))
        (glTwoThreeSupportedGenerator k) := by
  have ho (i l : Fin 7) : scalarProduct G (d.χ i) (d.χ l) = if i = l then 1 else 0 := by
    rw [scalarProduct_irr_ite (d.irreducible i) (d.irreducible l)]
    simp only [d.distinct.eq_iff]
  have h1 (i : Fin 7) : scalarProduct G (d.χ i) 1 = 0 :=
    irreducible_scalarProduct_of_ne (d.irreducible i) isLinearCharacter_one.1 (d.nontrivial i)
  fin_cases j <;> fin_cases k <;>
    simp [d.first, d.second, d.third, d.fourth, d.fifth,
      localSign, localRow, glTwoThreeSupportedGenerator,
      scalarProduct_add_right, scalarProduct_sub_right, scalarProduct_smul_right,
      scalarProduct_smul_left, scalarProduct_neg_left,
      glTwoThreeCharacter_orthonormal, star_intCast, ho, h1]

private theorem catalog_projection
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (hx : orderOf x = 2) (j : Fin 7) (a : C)
    (ha : x ∈ Subgroup.zpowers (a : G)) :
    projection x e (fun c => d.χ j (c : G)) (threeOddCoreQuotientMap e a) =
      (localSign d j : ℂ) * glTwoThreeCharacter (localRow j) (threeOddCoreQuotientMap e a) := by
  apply sub_eq_zero.mp
  apply glTwoThree_orthogonal_vanishes
    (f := projection x e (fun c => d.χ j (c : G)) -
      (localSign d j : ℂ) • glTwoThreeCharacter (localRow j))
    (by intro a g; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          projection_class x e _ a g,
          irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible _) a g])
    (fun k => ?_) _ ((threeOddCoreQuotientMap_root_iff x hx e a).mpr ha)
  rw [_root_.scalarProduct_sub_left, projection_coeff,
    scalarProduct_restrict_induced C (irreducibleCharacter_isClassFunction (d.irreducible j))]
  exact sub_eq_zero.mpr (catalog_coeff x e d j k)

/-- Every Wong constituent lies in the prescribed ambient principal block. -/
public theorem threeQuotientCharacter_mem_principalBlock
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2) (j : Fin 7) :
    ∃ i : b.I, i ∈ b.block ∧
      (fun g => b.chi i (ConjClasses.mk g)) = d.χ j := by
  obtain ⟨i, hi⟩ := b.complete.2.1 _
    (isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19 (d.irreducible j))
  have he : (fun g => b.chi i (ConjClasses.mk g)) = d.χ j := congrArg
    (fun f : ConjClassFunction G => fun g => f (ConjClasses.mk g)) hi
  refine ⟨i, ?_, he⟩
  by_contra hn
  let z : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : x ∈ Subgroup.zpowers (z : G) := Subgroup.mem_zpowers x
  have ht := projection_transfer x e b hx i z hz
  have hc := catalog_projection x e d hx j z hz
  rw [if_neg hn] at ht
  have hre : (fun c : C => b.chi i (ConjClasses.mk (c : G))) =
      (fun c : C => d.χ j (c : G)) := congrArg (fun f : ClassFunction G => fun c : C => f c) he
  rw [hre, hc, threeOddCoreQuotientMap_involution x hx e] at ht
  change (localSign d j : ℂ) * glTwoThreeCharacter (localRow j) (threeClassRepr 1) = 0 at ht
  rw [glTwoThreeCharacter_values] at ht
  fin_cases j <;> simp only [localSign, localRow, Matrix.cons_val, Fin.reduceFinMk,
    glTwoThreeCharacterTable, Int.cast_neg] at ht
  all_goals first
    | solve | rcases d.sign_unit 0 with hs | hs <;> norm_num [hs] at ht
    | solve | rcases d.sign_unit 1 with hs | hs <;> norm_num [hs] at ht
    | solve | rcases d.sign_unit 2 with hs | hs <;> norm_num [hs] at ht
    | solve | rcases d.sign_unit 3 with hs | hs <;> norm_num [hs] at ht

/-- The seven ambient characters on every cyclic root of the involution. -/
public theorem threeQuotientCharacter_root_restriction
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (j : Fin 7) (a : C) (ha : x ∈ Subgroup.zpowers (a : G)) :
    d.χ j a =
      (![d.sign 0,d.sign 0,d.sign 0,d.sign 0,d.sign 1,-d.sign 2,-d.sign 3] j : ℤ) *
        glTwoThreeCharacter (![2,4,6,7,1,5,3] j) (threeOddCoreQuotientMap e a) := by
  obtain ⟨i, hi, he⟩ := threeQuotientCharacter_mem_principalBlock x e d b hx j
  have ht := projection_transfer x e b hx i a ha
  rw [if_pos hi] at ht
  have hre : (fun c : C => b.chi i (ConjClasses.mk (c : G))) =
      (fun c : C => d.χ j (c : G)) := congrArg (fun f : ClassFunction G => fun c : C => f c) he
  rw [hre, catalog_projection x e d hx j a ha] at ht
  exact (congrFun he a).symm.trans ht.symm

/-- All eight principal candidates occur in the actual ambient principal block. -/
public theorem threeQuotient_principalConjCandidate_mem
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2) (j : Fin 8) :
    ∃ i : b.I, i ∈ b.block ∧ b.chi i = d.principalConjCandidate j := by
  have hc (k : Fin 7) : ∃ i : b.I, i ∈ b.block ∧ b.chi i =
      toConjClassFunction (d.χ k) (irreducibleCharacter_isClassFunction (d.irreducible k)) := by
    obtain ⟨i, hi, he⟩ := threeQuotientCharacter_mem_principalBlock x e d b hx k
    refine ⟨i, hi, ?_⟩
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    exact congrFun he g
  fin_cases j
  · refine ⟨b.principal, b.principal_mem, ?_⟩
    rw [b.principal_eq]
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    rfl
  all_goals exact hc _

/-- The complete root-section table in the principal-candidate indexing.
The local odd core is retained and the modular place is arbitrary. -/
public theorem threeQuotient_principalCandidate_root_restriction
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (a : C) (ha : x ∈ Subgroup.zpowers (a : G)) (j : Fin 8) :
    d.principalCandidate j a =
      (![1,d.sign 0,-d.sign 3,d.sign 1,-d.sign 2,d.sign 0,d.sign 0,d.sign 0] j : ℤ) *
        glTwoThreeCharacter (![0,4,3,1,5,2,6,7] j) (threeOddCoreQuotientMap e a) := by
  fin_cases j
  · simp [ThreeCharacterDecomposition.principalCandidate, glTwoThreeCharacter]
  all_goals exact threeQuotientCharacter_root_restriction x e d b hx _ a ha

/-- The involution column for all eight ambient candidates. -/
public theorem threeQuotient_principalCandidate_involution
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2) (j : Fin 8) :
    d.principalCandidate j x =
      (![1,3*d.sign 0,-3*d.sign 3,d.sign 1,4*d.sign 2,
        2*d.sign 0,-2*d.sign 0,-2*d.sign 0] j : ℤ) := by
  have h := threeQuotient_principalCandidate_root_restriction x e d b hx
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ (Subgroup.mem_zpowers x) j
  rw [threeOddCoreQuotientMap_involution x hx e] at h
  change _ = _ * glTwoThreeCharacter _ (threeClassRepr 1) at h
  rw [glTwoThreeCharacter_values] at h
  rw [h]
  fin_cases j <;> simp [glTwoThreeCharacterTable] <;> ring

/-- Arbitrary ambient irreducibles outside the catalog vanish on involution
roots after projection to the prescribed principal block. -/
public theorem threeQuotient_principalBlock_other_vanishes
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (i : b.I) (hi : i ∈ b.block)
    (hne : ∀ j : Fin 8, b.chi i ≠ d.principalConjCandidate j)
    (a : C) (ha : x ∈ Subgroup.zpowers (a : G)) :
    b.chi i (ConjClasses.mk (a : G)) = 0 := by
  let f : ClassFunction G := fun g => b.chi i (ConjClasses.mk g)
  have hf : IsIrreducibleCharacter f := isIrreducibleCharacter_ofConjClassFunctionBG19 (b.complete.1 i)
  have hn1 : f ≠ 1 := by
    intro h
    apply hne 0
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    exact congrFun h g
  have hnc (k : Fin 7) : f ≠ d.χ k := by
    intro h
    have he (j : Fin 8) (hj : d.principalCandidate j = d.χ k) : False := by
      apply hne j
      funext c
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
      exact (congrFun h g).trans (congrFun hj g).symm
    fin_cases k
    · exact he 5 rfl
    · exact he 1 rfl
    · exact he 6 rfl
    · exact he 7 rfl
    · exact he 3 rfl
    · exact he 4 rfl
    · exact he 2 rfl
  have hz : projection x e (fun c => f (c : G)) (threeOddCoreQuotientMap e a) = 0 := by
    apply glTwoThree_orthogonal_vanishes (projection_class x e _) (fun k => ?_)
      _ ((threeOddCoreQuotientMap_root_iff x hx e a).mpr ha)
    rw [projection_coeff,
      scalarProduct_restrict_induced C (irreducibleCharacter_isClassFunction hf)]
    exact d.orthogonal_of_not_mem hf hn1 hnc k
  have ht := projection_transfer x e b hx i a ha
  rw [if_pos hi] at ht
  exact ht.symm.trans hz

omit [Finite G] in
private theorem odd_mul_root (hx : orderOf x = 2) (r : C) (hr : Odd (orderOf r)) :
    x ∈ Subgroup.zpowers (x * (r : G)) := by
  have hc : Commute x (r : G) := (Subgroup.mem_centralizer_singleton_iff.mp r.property).symm
  have hpow : (x * (r : G)) ^ orderOf r = x := by
    rw [hc.mul_pow, ← Subgroup.coe_pow, pow_orderOf_eq_one, OneMemClass.coe_one, mul_one]
    obtain ⟨n, hn⟩ := hr
    rw [hn, pow_add, pow_mul, show x ^ 2 = 1 from hx ▸ pow_orderOf_eq_one x]
    simp
  exact ⟨(orderOf r : ℤ), by simpa only [zpow_natCast] using hpow⟩

private theorem table_involution_odd (w : L) (hw : Odd (orderOf w)) (j : Fin 8) :
    glTwoThreeCharacter j (threeCentral * w) =
      (![1,1,glTwoThreeCharacter 3 w - 1,glTwoThreeCharacter 3 w,
        glTwoThreeCharacter 3 w,-(glTwoThreeCharacter 3 w + 1),
        1 - glTwoThreeCharacter 3 w,1 - glTwoThreeCharacter 3 w] j : ℂ) := by
  obtain ⟨k, hk, _⟩ := three_conjugacy_data.1 w
  obtain ⟨g, hg⟩ := isConj_iff.mp hk
  have heord : orderOf w = orderOf (threeClassRepr k) := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq w).symm
  have ho : Odd (![1,2,4,3,6,2,8,8] k : ℕ) := by
    rw [← three_conjugacy_data.2.1 k, ← heord]
    exact hw
  have hval (i : Fin 8) : glTwoThreeCharacter i w = glTwoThreeCharacterTable i k := by
    rw [← glTwoThreeCharacter_values, ← hg]
    exact (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i) w g).symm
  have hmul (i : Fin 8) : glTwoThreeCharacter i (threeCentral * w) =
      glTwoThreeCharacter i (threeCentral * threeClassRepr k) := by
    rw [← hg]
    have he : (g * threeCentral * g⁻¹) * (g * w * g⁻¹) =
        g * (threeCentral * w) * g⁻¹ := by group
    calc
      _ = glTwoThreeCharacter i (g * (threeCentral * w) * g⁻¹) :=
        (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i) _ g).symm
      _ = _ := by rw [← he, threeCentral_conj]
  rw [hmul, hval]
  simp only [glTwoThreeCharacterTable, Matrix.cons_val]
  fin_cases k <;> norm_num at ho
  · have he : threeCentral * threeClassRepr 0 = threeClassRepr 1 := by decide +kernel
    simp only [Matrix.cons_val, Fin.reduceFinMk]
    rw [he, glTwoThreeCharacter_values]
    fin_cases j <;> norm_num [glTwoThreeCharacterTable, Matrix.cons_val, Fin.reduceFinMk]
  · have he : threeCentral * threeClassRepr 3 = threeClassRepr 4 := by decide +kernel
    simp only [Matrix.cons_val, Fin.reduceFinMk]
    rw [he, glTwoThreeCharacter_values]
    fin_cases j <;> norm_num [glTwoThreeCharacterTable, Matrix.cons_val, Fin.reduceFinMk] <;> rfl

/-- Positivity of degrees identifies the last two Wong signs. -/
public theorem threeQuotientCharacter_last_signs
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (hx : orderOf x = 2) : d.sign 2 = d.sign 3 := by
  have h := (threeQuotient_principalCandidate_odd_relations x hx e d 1 (by simp)).2.1
  change (d.sign 2 : ℂ) * d.χ 5 1 + 1 = (d.sign 3 : ℂ) * d.χ 6 1 at h
  have hp := irreducible_degree_ge_one (d.irreducible 5)
  have hq := irreducible_degree_ge_one (d.irreducible 6)
  rcases d.sign_unit 2 with h2 | h2 <;> rcases d.sign_unit 3 with h3 | h3
  · exact h2.trans h3.symm
  · have hh := congrArg Complex.re h
    norm_num [h2, h3] at hh
    linarith
  · have hh := congrArg Complex.re h
    norm_num [h2, h3] at hh
    linarith
  · exact h2.trans h3.symm

/-- The full involution section, with the three ABG signs still unresolved. -/
public theorem threeQuotient_principalCandidate_involution_section
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (r : C) (hr : Odd (orderOf r)) (j : Fin 8) :
    d.principalCandidate j (x * (r : G)) =
      threeSignedPrincipalInvolutionSection ![-d.sign 0,-d.sign 3,-d.sign 1]
        (threeOddCoreCharacter e 3 (ConjClasses.mk r)) j := by
  let z : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have h := threeQuotient_principalCandidate_root_restriction x e d b hx
    (z * r) (odd_mul_root x hx r hr) j
  rw [map_mul, threeOddCoreQuotientMap_involution x hx e,
    table_involution_odd _ (hr.of_dvd_nat (orderOf_map_dvd (threeOddCoreQuotientMap e) r))] at h
  change d.principalCandidate j (x * (r : G)) = _ at h
  rw [h, threeOddCoreCharacter_apply]
  fin_cases j <;> simp [threeSignedPrincipalInvolutionSection,
    threeQuotientCharacter_last_signs x e d hx] <;> ring

end
end ABG
