module

public import Theory.SpecificGroups.BabyMonster.NormalSubgroups.Generation
public import Theory.Alternating.theorem_5_2_1_2
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# An alternating-nine subgroup of a Baby Monster involution centralizer

The chain of vertices 0,...,7 in the fixed Y433 presentation gives a homomorphism
from S9. Each vertex commutes with vertex 9, so this homomorphism lands in its
centralizer. Its restriction to A9 is injective whenever the presented carrier
is nontrivial: simplicity of A9 reduces injectivity to the nonidentity of the
image of (0 1 2). If generators 0 and 1 coincide, the Coxeter relations identify
the generators appearing in the first arm word; its ninth-power relation then
kills generator 0. Normal generation would make the whole carrier trivial.

Thus the parent simple-group case needs neither matrix recognition nor the
order or simplicity theorem for the presented carrier. Nontriviality is an
explicit hypothesis, supplied there by the actual group identification.
The carrier still has BOTH ninth-power relators; it is not replaced by a
presentation for a double cover.

Source: Breuer--Magaard--Wilson, *Verification of the ordinary character table
of the Baby Monster* (2019), section 3.1, for the presentation. This direct
subdiagram argument supplies an alternative simple section for the
Aschbacher--Smith A.2.19 obstruction, using A.2.15(2).
-/

public section
namespace BabyMonster
open GLS3.Chapter5.SchurPresentation

private theorem commute_of_squares {G : Type*} [Group G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) : Commute a b := by
  have ha' : a⁻¹ = a := (eq_inv_of_mul_eq_one_right (by simpa [pow_two] using ha)).symm
  have hb' : b⁻¹ = b := (eq_inv_of_mul_eq_one_right (by simpa [pow_two] using hb)).symm
  have hab' : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right (by simpa [pow_two] using hab)
  simpa only [Commute, SemiconjBy, mul_inv_rev, ha', hb'] using hab'

private theorem equal_of_commuting_involutions {G : Type*} [Group G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : Commute a b)
    (hab : (a * b) ^ 3 = 1) : a = b := by
  have hab2 : (a * b) ^ 2 = 1 := by rw [hc.mul_pow, ha, hb, one_mul]
  have hab1 : a * b = 1 := by simpa only [pow_succ, hab2, one_mul] using hab
  calc
    a = a * (b * b) := by rw [← pow_two, hb, mul_one]
    _ = (a * b) * b := (mul_assoc _ _ _).symm
    _ = b := by rw [hab1, one_mul]

private theorem generator_zero_commutes (j : Generator) (hj : 2 ≤ j.val) :
    Commute (generator 0) (generator j) := by
  apply commute_of_squares (generator_sq 0) (generator_sq j)
  have hnot : (0, j) ∉ edges := by
    fin_cases j <;> simp_all [edges]
  simpa only [coxeterExponent, if_neg hnot] using
    generator_pair 0 j (by change 0 < j.val; omega)

/-- Every canonical generator is nonidentity in a nontrivial carrier. -/
theorem generator_ne_one [Nontrivial Carrier] (i : Generator) : generator i ≠ 1 := by
  intro h
  have hh := hom_eq_one_of_generator_eq_one (MonoidHom.id Carrier) i h
  obtain ⟨x, hx⟩ := exists_ne (1 : Carrier)
  exact hx (DFunLike.congr_fun hh x)

/-- The canonical generators are genuine involutions in a nontrivial carrier. -/
theorem generator_orderOf [Nontrivial Carrier] (i : Generator) : orderOf (generator i) = 2 :=
  orderOf_eq_prime (generator_sq i) (generator_ne_one i)

private theorem generator_zero_ne_generator_one [Nontrivial Carrier] : generator 0 ≠ generator 1 := by
  intro heq
  have step (i j : Generator) (hij : (i, j) ∈ edges) (hj : 2 ≤ j.val)
      (hi : generator i = generator 0) : generator j = generator 0 := by
    have hlt : i < j := by
      simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hij
      rcases hij with h | h | h | h | h | h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> decide
    apply (equal_of_commuting_involutions (generator_sq 0) (generator_sq j)
      (generator_zero_commutes j hj) _).symm
    simpa only [coxeterExponent, if_pos hij, hi] using generator_pair i j hlt
  have h2 := step 1 2 (by decide) (by decide) heq.symm
  have h3 := step 2 3 (by decide) (by decide) h2
  have h4 := step 3 4 (by decide) (by decide) h3
  have h5 := step 4 5 (by decide) (by decide) h4
  have h6 := step 5 6 (by decide) (by decide) h5
  have h7 := step 6 7 (by decide) (by decide) h6
  have h8 := step 4 8 (by decide) (by decide) h4
  have h := generator_firstArm
  simp only [firstArmWord, h2, h3, h4, h5, h6, h7, h8] at h
  have hw : generator 0 * generator 0 * generator 0 * generator 0 *
      generator 0 * generator 0 * generator 0 = generator 0 ^ 7 := by
    simp only [pow_succ, pow_zero, one_mul]
  rw [hw, ← pow_mul, pow_eq_pow_mod 63 (generator_sq 0)] at h
  exact generator_ne_one 0 (by simpa using h)

private abbrev NineCentralizer := Subgroup.centralizer ({generator 9} : Set Carrier)

private abbrev chainIndex (i : Fin 8) : Generator := i.castLE (by decide)

private def chainGenerator (i : Fin 8) : NineCentralizer :=
  ⟨generator (chainIndex i), by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hp : (generator (chainIndex i) * generator 9) ^ 2 = 1 := by
      have hnot : (chainIndex i, (9 : Generator)) ∉ edges := by
        fin_cases i <;> decide
      simpa only [coxeterExponent, if_neg hnot] using
        generator_pair (chainIndex i) 9 (by change i.val < 9; omega)
    exact (commute_of_squares (generator_sq _) (generator_sq _) hp).eq⟩

private theorem chain_liftable : (CoxeterMatrix.A 8).IsLiftable chainGenerator := by
  intro i j
  apply Subtype.ext
  change (generator (chainIndex i) * generator (chainIndex j)) ^
      (CoxeterMatrix.A 8) i j = 1
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hexp : ∀ i j : Fin 8, i < j → (CoxeterMatrix.A 8) i j =
        coxeterExponent (chainIndex i) (chainIndex j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.A, coxeterExponent, edges, chainIndex]
    rw [hexp i j hij]
    exact generator_pair _ _ hij
  · simpa only [CoxeterMatrix.diagonal, pow_one, ← pow_two] using
      generator_sq (chainIndex i)
  · have hexp : ∀ i j : Fin 8, j < i → (CoxeterMatrix.A 8) i j =
        coxeterExponent (chainIndex j) (chainIndex i) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.A, coxeterExponent, edges, chainIndex]
    rw [hexp i j hji]
    have h := generator_pair (chainIndex j) (chainIndex i) hji
    have hi : (generator (chainIndex i))⁻¹ = generator (chainIndex i) :=
      (eq_inv_of_mul_eq_one_right (by simpa [pow_two] using generator_sq (chainIndex i))).symm
    have hj : (generator (chainIndex j))⁻¹ = generator (chainIndex j) :=
      (eq_inv_of_mul_eq_one_right (by simpa [pow_two] using generator_sq (chainIndex j))).symm
    simpa only [← inv_pow, mul_inv_rev, hi, hj, inv_one] using congrArg Inv.inv h

private noncomputable def symmetricNineEquiv : TypeACoxeterGroup 4 ≃* Equiv.Perm (Fin 9) :=
  MulEquiv.ofBijective (typeACoxeterPermutationProjection 4)
    ⟨typeACoxeterPermutationProjection_injective 4,
      typeACoxeterPermutationProjection_surjective 4⟩

private noncomputable def symmetricNineHom : Equiv.Perm (Fin 9) →* NineCentralizer :=
  ((CoxeterMatrix.A 8).toCoxeterSystem.lift ⟨chainGenerator, chain_liftable⟩).comp
    symmetricNineEquiv.symm.toMonoidHom

private theorem symmetricNineHom_adjacent (i : Fin 8) :
    symmetricNineHom (adjacentSwap 4 i) = chainGenerator i := by
  have hi : symmetricNineEquiv ((CoxeterMatrix.A 8).simple i) = adjacentSwap 4 i :=
    typeACoxeterPermutationProjection_simple 4 i
  rw [← hi]
  change ((CoxeterMatrix.A 8).toCoxeterSystem.lift ⟨chainGenerator, chain_liftable⟩)
    (symmetricNineEquiv.symm (symmetricNineEquiv ((CoxeterMatrix.A 8).simple i))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (CoxeterMatrix.A 8).toCoxeterSystem.lift_apply_simple chain_liftable i

/-- The A9 homomorphism obtained from the eight-vertex chain. -/
noncomputable def alternatingNineHom : alternatingGroup (Fin 9) →* Carrier :=
  NineCentralizer.subtype.comp (symmetricNineHom.comp (alternatingGroup (Fin 9)).subtype)

private def threeCycle : alternatingGroup (Fin 9) :=
  ⟨adjacentSwap 4 0 * adjacentSwap 4 1, by
    simp [Equiv.Perm.mem_alternatingGroup, adjacentSwap]⟩

private theorem alternatingNineHom_threeCycle :
    alternatingNineHom threeCycle = generator 0 * generator 1 := by
  change (symmetricNineHom (adjacentSwap 4 0 * adjacentSwap 4 1) : Carrier) = _
  rw [map_mul, symmetricNineHom_adjacent, symmetricNineHom_adjacent]
  rfl

/-- Simplicity of A9 and the arm relation prevent the chain map from collapsing. -/
theorem alternatingNineHom_injective [Nontrivial Carrier] :
    Function.Injective alternatingNineHom := by
  let : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  apply (alternatingNineHom.ker_eq_bot_iff).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal alternatingNineHom.ker inferInstance with h | h
  · exact h
  · have hz : alternatingNineHom threeCycle = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [h]
      trivial
    rw [alternatingNineHom_threeCycle] at hz
    have : generator 0 = generator 1 := by
      calc
        generator 0 = generator 0 * (generator 1 * generator 1) := by
          rw [← pow_two, generator_sq, mul_one]
        _ = (generator 0 * generator 1) * generator 1 := (mul_assoc _ _ _).symm
        _ = generator 1 := by rw [hz, one_mul]
    exact (generator_zero_ne_generator_one this).elim

/-- The constructed A9 image centralizes the canonical generator numbered 9. -/
theorem alternatingNineHom_centralizes (a : alternatingGroup (Fin 9)) :
    alternatingNineHom a ∈ Subgroup.centralizer ({generator 9} : Set Carrier) :=
  (symmetricNineHom a).property

end BabyMonster
