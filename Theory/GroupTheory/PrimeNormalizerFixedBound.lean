module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Fixed points of prime subgroup normalizers

Let E be a finite group of order p+1 for a prime p, and let K be an
order-p subgroup of its automorphism group. A nonidentity automorphism
normalizing K fixes at most one nonidentity element of E. No elementary
abelian, involution, or solvability hypothesis is required.

Every nonidentity element of K induces a permutation of prime order p.
Its single p-cycle comprises all nonidentity elements of E. Evaluation
at any such element is therefore injective on K, and the cycle acts
transitively on those elements.

If a normalizing automorphism fixes two distinct nonidentity elements,
the translation between them agrees with its conjugate at the first
point. Injective evaluation forces commutation with that translation.
Transitivity then forces the automorphism to fix every element, contrary
to its nonidentity hypothesis. This bounds its fixed subgroup by the
identity and at most one other point.

This generalizes the order-eight/order-seven argument used in Stellmacher
Section 11 (`refs/latex/stellmacher-n-group.tex`) and supplies the
order-thirty-two/order-thirty-one instance used for the oddness consequence
of Parrott (1972), GL(5,2) property (7), printed p.673.
-/

universe u

private theorem prime_cycle
    (p : ℕ) (hp : Nat.Prime p)
    (E : Type u) [Group E] [Finite E] (hE : Nat.card E = p + 1)
    (K : Subgroup (MulAut E)) (hK : Nat.card K = p)
    (translation : MulAut E) (hmem : translation ∈ K) (hne : translation ≠ 1) :
    (MulAut.toPerm E translation).IsCycle ∧
      ∀ element : E, element ≠ 1 → translation element ≠ element := by
  classical
  let _ := Fintype.ofFinite E
  have horder : orderOf translation = p := by
    have hdiv := K.orderOf_dvd_natCard hmem
    rw [hK] at hdiv
    rcases (Nat.dvd_prime hp).mp hdiv with hone | hprime
    · exact False.elim (hne (orderOf_eq_one_iff.mp hone))
    · exact hprime
  have hinj : Function.Injective (MulAut.toPerm E) := by
    intro first second heq
    apply MulEquiv.ext
    exact Equiv.congr_fun heq
  have hperm : orderOf (MulAut.toPerm E translation) = p := by
    rw [orderOf_injective (MulAut.toPerm E) hinj, horder]
  have hcycle : (MulAut.toPerm E translation).IsCycle := by
    apply Equiv.Perm.isCycle_of_prime_order'
    · rw [hperm]; exact hp
    · rw [hperm, ← Nat.card_eq_fintype_card, hE]
      have := hp.two_le
      omega
  have hsupport : (MulAut.toPerm E translation).support = Finset.univ.erase 1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro element hmember
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq
      subst element
      exact (Equiv.Perm.mem_support.mp hmember) (map_one translation)
    · rw [← hcycle.orderOf, hperm, Finset.card_erase_of_mem (Finset.mem_univ 1),
        Finset.card_univ, ← Nat.card_eq_fintype_card, hE]
      omega
  refine ⟨hcycle, ?_⟩
  intro element hnelement
  have hmember : element ∈ (MulAut.toPerm E translation).support := by
    rw [hsupport]
    simp [hnelement]
  exact Equiv.Perm.mem_support.mp hmember

private theorem prime_evaluation_injective
    (p : ℕ) (hp : Nat.Prime p)
    (E : Type u) [Group E] [Finite E] (hE : Nat.card E = p + 1)
    (K : Subgroup (MulAut E)) (hK : Nat.card K = p)
    (element : E) (hnelement : element ≠ 1) :
    Function.Injective (fun translation : K => (translation : MulAut E) element) := by
  intro first second heq
  change (first : MulAut E) element = (second : MulAut E) element at heq
  have hone : (second : MulAut E)⁻¹ * first = 1 := by
    by_contra hne
    have hmove := (prime_cycle p hp E hE K hK _
      (K.mul_mem (K.inv_mem second.property) first.property) hne).2 element hnelement
    apply hmove
    change (second : MulAut E)⁻¹ ((first : MulAut E) element) = element
    rw [heq]
    exact MulAut.inv_apply_self E (second : MulAut E) element
  apply Subtype.ext
  exact (inv_mul_eq_one.mp hone).symm

private theorem fixed_nonidentity_unique
    (p : ℕ) (hp : Nat.Prime p)
    (E : Type u) [Group E] [Finite E] (hE : Nat.card E = p + 1)
    (K : Subgroup (MulAut E)) (hK : Nat.card K = p)
    (automorphism : MulAut E)
    (hnormalizer : automorphism ∈ Subgroup.normalizer (K : Set (MulAut E)))
    (hne : automorphism ≠ 1)
    (first second : E) (hfirst : first ≠ 1) (hsecond : second ≠ 1)
    (hfixfirst : automorphism first = first)
    (hfixsecond : automorphism second = second) : first = second := by
  classical
  by_contra hdistinct
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hdiv : p ∣ Nat.card K := hK ▸ dvd_rfl
  obtain ⟨generator, horder⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hgenne : (generator : MulAut E) ≠ 1 := by
    intro heq
    have : generator = 1 := Subtype.ext heq
    have hone : orderOf generator = 1 := by simp [this]
    exact hp.ne_one (horder.symm.trans hone)
  have hgen := prime_cycle p hp E hE K hK generator generator.property hgenne
  obtain ⟨power, hpower⟩ := hgen.1.exists_pow_eq (hgen.2 first hfirst)
    (hgen.2 second hsecond)
  let translation : MulAut E := (generator : MulAut E) ^ power
  have htrans : translation first = second := by
    rw [← map_pow] at hpower
    exact hpower
  have hmem : translation ∈ K := K.pow_mem generator.property power
  have htransne : translation ≠ 1 := by
    intro heq
    apply hdistinct
    simpa [heq] using htrans
  have hconjmem : automorphism * translation * automorphism⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hnormalizer translation).mp hmem
  have hinvfirst : automorphism⁻¹ first = first := by
    calc
      automorphism⁻¹ first = automorphism⁻¹ (automorphism first) :=
        congrArg (fun element => automorphism⁻¹ element) hfixfirst.symm
      _ = first := MulAut.inv_apply_self E automorphism first
  have hconj : automorphism * translation * automorphism⁻¹ = translation := by
    have heq :
        (⟨automorphism * translation * automorphism⁻¹, hconjmem⟩ : K) =
          ⟨translation, hmem⟩ := by
      apply prime_evaluation_injective p hp E hE K hK first hfirst
      change automorphism (translation (automorphism⁻¹ first)) = translation first
      rw [hinvfirst, htrans, hfixsecond]
    exact congrArg Subtype.val heq
  have hcommute : Commute automorphism translation := by
    change automorphism * translation = translation * automorphism
    exact (mul_inv_eq_iff_eq_mul).mp hconj
  have hcycle := prime_cycle p hp E hE K hK translation hmem htransne
  apply hne
  apply MulEquiv.ext
  intro element
  change automorphism element = element
  by_cases helement : element = 1
  · simp [helement]
  obtain ⟨exponent, hexponent⟩ := hcycle.1.exists_pow_eq
    (hcycle.2 first hfirst) (hcycle.2 element helement)
  have hreach : (translation ^ exponent) first = element := by
    rw [← map_pow] at hexponent
    exact hexponent
  rw [← hreach]
  have heq := congrArg (fun map : MulAut E => map first) (hcommute.pow_right exponent).eq
  simpa only [MulAut.mul_apply, hfixfirst] using heq

/-- A nonidentity prime-subgroup normalizer fixes at most two elements. -/
public theorem card_fixed_le_two_of_normalizes_prime
    (p : ℕ) (hp : Nat.Prime p)
    (E : Type u) [Group E] [Finite E] (hE : Nat.card E = p + 1)
    (K : Subgroup (MulAut E)) (hK : Nat.card K = p)
    (automorphism : MulAut E)
    (hnormalizer : automorphism ∈ Subgroup.normalizer (K : Set (MulAut E)))
    (hne : automorphism ≠ 1) :
    Nat.card (automorphism.toMonoidHom.eqLocus (MonoidHom.id E)) ≤ 2 := by
  classical
  let _ := Fintype.ofFinite E
  obtain ⟨witness, hwitness⟩ : ∃ witness : E, ∀ element : E,
      automorphism element = element → element = 1 ∨ element = witness := by
    by_cases hexists : ∃ element : E, element ≠ 1 ∧ automorphism element = element
    · obtain ⟨witness, hneone, hfixed⟩ := hexists
      refine ⟨witness, fun element helement => ?_⟩
      by_cases hone : element = 1
      · exact Or.inl hone
      · exact Or.inr (fixed_nonidentity_unique p hp E hE K hK automorphism
          hnormalizer hne element witness hone hneone helement hfixed)
    · refine ⟨1, fun element helement => Or.inl ?_⟩
      by_contra hone
      exact hexists ⟨element, hone, helement⟩
  let fixed := automorphism.toMonoidHom.eqLocus (MonoidHom.id E)
  change Nat.card fixed ≤ 2
  have hcard : Nat.card fixed = (fixed : Set E).toFinset.card := by
    rw [Set.toFinset_card]
    exact Nat.card_eq_fintype_card
  rw [hcard]
  apply (Finset.card_le_card (t := {1, witness}) ?_).trans Finset.card_le_two
  intro element hmember
  have hmem : element ∈ fixed := Set.mem_toFinset.mp hmember
  have hfixed : automorphism element = element := hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hwitness element hfixed
