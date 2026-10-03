module

public import Theory.Character.ModularBlock.QuotientRepresentation
public import Theory.Character.Inflation
public import Theory.GroupTheory.ConjugacyQuotientCounts

/-!
# Ordinary principal blocks through an odd normal quotient

Inflation identifies the actual principal congruence blocks of a finite group
and its quotient by an odd normal subgroup, at the prescribed cyclotomic root
and contracted prime. This gives an equivalence of their ordinary principal
characters preserving values under inflation.

For an inflated character, its central-character value minus the class size
is the corresponding quotient error multiplied by an integer class-fiber
multiplicity. Conversely, summing these errors over all classes above a fixed
quotient class gives the quotient error multiplied by the kernel order. That
odd order reduces to one modulo the prime above two. Contraction of the actual
prime therefore proves both directions of block membership. Ordinary descent
through the odd normal subgroup and irreducibility under inflation then give
the bijection, using completeness and injectivity of the character families.

This is the ordinary block comparison for odd normal quotients in Feit,
*The Representation Theory of Finite Groups*, III.2.13. Individual class-fiber
multiplicities are not assumed odd. The elementary counting identities live in
`Theory.GroupTheory.ConjugacyQuotientCounts`; the ideal argument below retains
the actual coefficient places throughout.
-/

public section

open scoped BigOperators
noncomputable section
namespace ModularBlock.OrdinaryOddQuotient
open PrincipalBlockConstruction BlockPreliminaries CompatibleLocalBlock
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G]

private def centralError (d : PrincipalCongruenceBlockData G) (i : d.I)
    (c : ConjClasses G) : cyclotomicOrder d.eta :=
  centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) (d.complete.1 i) c -
    (Nat.card c.carrier : cyclotomicOrder d.eta)

private theorem centralError_coe (d : PrincipalCongruenceBlockData G) (i : d.I)
    (c : ConjClasses G) :
    (centralError d i c : ℂ) =
      (Nat.card c.carrier : ℂ) * (d.chi i c / d.chi i (ConjClasses.mk 1) - 1) := by
  change (Nat.card c.carrier : ℂ) * d.chi i c / d.chi i (ConjClasses.mk 1) -
    (Nat.card c.carrier : ℂ) = _
  ring

private theorem mem_block_iff_centralError (d : PrincipalCongruenceBlockData G) (i : d.I) :
    i ∈ d.block ↔ ∀ c, centralError d i c ∈ d.primeIdeal := by
  rw [d.mem_block_iff, sameTwoBlock_iff]
  have hprincipal (c : ConjClasses G) :
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi d.principal)
        (d.complete.1 d.principal) c = (Nat.card c.carrier : cyclotomicOrder d.eta) := by
    apply Subtype.ext
    change ordinaryCentralCharacterValue (d.chi d.principal) c = _
    simp [ordinaryCentralCharacterValue, d.principal_eq]
  simp only [centralError, hprincipal]

variable {H : Type*} [Group H] [Finite H]

private theorem centralError_inflation (d : PrincipalCongruenceBlockData G)
    (q : PrincipalCongruenceBlockData H) (f : G →* H) (hf : Function.Surjective f)
    (inclusion : cyclotomicOrder q.eta →+* cyclotomicOrder d.eta)
    (hinclusion : ∀ a, (inclusion a : ℂ) = (a : ℂ))
    (i : d.I) (j : q.I) (hchi : d.chi i = q.chi j ∘ ConjClasses.map f)
    (c : ConjClasses G) :
    ∃ m : ℕ, centralError d i c = m * inclusion (centralError q j (ConjClasses.map f c)) := by
  obtain ⟨m, hm⟩ := ConjClasses.card_map_carrier_dvd f hf c
  refine ⟨m, ?_⟩
  apply Subtype.ext
  change (centralError d i c : ℂ) = (m : ℂ) * (inclusion _ : ℂ)
  rw [hinclusion, centralError_coe, centralError_coe, hchi, hm]
  simp only [Function.comp_apply, Nat.cast_mul]
  have hone : ConjClasses.map f (ConjClasses.mk 1) = ConjClasses.mk 1 := by
    change ConjClasses.mk (f 1) = _
    rw [map_one]
  rw [hone]
  ring

private theorem sum_centralError_fiber (d : PrincipalCongruenceBlockData G)
    (q : PrincipalCongruenceBlockData H) (f : G →* H) (hf : Function.Surjective f)
    (inclusion : cyclotomicOrder q.eta →+* cyclotomicOrder d.eta)
    (hinclusion : ∀ a, (inclusion a : ℂ) = (a : ℂ))
    (i : d.I) (j : q.I) (hchi : d.chi i = q.chi j ∘ ConjClasses.map f)
    (k : ConjClasses H) :
    (∑ c : ConjClasses G, if ConjClasses.map f c = k then centralError d i c else 0) =
      (Nat.card f.ker : cyclotomicOrder d.eta) * inclusion (centralError q j k) := by
  have hone : ConjClasses.map f (ConjClasses.mk 1) = ConjClasses.mk 1 := by
    change ConjClasses.mk (f 1) = _
    rw [map_one]
  have hcard : (∑ c : ConjClasses G,
      if ConjClasses.map f c = k then (Nat.card c.carrier : ℂ) else 0) =
      (Nat.card f.ker : ℂ) * (Nat.card k.carrier : ℂ) := by
    exact_mod_cast ConjClasses.sum_card_map_fiber f hf k
  apply Subtype.ext
  change (cyclotomicOrder d.eta).subtype _ = (Nat.card f.ker : ℂ) * (inclusion _ : ℂ)
  rw [map_sum, hinclusion, centralError_coe]
  calc
    _ = ∑ c : ConjClasses G,
        (if ConjClasses.map f c = k then (Nat.card c.carrier : ℂ) else 0) *
          (q.chi j k / q.chi j (ConjClasses.mk 1) - 1) := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : ConjClasses.map f c = k
      · simp only [hc, if_true]
        change (centralError d i c : ℂ) = _
        rw [centralError_coe, hchi]
        simp only [Function.comp_apply, hc, hone]
      · simp only [hc, if_false, map_zero, zero_mul]
    _ = _ := by rw [← Finset.sum_mul, hcard]; ring

private theorem mem_of_odd_mul_mem {R : Type*} [CommRing R]
    (P : Ideal R) (htwo : (2 : R) ∈ P) {n : ℕ} (hn : Odd n)
    {x : R} (hx : (n : R) * x ∈ P) : x ∈ P := by
  have hn' : (n : R ⧸ P) = 1 :=
    natCast_eq_one_of_odd_of_two_eq_zero hn (by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr htwo)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  simpa only [map_mul, map_natCast, hn', one_mul] using h

private theorem errors_mem_iff
    {R S A B : Type*} [CommRing R] [CommRing S] [Fintype A]
    (P : Ideal R) (Q : Ideal S) (inc : S →+* R) (hQ : Q = P.comap inc)
    (F : A → B) [DecidableEq B] (v : A → R) (w : B → S)
    (n : ℕ) (hn : Odd n) (htwo : (2 : R) ∈ P)
    (hmul : ∀ a, ∃ m : ℕ, v a = m * inc (w (F a)))
    (hsum : ∀ b, (∑ a : A, if F a = b then v a else 0) = (n : R) * inc (w b)) :
    (∀ a, v a ∈ P) ↔ ∀ b, w b ∈ Q := by
  constructor
  · intro hv b
    rw [hQ]
    change inc (w b) ∈ P
    apply mem_of_odd_mul_mem P htwo hn
    rw [← hsum b]
    apply Ideal.sum_mem
    intro a _
    split_ifs
    · exact hv a
    · exact P.zero_mem
  · intro hw a
    obtain ⟨m, hm⟩ := hmul a
    rw [hm]
    apply Ideal.mul_mem_left
    have h := hw (F a)
    rwa [hQ] at h

private theorem mem_block_iff_of_surjective (d : PrincipalCongruenceBlockData G)
    (q : PrincipalCongruenceBlockData H) (f : G →* H) (hf : Function.Surjective f)
    (inclusion : cyclotomicOrder q.eta →+* cyclotomicOrder d.eta)
    (hinclusion : ∀ a, (inclusion a : ℂ) = (a : ℂ))
    (hprime : q.primeIdeal = d.primeIdeal.comap inclusion)
    (hker : Odd (Nat.card f.ker))
    (i : d.I) (j : q.I) (hchi : d.chi i = q.chi j ∘ ConjClasses.map f) :
    i ∈ d.block ↔ j ∈ q.block := by
  exact (mem_block_iff_centralError d i).trans ((errors_mem_iff
    d.primeIdeal q.primeIdeal inclusion hprime (ConjClasses.map f)
    (centralError d i) (centralError q j) (Nat.card f.ker) hker
    (two_mem_of_liesOver d.primeIdeal d.primeIdeal_liesOverTwo)
    (centralError_inflation d q f hf inclusion hinclusion i j hchi)
    (sum_centralError_fiber d q f hf inclusion hinclusion i j hchi)).trans
    (mem_block_iff_centralError q j).symm)

private theorem orderInclusion_coe {eta xi : ℂ} (hxi : xi ∈ cyclotomicOrder eta)
    (a : cyclotomicOrder xi) : (cyclotomicOrderInclusion hxi a : ℂ) = (a : ℂ) :=
  Subring.coe_inclusion _ a

private def quotientOrderInclusion (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] :
    cyclotomicOrder (compatibleQuotientPrincipalCongruenceBlockData d N).eta →+*
      cyclotomicOrder d.eta := cyclotomicOrderInclusion (quotientRoot_mem d N)

private theorem quotientOrderInclusion_coe (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal]
    (a : cyclotomicOrder (compatibleQuotientPrincipalCongruenceBlockData d N).eta) :
    (quotientOrderInclusion d N a : ℂ) = (a : ℂ) :=
  orderInclusion_coe (quotientRoot_mem d N) a

private theorem quotientPrime_eq (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] :
    (compatibleQuotientPrincipalCongruenceBlockData d N).primeIdeal =
      d.primeIdeal.comap (quotientOrderInclusion d N) := rfl

omit [Finite G] in
private theorem odd_quotient_ker (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) :
    Odd (Nat.card (QuotientGroup.mk' N).ker) := by
  simpa only [QuotientGroup.ker_mk'] using hN

/-- Inflation identifies membership in the actual compatible principal blocks. -/
theorem mem_block_iff (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) (i : d.I)
    (j : (compatibleQuotientPrincipalCongruenceBlockData d N).I)
    (hchi : d.chi i = (compatibleQuotientPrincipalCongruenceBlockData d N).chi j ∘
      ConjClasses.map (QuotientGroup.mk' N)) :
    i ∈ d.block ↔ j ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block := by
  exact mem_block_iff_of_surjective d (compatibleQuotientPrincipalCongruenceBlockData d N)
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (quotientOrderInclusion d N) (quotientOrderInclusion_coe d N) (quotientPrime_eq d N)
    (odd_quotient_ker N hN) i j hchi

/-- Every ambient principal-block character is the inflation of a character
in the compatible quotient principal block. -/
theorem exists_quotient_mem_block (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (i : d.I) (hi : i ∈ d.block) :
    ∃ j : (compatibleQuotientPrincipalCongruenceBlockData d N).I,
      j ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block ∧
      d.chi i = (compatibleQuotientPrincipalCongruenceBlockData d N).chi j ∘
        ConjClasses.map (QuotientGroup.mk' N) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  obtain ⟨m, σ, hσ, hiσ⟩ := Cartan.exists_oddNormal_ordinary_descent d N hN i hi
  obtain ⟨j, hj⟩ := q.complete.2.1 (characterClassFunction σ)
    (isIrreducibleCharacter_characterClassFunction σ hσ)
  have hchi : d.chi i = q.chi j ∘ ConjClasses.map (QuotientGroup.mk' N) := by
    rw [hiσ, hj]
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    rfl
  exact ⟨j, (mem_block_iff d N hN i j hchi).mp hi, hchi⟩

private def blockMap (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) :
    {i // i ∈ d.block} →
      {j // j ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block} := fun i =>
  ⟨Classical.choose (exists_quotient_mem_block d N hN i.val i.property),
    (Classical.choose_spec (exists_quotient_mem_block d N hN i.val i.property)).1⟩

private theorem blockMap_spec (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) (i : {i // i ∈ d.block}) :
    d.chi i.val = (compatibleQuotientPrincipalCongruenceBlockData d N).chi
      (blockMap d N hN i).val ∘ ConjClasses.map (QuotientGroup.mk' N) :=
  (Classical.choose_spec (exists_quotient_mem_block d N hN i.val i.property)).2

private theorem blockMap_bijective (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) :
    Function.Bijective (blockMap d N hN) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  constructor
  · intro i i' heq
    apply Subtype.ext
    apply d.complete.2.2
    rw [blockMap_spec d N hN i, blockMap_spec d N hN i', heq]
  · intro j
    obtain ⟨i, hi⟩ := d.complete.2.1
      (q.chi j.val ∘ ConjClasses.map (QuotientGroup.mk' N))
      (isIrreducibleConjCharacter_comp_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (q.complete.1 j.val))
    have hib : i ∈ d.block := (mem_block_iff d N hN i j.val hi).mpr j.property
    refine ⟨⟨i, hib⟩, ?_⟩
    apply Subtype.ext
    apply q.complete.2.2
    have heq := (blockMap_spec d N hN ⟨i, hib⟩).symm.trans hi
    funext c
    obtain ⟨b, rfl⟩ := ConjClasses.map_surjective (QuotientGroup.mk'_surjective N) c
    exact congrFun heq b

/-- The actual principal ordinary characters of an odd normal quotient correspond
bijectively to those of the ambient group, by inflation at the prescribed place. -/
def blockEquiv (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) :
    {i // i ∈ d.block} ≃
      {j // j ∈ (compatibleQuotientPrincipalCongruenceBlockData d N).block} :=
  Equiv.ofBijective (blockMap d N hN) (blockMap_bijective d N hN)

/-- The principal-block equivalence preserves ordinary character values by inflation. -/
theorem blockEquiv_character (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (i : {i // i ∈ d.block}) (g : G) :
    d.chi i.val (ConjClasses.mk g) =
      (compatibleQuotientPrincipalCongruenceBlockData d N).chi (blockEquiv d N hN i).val
        (ConjClasses.mk (QuotientGroup.mk' N g)) :=
  congrFun (blockMap_spec d N hN i) (ConjClasses.mk g)

end ModularBlock.OrdinaryOddQuotient
