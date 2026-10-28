module

public import Theory.Representation.PrimeFixedPointCentralization.Defs
public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.PrimeSubgroupFixedVector
public import Theory.Representation.InvariantsBaseChange
public import Theory.Representation.NormalInvariants

/-!
# The abelian and odd extraspecial branches of the prime fixed-vector theorem

For an abelian kernel, extend scalars and use distinct character weights to
obtain a nonzero fixed vector, then descend invariants. For an extraspecial
kernel of odd prime-power order, the exceptional degree in the extraspecial
fixed-vector theorem is even and hence cannot be the odd prime actor order.

These are the two terminal branches of Aschbacher, *Finite Group Theory*,
second edition, 36.1–36.2, printed pp.193–194. The reduction of an arbitrary
prime-power kernel to these configurations is a separate obligation.
-/

open scoped IsMulCommutative TensorProduct

namespace Representation.PrimeFixedPointCentralization

/-- The Fermat exception cannot occur for an odd extraspecial kernel and
an odd prime-order actor. -/
public theorem extraspecial_fixed_vector
    {q r n : ℕ} [Fact q.Prime] (hqodd : Odd q) (hr : r.Prime) (hrodd : Odd r)
    {P A W : Type*} [Group P] [IsExtraspecial q P]
    [Group A] [IsCyclic A]
    (hP : Nat.card P = q ^ (2 * n + 1)) (hA : Nat.card A = r)
    (hqr : q ≠ r) (φ : A →* MulAut P)
    (hcent : ∀ a : A, a ≠ 1 → {z | φ a z = z} = (Subgroup.center P : Set P))
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ) :
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v := by
  have hcop : r.Coprime q := (hr.coprime_iff_not_dvd.mpr fun h =>
    hqr ((Nat.dvd_prime (Fact.out : q.Prime)).mp h |>.resolve_left hr.ne_one).symm)
  have hchar : ¬ ringChar (ZMod 2) ∣ r * q ^ (2 * n + 1) := by
    rw [ringChar.eq (ZMod 2) 2]
    exact (hrodd.mul (hqodd.pow)).not_two_dvd_nat
  have hne : r ≠ q ^ n + 1 := by
    intro heq
    have heven : Even r := heq ▸ hqodd.pow.add_odd (by decide : Odd (1 : ℕ))
    exact (Nat.not_even_iff_odd.mpr hrodd) heven
  have hnonzero := Representation.theorem_2_5_b hP hA hcop hcent hchar hne hfaith
  by_contra! h
  apply hnonzero
  ext v
  constructor
  · intro hv
    exact Set.mem_singleton_iff.mpr (by
      by_contra hv0
      obtain ⟨a, ha⟩ := h v hv0
      exact ha (hv a))
  · rintro rfl
    simp

/-- A faithful irreducible binary module for an abelian kernel and a
prime-order complement acting fixed freely has a nonzero complement-fixed vector. -/
public theorem abelian_fixed_vector
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] (hqodd : Odd q)
    {P A W : Type*} [Group P] [Finite P] [IsMulCommutative P] [Nontrivial P]
    [Group A] [Finite A] (hP : IsPGroup q P) (hA : Nat.card A = r)
    (φ : A →* MulAut P)
    (hfree : ∀ a : A, a ≠ 1 → ∀ z : P, φ a z = z → z = 1)
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ) :
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v := by
  classical
  let G := SemidirectProduct P A φ
  let B : Subgroup G := (SemidirectProduct.inl : P →* G).range
  let X : Subgroup G := (SemidirectProduct.inr : A →* G).range
  let : B.Normal := Representation.theorem_2_5_rangeInl_normal
  let : Finite G := Finite.of_equiv (P × A) SemidirectProduct.equivProd.symm
  let : IsMulCommutative B := inferInstanceAs
    (IsMulCommutative (SemidirectProduct.inl : P →* G).range)
  have hX : Nat.card X = r := by
    rw [Nat.card_congr (MonoidHom.ofInjective
      (f := (SemidirectProduct.inr : A →* G)) SemidirectProduct.inr_injective).toEquiv.symm]
    exact hA
  have hfixed : B ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    rintro g ⟨⟨z, rfl⟩, hz⟩
    have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
      (hA ▸ (Fact.out : r.Prime).one_lt)
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have he := (Subgroup.mem_centralizer_iff.mp hz)
      (SemidirectProduct.inr a) ⟨a, rfl⟩
    have he' : φ a z = z := by
      have := congrArg SemidirectProduct.left he
      change 1 * φ a z = z * φ 1 1 at this
      simpa using this
    simp [hfree a ha z he']
  have hfixB : invariants (ρ.comp B.subtype) = ⊥ := by
    by_contra hne
    have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ B hne
    obtain ⟨z, hz⟩ := exists_ne (1 : P)
    have he : ρ (SemidirectProduct.inl z) = 1 := hk ⟨z, rfl⟩
    have he' : (SemidirectProduct.inl z : G) = 1 := hfaith (by simpa using he)
    exact hz (by simpa using congrArg SemidirectProduct.left he')
  let E := AlgebraicClosure (ZMod 2)
  let σ := Representation.extendScalars E ρ
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial (E ⊗[ZMod 2] W) := Representation.extendScalars_nontrivial E ρ
  have horder : (Nat.card B : E) ≠ 0 := by
    have hcard : Nat.card B = Nat.card P :=
      Nat.card_congr Representation.theorem_2_5_rangeInlEquiv.toEquiv.symm
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hcard, hn, Nat.cast_pow]
    apply pow_ne_zero
    rw [ne_eq, CharP.cast_eq_zero_iff E 2]
    exact hqodd.not_two_dvd_nat
  have hfixBE : invariants (σ.comp B.subtype) = ⊥ := by
    change (Representation.extendScalars E (ρ.comp B.subtype)).invariants = ⊥
    rw [Representation.invariants_extendScalars_eq_baseChange_of_finite,
      hfixB, Submodule.baseChange_bot]
  have hfixXE := Representation.prime_subgroup_invariants_ne_bot_of_fixed_free
    σ B X hX hfixed horder hfixBE
  have hfixX : invariants (ρ.comp X.subtype) ≠ ⊥ := by
    intro hbot
    apply hfixXE
    change (Representation.extendScalars E (ρ.comp X.subtype)).invariants = ⊥
    rw [Representation.invariants_extendScalars_eq_baseChange_of_finite,
      hbot, Submodule.baseChange_bot]
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixX
  exact ⟨v, hv0, fun a => hv ⟨SemidirectProduct.inr a, ⟨a, rfl⟩⟩⟩


/-- The structural alternative supplies the minimal-case fixed vector.
Its existence must still be established from minimality; no such existence
is assumed by an unconditional source theorem here. -/
public theorem fixed_vector_of_structure
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hqodd : Odd q) (hrodd : Odd r) (hqr : q ≠ r)
    {P A W : Type*} [Group P] [Finite P] [Group A] [Finite A]
    (hP : IsPGroup q P) (hA : Nat.card A = r)
    (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hstructure : HasMinimalActionStructure q φ)
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ) :
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  rcases hstructure with ⟨hab, hfree⟩ | ⟨n, hextra, hcard, hcent⟩
  · let : IsMulCommutative P := hab
    let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
      (hA ▸ (Fact.out : r.Prime).one_lt)
    let : Nontrivial P := by
      rcases subsingleton_or_nontrivial P with hs | hn
      · let : Subsingleton P := hs
        obtain ⟨a, ha⟩ := exists_ne (1 : A)
        exact (ha (hφ (by ext z; exact Subsingleton.elim _ _))).elim
      · exact hn
    exact abelian_fixed_vector hqodd hP hA φ hfree ρ hfaith
  · let : IsExtraspecial q P := hextra
    exact extraspecial_fixed_vector hqodd Fact.out hrodd hcard hA hqr φ hcent ρ hfaith

end Representation.PrimeFixedPointCentralization
