import Submission.FeitThompson.Representation.CharacterValues
import Submission.FeitThompson.Representation.Divisibility
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int

/-!
# Central-character preliminaries for ordinary `2`-blocks

The ordinary central character of an irreducible representation takes its
values in the same cyclotomic integer ring as the character itself.  This is
the integrality bridge needed to define ordinary blocks by congruence of
central characters modulo a prime above `2`.
-/

noncomputable section

namespace Submission.ZStar

namespace BlockPreliminaries

open scoped IntermediateField

attribute [local instance] Fintype.ofFinite

universe u v

private lemma cyclotomicOrder_le_adjoin
    {η : ℂ} :
    Representation.cyclotomicOrder η ≤
      (IntermediateField.adjoin ℚ ({η} : Set ℂ)).toSubfield.toSubring := by
  rw [Representation.cyclotomicOrder, Subring.closure_le]
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  subst z
  exact IntermediateField.subset_adjoin ℚ ({η} : Set ℂ) (by simp)

private lemma adjoin_generator_eq_top
    {η : ℂ} :
    let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
    let ηK : K := ⟨η, IntermediateField.subset_adjoin ℚ ({η} : Set ℂ) (by simp)⟩
    IntermediateField.adjoin ℚ ({ηK} : Set K) = ⊤ := by
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  letI : Algebra ℚ K := K.algebra'
  let ηK : K :=
    ⟨η, IntermediateField.subset_adjoin ℚ ({η} : Set ℂ) (by simp)⟩
  apply (IntermediateField.lift_inj
    (IntermediateField.adjoin ℚ ({ηK} : Set K)) (⊤ : IntermediateField ℚ K)).mp
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  change IntermediateField.adjoin ℚ (Subtype.val '' ({ηK} : Set K)) = K
  have himage : Subtype.val '' ({ηK} : Set K) = ({η} : Set ℂ) := by
    ext z
    simp [ηK]
  rw [himage]

private lemma classSumScalar_mem_adjoin
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    Representation.classSumScalar (ρ := ρ) c ∈
      IntermediateField.adjoin ℚ ({η} : Set ℂ) := by
  classical
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep c
  have hxc : x ∈ c.carrier :=
    ConjClasses.mem_carrier_iff_mk_eq.mpr hx
  rw [Representation.classSumScalar_eq_card_mul_character_div ρ c hxc]
  have hcharA : ρ.character x ∈ Representation.cyclotomicOrder η :=
    Representation.representation_character_mem_cyclotomicOrder hη ρ x
  have hdegreeA : ρ.character 1 ∈ Representation.cyclotomicOrder η :=
    Representation.representation_character_mem_cyclotomicOrder hη ρ 1
  have hAK := cyclotomicOrder_le_adjoin (η := η)
  exact K.div_mem
    (K.mul_mem (K.natCast_mem (Nat.card c.carrier)) (hAK hcharA))
    (hAK hdegreeA)

private lemma isIntegral_adjoinElement_of_isIntegral_coe
    {η z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({η} : Set ℂ))
    (hz : IsIntegral ℤ z) :
    IsIntegral ℤ
      (⟨z, hzK⟩ : IntermediateField.adjoin ℚ ({η} : Set ℂ)) := by
  rcases hz with ⟨P, hPmonic, hPzero⟩
  refine ⟨P, hPmonic, ?_⟩
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  change Polynomial.eval₂ (Int.castRingHom K) (⟨z, hzK⟩ : K) P = 0
  apply Subtype.ext
  change K.val.toRingHom
    (Polynomial.eval₂ (Int.castRingHom K) (⟨z, hzK⟩ : K) P) = 0
  exact (Polynomial.ringHom_eval₂_intCastRingHom P K.val.toRingHom
    (⟨z, hzK⟩ : K)).trans (by simpa using hPzero)

private lemma intAdjoin_coe_mem_cyclotomicOrder
    {η : ℂ}
    (K := IntermediateField.adjoin ℚ ({η} : Set ℂ))
    (ηK : K) (hηK : (ηK : ℂ) = η)
    (z : Algebra.adjoin ℤ ({ηK} : Set K)) :
    ((z : K) : ℂ) ∈ Representation.cyclotomicOrder η := by
  let A := Representation.cyclotomicOrder η
  refine Algebra.adjoin_induction
    (p := fun x _hx => ((x : K) : ℂ) ∈ A) ?_ ?_ ?_ ?_ z.property
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simpa [hηK] using Representation.eta_mem_cyclotomicOrder η
  · intro m
    simpa using Representation.intCast_mem_cyclotomicOrder η m
  · intro x y _hx _hy hxA hyA
    simpa using A.add_mem hxA hyA
  · intro x y _hx _hy hxA hyA
    simpa using A.mul_mem hxA hyA

private def cyclotomicOrderSubalgebra (η : ℂ) : Subalgebra ℤ ℂ where
  carrier := Representation.cyclotomicOrder η
  zero_mem' := (Representation.cyclotomicOrder η).zero_mem
  add_mem' := (Representation.cyclotomicOrder η).add_mem
  one_mem' := (Representation.cyclotomicOrder η).one_mem
  mul_mem' := (Representation.cyclotomicOrder η).mul_mem
  algebraMap_mem' := by
    intro z
    exact Representation.intCast_mem_cyclotomicOrder η z

private lemma cyclotomicOrderSubalgebra_integral
    {η : ℂ} (hη : IsIntegral ℤ η) :
    Algebra.IsIntegral ℤ (cyclotomicOrderSubalgebra η) := by
  let B := Algebra.adjoin ℤ ({η} : Set ℂ)
  letI : Algebra.IsIntegral ℤ B :=
    Algebra.IsIntegral.adjoin (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact IsIntegral.algebraMap hη)
  have hBA : B = cyclotomicOrderSubalgebra η := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      change η ∈ Representation.cyclotomicOrder η
      exact Representation.eta_mem_cyclotomicOrder η
    · intro z hz
      change z ∈ Subring.closure ({η} : Set ℂ) at hz
      have hle : Subring.closure ({η} : Set ℂ) ≤ B.toSubring := by
        apply Subring.closure_le.mpr
        intro x hx
        exact Algebra.subset_adjoin hx
      exact hle hz
  let e : B ≃ₐ[ℤ] cyclotomicOrderSubalgebra η :=
    Subalgebra.equivOfEq B (cyclotomicOrderSubalgebra η) hBA
  exact (e.isIntegral_iff).mp inferInstance

private lemma cyclotomicOrder_integral
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G)) :
    Algebra.IsIntegral ℤ (Representation.cyclotomicOrder η) := by
  letI : Algebra.IsIntegral ℤ (cyclotomicOrderSubalgebra η) :=
    cyclotomicOrderSubalgebra_integral (hη := hη.isIntegral (Nat.card_pos (α := G)))
  let e : cyclotomicOrderSubalgebra η ≃ₐ[ℤ]
      Representation.cyclotomicOrder η :=
    { toFun := fun z => ⟨z, z.2⟩
      invFun := fun z => ⟨z, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  apply Algebra.IsIntegral.mk
  intro z
  let z' : cyclotomicOrderSubalgebra η := ⟨z, z.2⟩
  have hz' : IsIntegral ℤ z' :=
    Algebra.IsIntegral.isIntegral z'
  simpa [e, z'] using hz'.map e

/-- A maximal ideal of `ℤ[η]` lying above the prime `2`. -/
theorem exists_maximalIdeal_above_two
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G)) :
    ∃ P : Ideal (Representation.cyclotomicOrder η),
      P.IsMaximal ∧ P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  letI : Algebra.IsIntegral ℤ (Representation.cyclotomicOrder η) :=
    cyclotomicOrder_integral hη
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (Ideal.span ({(2 : ℤ)} : Set ℤ))

/-- The scalar by which a conjugacy-class sum acts in an irreducible complex
representation belongs to the cyclotomic integer ring generated by a
primitive `|G|`-th root of unity. -/
theorem classSumScalar_mem_cyclotomicOrder
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    Representation.classSumScalar (ρ := ρ) c ∈
      Representation.cyclotomicOrder η := by
  classical
  let n := Nat.card G
  have hn : n ≠ 0 := (Nat.card_pos (α := G)).ne'
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  let ηK : K :=
    ⟨η, IntermediateField.subset_adjoin ℚ ({η} : Set ℂ) (by simp)⟩
  have hηKcoe : (ηK : ℂ) = η := rfl
  have hηK : IsPrimitiveRoot ηK n := by
    apply IsPrimitiveRoot.of_map_of_injective (f := K.val) (by simpa [n, ηK] using hη)
    exact K.val.injective
  letI : NeZero n := ⟨hn⟩
  have htopIF : IntermediateField.adjoin ℚ ({ηK} : Set K) = ⊤ := by
    exact adjoin_generator_eq_top (η := η)
  have hηKalg : IsAlgebraic ℚ ηK := by
    apply IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn)
    rw [hηK.pow_eq_one]
    exact isAlgebraic_one
  have htopAlg : Algebra.adjoin ℚ ({ηK} : Set K) = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (by
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact hηKalg) htopIF
  let e : (Algebra.adjoin ℚ ({ηK} : Set K)) ≃ₐ[ℚ] K :=
    (Subalgebra.equivOfEq _ _ htopAlg).trans Subalgebra.topEquiv
  letI hcyclAdjoin : IsCyclotomicExtension {n} ℚ
      (Algebra.adjoin ℚ ({ηK} : Set K)) :=
    hηK.adjoin_isCyclotomicExtension ℚ
  letI : IsCyclotomicExtension {n} ℚ K :=
    IsCyclotomicExtension.equiv {n} ℚ _ e
  letI : Algebra ℤ K := Ring.toIntAlgebra K
  let Aint := Algebra.adjoin ℤ ({ηK} : Set K)
  letI : IsIntegralClosure Aint ℤ K := by
    simpa [Aint] using
      (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hηK)
  let a := Representation.classSumScalar (ρ := ρ) c
  have haK : a ∈ K := by
    simpa [a, K, n] using classSumScalar_mem_adjoin hη ρ c
  let aK : K := ⟨a, haK⟩
  have haKint : IsIntegral ℤ aK :=
    isIntegral_adjoinElement_of_isIntegral_coe haK
      (Representation.classSumScalar_isIntegral ρ c)
  let aA : Aint := IsIntegralClosure.mk' Aint aK haKint
  have haA : algebraMap Aint K aA = aK :=
    IsIntegralClosure.algebraMap_mk' Aint aK haKint
  have haAcycl : (((aA : Aint) : K) : ℂ) ∈
      Representation.cyclotomicOrder η := by
    exact intAdjoin_coe_mem_cyclotomicOrder K ηK hηKcoe aA
  have hacoe : (((aA : Aint) : K) : ℂ) = a := by
    exact congrArg (fun z : K => (z : ℂ)) haA
  simpa [a, hacoe] using haAcycl

/-! ## Congruence central characters -/

/-- The scalar by which a class sum acts on an irreducible character, written
without choosing an affording representation. -/
def ordinaryCentralCharacterValue
    {G : Type u} [Group G] [Finite G]
    (χ : Representation.ClassFunction G) (c : ConjClasses G) : ℂ :=
  (Nat.card c.carrier : ℂ) * χ c /
    χ (ConjClasses.mk (1 : G))

theorem ordinaryCentralCharacterValue_mem_cyclotomicOrder
    {G : Type u} [Group G] [Finite G]
    {χ : Representation.ClassFunction G}
    (hχ : Representation.IsIrreducibleCharacter χ)
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (c : ConjClasses G) :
    ordinaryCentralCharacterValue χ c ∈ Representation.cyclotomicOrder η := by
  classical
  rcases hχ.1 with ⟨n, ρ, hρχ⟩
  have hρirr : Representation.IsIrreducible ρ := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρχ] using hχ.2
  letI : Representation.IsIrreducible ρ := hρirr
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep c
  have hxc : x ∈ c.carrier := ConjClasses.mem_carrier_iff_mk_eq.mpr hx
  have hscalar := classSumScalar_mem_cyclotomicOrder hη ρ c
  have hscalar_eq := Representation.classSumScalar_eq_card_mul_character_div ρ c hxc
  have hchar_eq : χ c = ρ.character x := by
    rw [hρχ, ← hx]
    rfl
  have hdegree_eq : χ (ConjClasses.mk (1 : G)) = ρ.character 1 := by
    rw [hρχ]
    rfl
  rw [ordinaryCentralCharacterValue, hchar_eq, hdegree_eq]
  rw [← hscalar_eq]
  exact hscalar

/-- The order-valued ordinary central character. -/
def centralCharacterInCyclotomicOrder
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (χ : Representation.ClassFunction G)
    (hχ : Representation.IsIrreducibleCharacter χ)
    (c : ConjClasses G) : Representation.cyclotomicOrder η :=
  ⟨ordinaryCentralCharacterValue χ c,
    ordinaryCentralCharacterValue_mem_cyclotomicOrder hχ hη c⟩

/-- The reduction of a central character modulo an ideal of the cyclotomic
order. -/
def reducedCentralCharacter
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ : Representation.ClassFunction G)
    (hχ : Representation.IsIrreducibleCharacter χ) :
    ConjClasses G → (Representation.cyclotomicOrder η) ⧸ P :=
  fun c => Ideal.Quotient.mk P (centralCharacterInCyclotomicOrder hη χ hχ c)

/-- Two irreducible ordinary characters lie in the same congruence block when
all of their central-character values have the same reduction modulo `P`. -/
def SameTwoBlock
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ ψ : Representation.ClassFunction G)
    (hχ : Representation.IsIrreducibleCharacter χ)
    (hψ : Representation.IsIrreducibleCharacter ψ) : Prop :=
  reducedCentralCharacter hη P χ hχ = reducedCentralCharacter hη P ψ hψ

theorem sameTwoBlock_iff
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ ψ : Representation.ClassFunction G)
    (hχ : Representation.IsIrreducibleCharacter χ)
    (hψ : Representation.IsIrreducibleCharacter ψ) :
    SameTwoBlock hη P χ ψ hχ hψ ↔
      ∀ c : ConjClasses G,
        centralCharacterInCyclotomicOrder hη χ hχ c -
          centralCharacterInCyclotomicOrder hη ψ hψ c ∈ P := by
  constructor
  · intro h c
    exact Ideal.Quotient.eq.mp (congrFun h c)
  · intro h
    funext c
    exact Ideal.Quotient.eq.mpr (h c)

theorem sameTwoBlock_refl
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ : Representation.ClassFunction G)
    (hχ : Representation.IsIrreducibleCharacter χ) :
    SameTwoBlock hη P χ χ hχ hχ := rfl

theorem sameTwoBlock_symm
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    {χ ψ : Representation.ClassFunction G}
    {hχ : Representation.IsIrreducibleCharacter χ}
    {hψ : Representation.IsIrreducibleCharacter ψ}
    (h : SameTwoBlock hη P χ ψ hχ hψ) :
    SameTwoBlock hη P ψ χ hψ hχ := h.symm

theorem sameTwoBlock_trans
    {G : Type u} [Group G] [Finite G]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    {χ ψ φ : Representation.ClassFunction G}
    {hχ : Representation.IsIrreducibleCharacter χ}
    {hψ : Representation.IsIrreducibleCharacter ψ}
    {hφ : Representation.IsIrreducibleCharacter φ}
    (h₁ : SameTwoBlock hη P χ ψ hχ hψ)
    (h₂ : SameTwoBlock hη P ψ φ hψ hφ) :
    SameTwoBlock hη P χ φ hχ hφ := h₁.trans h₂

/-- The congruence block of a chosen member of a finite irreducible-character
family. -/
def ordinaryTwoBlock
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ : I → Representation.ClassFunction G)
    (hχ : ∀ i, Representation.IsIrreducibleCharacter (χ i))
    (base : I) : Finset I := by
  classical
  exact Finset.univ.filter fun i => SameTwoBlock hη P (χ i) (χ base) (hχ i) (hχ base)

@[simp] theorem mem_ordinaryTwoBlock_iff
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ : I → Representation.ClassFunction G)
    (hχ : ∀ i, Representation.IsIrreducibleCharacter (χ i))
    (base i : I) :
    i ∈ ordinaryTwoBlock hη P χ hχ base ↔
      SameTwoBlock hη P (χ i) (χ base) (hχ i) (hχ base) := by
  classical
  simp [ordinaryTwoBlock]

@[simp] theorem base_mem_ordinaryTwoBlock
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (P : Ideal (Representation.cyclotomicOrder η))
    (χ : I → Representation.ClassFunction G)
    (hχ : ∀ i, Representation.IsIrreducibleCharacter (χ i))
    (base : I) :
    base ∈ ordinaryTwoBlock hη P χ hχ base := by
  rw [mem_ordinaryTwoBlock_iff]
  exact sameTwoBlock_refl hη P (χ base) (hχ base)

theorem two_mem_of_liesOver
    {η : ℂ} (P : Ideal (Representation.cyclotomicOrder η))
    (hP : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))) :
    (2 : Representation.cyclotomicOrder η) ∈ P := by
  letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hP
  apply (Ideal.mem_of_liesOver P (Ideal.span ({(2 : ℤ)} : Set ℤ)) 2).mp
  exact Ideal.subset_span (by simp)

theorem two_eq_zero_mod_liesOver
    {η : ℂ} (P : Ideal (Representation.cyclotomicOrder η))
    (hP : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))) :
    Ideal.Quotient.mk P (2 : Representation.cyclotomicOrder η) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (two_mem_of_liesOver P hP)

end BlockPreliminaries

end Submission.ZStar
