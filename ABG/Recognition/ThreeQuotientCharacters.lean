module

public import ABG.Recognition.ThreeCentralizerCharacters
public import Theory.Character.ModularBlock.PrincipalQuotient

/-!
# GL₂(3) characters above a possibly nontrivial odd core

If `H/O₂′(H)` is GL₂(3), inflate its eight actual irreducible characters
to `H`. They remain distinct and have degrees `1,1,2,3,3,4,2,2`.
Every row of any principal congruence two-block of `H` occurs in this family:
the odd-core kernel theorem descends the row, and completeness of the matrix
table identifies the quotient character. In particular the local principal
block has at most eight rows. The reverse inclusion is a separate assertion.

These statements apply to involution centralizers without assuming that their
odd cores vanish. Source: ABG III.2 Proposition 7 and the GL₂(3) table in
Wong (1964), Table 1, p.97.
-/

namespace ABG
open BenderGlauberman Matrix.GeneralLinearGroup
open ModularBlock.PrincipalBlockConstruction
noncomputable section

variable {H : Type*} [Group H] [Finite H]

/-- The quotient homomorphism expressed in the concrete matrix model. -/
@[expose] public def threeOddCoreQuotientMap
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) : H →* GL (Fin 2) (ZMod 3) :=
  (e.trans glTwoThreeFieldEquiv).toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 H))

omit [Finite H] in
public theorem threeOddCoreQuotientMap_surjective
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) :
    Function.Surjective (threeOddCoreQuotientMap e) :=
  (e.trans glTwoThreeFieldEquiv).surjective.comp
    (QuotientGroup.mk'_surjective (pPrimeCore 2 H))

/-- The eight inflated characters, in the actual congruence-block convention. -/
@[expose] public def threeOddCoreCharacter
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) (i : Fin 8) : ConjClassFunction H :=
  toConjClassFunction (glTwoThreeCharacter i)
      (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i)) ∘
    ConjClasses.map (threeOddCoreQuotientMap e)

public theorem threeOddCoreCharacter_irreducible
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) (i : Fin 8) :
    IsIrreducibleConjCharacter (threeOddCoreCharacter e i) :=
  isIrreducibleConjCharacter_comp_surjective (threeOddCoreQuotientMap e)
    (threeOddCoreQuotientMap_surjective e)
    (isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19
      (glTwoThreeCharacter_irreducible i))

omit [Finite H] in
public theorem threeOddCoreCharacter_apply
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) (i : Fin 8) (h : H) :
    threeOddCoreCharacter e i (ConjClasses.mk h) =
      glTwoThreeCharacter i (threeOddCoreQuotientMap e h) := rfl

omit [Finite H] in
/-- The degrees are inherited from genuine characters of the quotient. -/
public theorem threeOddCoreCharacter_degree
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) (i : Fin 8) :
    threeOddCoreCharacter e i (ConjClasses.mk 1) =
      (![1, 1, 2, 3, 3, 4, 2, 2] i : ℂ) := by
  rw [threeOddCoreCharacter_apply, map_one]
  change glTwoThreeCharacter i (threeClassRepr 0) = _
  rw [glTwoThreeCharacter_values]
  fin_cases i <;> rfl

omit [Finite H] in
public theorem threeOddCoreCharacter_injective
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1) :
    Function.Injective (threeOddCoreCharacter e) := by
  intro i j hij
  apply glTwoThreeCharacter_injective
  funext g
  obtain ⟨h, rfl⟩ := threeOddCoreQuotientMap_surjective e g
  exact congrFun hij (ConjClasses.mk h)

/-- Every local principal-block row occurs in the inflated matrix table. -/
public theorem threeOddCoreCharacter_complete_on_principalBlock
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) {j : d.I} (hj : j ∈ d.block) :
    ∃! i : Fin 8, threeOddCoreCharacter e i = d.chi j := by
  obtain ⟨χ, hχ, he⟩ :=
    ModularBlock.PrincipalBlockKernel.exists_quotient_character_of_mem_block d hj
  let f := e.trans glTwoThreeFieldEquiv
  have hirr := isIrreducibleCharacter_comp_mulEquiv f.symm
    (isIrreducibleCharacter_ofConjClassFunctionBG19 hχ)
  obtain ⟨i, hi, _⟩ := glTwoThreeCharacter_complete hirr
  have hrow : threeOddCoreCharacter e i = d.chi j := by
    funext c
    obtain ⟨h, rfl⟩ := ConjClasses.exists_rep c
    rw [he, threeOddCoreCharacter_apply]
    change glTwoThreeCharacter i (f ((QuotientGroup.mk' (pPrimeCore 2 H)) h)) = _
    rw [hi]
    simp only [MulEquiv.symm_apply_apply]
    rfl
  exact ⟨i, hrow, fun k hk => threeOddCoreCharacter_injective e (hk.trans hrow.symm)⟩

/-- A useful upper bound before proving that all eight inflated rows belong
to the compatible principal block. -/
public theorem threeOddCore_principalBlock_card_le
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) : d.block.card ≤ 8 := by
  classical
  have hex (j : {j : d.I // j ∈ d.block}) :
      ∃ i : Fin 8, threeOddCoreCharacter e i = d.chi j.val :=
    (threeOddCoreCharacter_complete_on_principalBlock e d j.property).exists
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    apply d.complete.2.2
    exact (hf j).symm.trans ((congrArg (threeOddCoreCharacter e) hjk).trans (hf k))
  simpa using Fintype.card_le_of_injective f hinj

/-- A degree-three row exists in any complete ordinary family on `H`.
Membership in its principal block is not assumed or concluded here. -/
public theorem threeOddCore_exists_degree_three_row
    (e : (H ⧸ pPrimeCore 2 H) ≃* GL2 3 1)
    (d : PrincipalCongruenceBlockData H) :
    ∃ j : d.I, d.chi j = threeOddCoreCharacter e 3 ∧
      d.chi j (ConjClasses.mk 1) = 3 := by
  obtain ⟨j, hj⟩ := d.complete.2.1 _ (threeOddCoreCharacter_irreducible e 3)
  exact ⟨j, hj, hj ▸ threeOddCoreCharacter_degree e 3⟩

end
end ABG
