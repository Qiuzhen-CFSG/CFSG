module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Contracts
public import Theory.Character.ModularBlock.PrimeCongruenceArithmetic
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# The actual principal eleven-block of the supplied J₁ table

Choose a maximal ideal over eleven in the group-order cyclotomic order and
retain the supplied complete ordinary family, indexed by `Fin 15`. Its zero
row is the principal character. Clearing each degree prime to eleven reduces
the central-character comparison to the ordinary table: the identity gives
zero difference, column nine has character value congruent to the degree,
and every other class size is divisible by eleven.

Conversely, the four rows with degrees 77, 77, 77 and 209 vanish at column
nine. That class has size 15960, prime to eleven, so their central characters
cannot agree with the principal character. This computes membership in the
actual congruence block; the block itself is not defined by the degree test.

Source: Feit, *The Representation Theory of Finite Groups*, IV.4.2, p.150;
Janko, J. Algebra 3 (1966), 147–186. The ordinary table and its ATLAS
provenance are specified in `OrdinaryData.lean`; see `Construction/Source.md`.
-/

noncomputable section
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
open ModularBlock.BlockPreliminaries ModularBlock.PrimeBlockConstruction
open ModularBlock.PrimeCongruenceArithmetic

variable {G : Type*} [Group G] [Finite G]

private theorem class_size (d : OrdinaryData G) (horder : Nat.card G = 175560)
    (j : Fin 15) : Nat.card (d.classes j).carrier = 175560 / centralizerOrder j := by
  rw [d.classes_eq]
  have hpos : 0 < centralizerOrder j := by fin_cases j <;> decide
  have he := ConjClasses.nat_card_carrier_mul_card_centralizer (d.representatives j)
  rw [d.centralizers, horder] at he
  rw [← he, Nat.mul_div_cancel _ hpos]

private def elevenCorrection : Fin 15 → ℤ :=
  ![0, -5, -5, -7, -7, -7, -7, -7, -11, -11, -11, -12, -12, -12, -19]

private theorem columnNine_difference (x y : ℂ) (i : Fin 15) :
    ordinaryValue x y i 9 - (ordinaryDegree i : ℂ) = 11 * (elevenCorrection i : ℂ) := by
  fin_cases i <;> simp [ordinaryValue, ordinaryDegree, elevenCorrection] <;> norm_num

private theorem columnNine_zero (x y : ℂ) (i : Fin 15) (hi : 11 ∣ ordinaryDegree i) :
    ordinaryValue x y i 9 = 0 := by
  fin_cases i <;> simp_all [ordinaryDegree, ordinaryValue]

/-- Every occurrence of a supplied ordinary row has the asserted membership
in an actual prime congruence block, regardless of the chosen prime above eleven. -/
public theorem principalBlock_membership (d : OrdinaryData G) (horder : Nat.card G = 175560)
    (b : PrimeCongruenceBlockData 11 G) (i : Fin 15) (r : b.I)
    (hrow : b.chi r = d.chi i) : r ∈ b.block ↔ ¬ 11 ∣ ordinaryDegree i := by
  constructor
  · intro hr hi
    apply not_mem_block_of_vanish b r (d.classes 9) ?_ ?_ hr
    · rw [class_size d horder]
      decide +kernel
    · rw [hrow, d.values]
      exact columnNine_zero _ _ i hi
  · intro hi
    have hd : b.chi r (ConjClasses.mk 1) = (ordinaryDegree i : ℂ) := by
      rw [hrow, d.degree_value]
    apply (mem_block_iff_of_degree b r hd hi).mpr
    intro C
    obtain ⟨j, rfl⟩ := d.classes.surjective C
    by_cases hj0 : j = 0
    · subst j
      have hz : characterValue b.eta_spec (b.chi r) (b.complete.1 r).1 (d.classes 0) -
          (ordinaryDegree i : cyclotomicOrder b.eta) = 0 := by
        apply Subtype.ext
        change b.chi r (d.classes 0) - (ordinaryDegree i : ℂ) = 0
        rw [d.classes_eq, d.identity, hd, sub_self]
      rw [hz, mul_zero]
      exact b.primeIdeal.zero_mem
    by_cases hj9 : j = 9
    · subst j
      apply b.primeIdeal.mul_mem_left
      have heq : characterValue b.eta_spec (b.chi r) (b.complete.1 r).1 (d.classes 9) -
          (ordinaryDegree i : cyclotomicOrder b.eta) =
          (11 : cyclotomicOrder b.eta) * (elevenCorrection i : cyclotomicOrder b.eta) := by
        apply Subtype.ext
        change b.chi r (d.classes 9) - (ordinaryDegree i : ℂ) =
          11 * (elevenCorrection i : ℂ)
        rw [hrow, d.values, columnNine_difference]
      rw [heq]
      apply b.primeIdeal.mul_mem_right
      exact (natCast_mem_iff b.primeIdeal b.primeIdeal_liesOver 11).mpr (dvd_refl 11)
    · apply b.primeIdeal.mul_mem_right
      apply (natCast_mem_iff b.primeIdeal b.primeIdeal_liesOver _).mpr
      rw [class_size d horder]
      fin_cases j <;> simp_all [centralizerOrder]

/-- Construct the actual principal eleven-block identification from the ordinary
table and group order, with no modular or additional local-group premise. -/
public theorem exists_principalBlockIdentification (d : OrdinaryData G)
    (horder : Nat.card G = 175560) : Nonempty (Construction.PrincipalBlockIdentification d) := by
  classical
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let η := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (Nat.card G : ℂ))
  have hη : IsPrimitiveRoot η (Nat.card G) :=
    Complex.isPrimitiveRoot_exp (Nat.card G) (Nat.card_pos (α := G)).ne'
  obtain ⟨P, hPmax, hPover⟩ := exists_maximalIdeal_above_prime hη 11
  have hprincipal : d.chi 0 = ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter G := by
    ext C
    obtain ⟨j, rfl⟩ := d.classes.surjective C
    rw [d.values]
    fin_cases j <;> simp [ordinaryValue, ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter]
  let b : PrimeCongruenceBlockData 11 G := {
    I := Fin 15
    fintypeI := inferInstance
    decidableEqI := inferInstance
    chi := d.chi
    complete := d.complete
    eta := η
    eta_spec := hη
    primeIdeal := P
    primeIdeal_maximal := hPmax
    primeIdeal_liesOver := hPover
    principal := 0
    principal_eq := hprincipal }
  exact ⟨{
    data := b
    rows := Equiv.refl _
    characters := fun _ => rfl
    principal := rfl
    membership := fun i => principalBlock_membership d horder b i i rfl }⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
