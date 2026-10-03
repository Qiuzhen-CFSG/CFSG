module

public import Theory.Character.ModularBlock.BrauerCharacterBasis
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Principal-block decomposition and Cartan data

The coefficients in a decomposition matrix express restrictions of actual
ordinary irreducible characters in the eigenvalue-defined Brauer characters
of a complete family of simple modules in the principal block. Membership
in that block means that its actual reduced selector acts as the identity.
Linear independence makes these nonnegative integral coefficients unique.
The Cartan matrix is their Gram matrix, the character-theoretic definition
of Cartan invariants. In particular it is not an independently supplied matrix.

Evaluating the character decompositions at the identity and rearranging
finite sums proves the block-dimension formula `degreeᵀ * Cartan * degree`.
This is the reusable interface for the local computations in Fong,
*Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71, (6)–(7).
Existence and computation of these data are separate mathematical theorems;
this module makes no existence assumption about decomposition matrices.
-/

public section
noncomputable section

namespace ModularBlock

open scoped BigOperators
open PrincipalBlockConstruction BrauerCoefficientExtension BrauerBlockReduction

universe u
variable {G : Type u} [Group G] [Finite G]

namespace BrauerCharacter

/-- The lifted eigenvalue sum at the identity remembers the integer dimension. -/
@[simp] theorem value_one (d : PrincipalCongruenceBlockData G)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) :
    value d ρ 1 = (Module.finrank (splittingField d) V : ℂ) := by
  have hroots : (Polynomial.X - 1 : Polynomial (splittingField d)).roots = {1} := by
    simpa using Polynomial.roots_X_sub_C (1 : splittingField d)
  simp [value, integralValue, LinearMap.charpoly_one, Polynomial.roots_pow, hroots,
    Multiset.nsmul_singleton]

end BrauerCharacter

namespace Cartan

/-- The principal selector over the splitting field of the prescribed prime. -/
@[expose] def splittingSelector (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (splittingField d) G :=
  MonoidAlgebra.mapRingHom G (residueInclusion d) (reducedPrincipalBlockElement d)

/-- Block membership of an actual modular representation. -/
@[expose] def InPrincipalBlock (d : PrincipalCongruenceBlockData G)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    (ρ : Representation (splittingField d) G V) : Prop :=
  ρ.asAlgebraHom (splittingSelector d) = 1

/-- If every ordinary character is in the principal congruence block, its
actual selector is the identity, also after reduction and scalar extension. -/
theorem splittingSelector_eq_one_of_block_eq_univ
    (d : PrincipalCongruenceBlockData G) (hblock : d.block = Finset.univ) :
    splittingSelector d = 1 := by
  classical
  have hcomplex : BlockOrthogonality.principalBlockElement d = 1 := by
    ext g
    rw [BlockOrthogonality.principalBlockElement_coeff, hblock]
    have hcoeff := BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
      d.chi d.complete (1 : MonoidAlgebra ℂ G) (by simp)
      (fun _ => (1 : ℂ)) (by intros; simp) g
    simpa using hcoeff.symm
  have hlocal : BlockOrthogonality.localizedPrincipalBlockElement d = 1 := by
    apply BlockOrthogonality.localizedGroupAlgebraToComplex_injective d
    simpa only [BlockOrthogonality.principalBlockElement, map_one] using hcomplex
  simp [splittingSelector, reducedPrincipalBlockElement, hlocal]

/-- In a group with a single ordinary two-block, every modular representation
belongs to the principal block in the selector-action sense. -/
theorem inPrincipalBlock_of_block_eq_univ
    (d : PrincipalCongruenceBlockData G) (hblock : d.block = Finset.univ)
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    (ρ : Representation (splittingField d) G V) : InPrincipalBlock d ρ := by
  rw [InPrincipalBlock, splittingSelector_eq_one_of_block_eq_univ d hblock, map_one]

/-- A complete, nonredundant family of genuine irreducible modular characters
in the principal block. Matrix models cover all finite-dimensional modules. -/
structure PrincipalBrauerFamily (d : PrincipalCongruenceBlockData G) (n : ℕ) where
  degree : Fin n → ℕ
  rep : (j : Fin n) → Representation (splittingField d) G (Fin (degree j) → splittingField d)
  irreducible : ∀ j, Representation.IsIrreducible (rep j)
  inBlock : ∀ j, InPrincipalBlock d (rep j)
  complete : ∀ (m : ℕ) (ρ : Representation (splittingField d) G (Fin m → splittingField d)),
    Representation.IsIrreducible ρ → InPrincipalBlock d ρ →
      ∃ j, Nonempty (ρ.Equiv (rep j))
  independent : LinearIndependent ℂ (fun j => BrauerCharacter.character d (rep j))

namespace PrincipalBrauerFamily

variable {d : PrincipalCongruenceBlockData G} {n : ℕ}
  (b : PrincipalBrauerFamily d n)

/-- The complex space spanned by the block's irreducible Brauer characters. -/
@[expose] def characterSpace : Submodule ℂ (BrauerCharacter.TwoRegularClasses G → ℂ) :=
  Submodule.span ℂ (Set.range (fun j => BrauerCharacter.character d (b.rep j)))

/-- A genuine basis consisting of the irreducible modular characters. -/
def basis : Module.Basis (Fin n) ℂ b.characterSpace := Module.Basis.span b.independent

@[simp] theorem basis_apply (j : Fin n) :
    (b.basis j : BrauerCharacter.TwoRegularClasses G → ℂ) =
      BrauerCharacter.character d (b.rep j) :=
  Module.Basis.coe_span_apply b.independent j

/-- Completeness places the character of every simple block module in this space. -/
theorem character_mem_space (m : ℕ)
    (ρ : Representation (splittingField d) G (Fin m → splittingField d))
    (hρ : Representation.IsIrreducible ρ) (hblock : InPrincipalBlock d ρ) :
    BrauerCharacter.character d ρ ∈ b.characterSpace := by
  obtain ⟨j, ⟨e⟩⟩ := b.complete m ρ hρ hblock
  rw [BrauerCharacter.character_equiv d e]
  exact Submodule.subset_span (Set.mem_range_self j)

end PrincipalBrauerFamily

/-- The actual ordinary-to-Brauer character decompositions in a principal block. -/
structure PrincipalDecompositionData (d : PrincipalCongruenceBlockData G) (n : ℕ) where
  family : PrincipalBrauerFamily d n
  decomposition : d.I → Fin n → ℕ
  restriction : ∀ i ∈ d.block, ∀ g : G, Odd (orderOf g) →
    d.chi i (ConjClasses.mk g) =
      ∑ j, (decomposition i j : ℂ) * BrauerCharacter.value d (family.rep j) g

namespace PrincipalDecompositionData

variable {d : PrincipalCongruenceBlockData G} {n : ℕ}
  (a : PrincipalDecompositionData d n)

/-- Cartan invariants computed from the genuine decomposition coefficients. -/
@[expose] def cartan (j k : Fin n) : ℕ :=
  ∑ i ∈ d.block, a.decomposition i j * a.decomposition i k

theorem cartan_symmetric (j k : Fin n) : a.cartan j k = a.cartan k j := by
  simp only [cartan, Nat.mul_comm]

/-- Ordinary dimensions are the decomposition multiplicities weighted by
the actual dimensions of the simple modular representations. -/
theorem degree_eq (i : d.I) (hi : i ∈ d.block) :
    d.chi i (ConjClasses.mk 1) =
      ∑ j, (a.decomposition i j : ℂ) * (a.family.degree j : ℂ) := by
  simpa using a.restriction i hi 1 (by simp)

/-- The decomposition numbers are uniquely determined by the genuine
Brauer characters, rather than arbitrary choices of matrix entries. -/
theorem decomposition_unique (i : d.I) (hi : i ∈ d.block)
    (coeff : Fin n → ℕ)
    (hcoeff : ∀ g : G, Odd (orderOf g) →
      d.chi i (ConjClasses.mk g) =
        ∑ j, (coeff j : ℂ) * BrauerCharacter.value d (a.family.rep j) g) :
    a.decomposition i = coeff := by
  have hsum :
      ∑ j, (a.decomposition i j : ℂ) • BrauerCharacter.character d (a.family.rep j) =
        ∑ j, (coeff j : ℂ) • BrauerCharacter.character d (a.family.rep j) := by
    funext c
    obtain ⟨g, hg, hc⟩ := c.property
    have heq : c = BrauerCharacter.twoRegularClass g hg := Subtype.ext hc.symm
    subst c
    simpa using (a.restriction i hi g hg).symm.trans (hcoeff g hg)
  have heq := Fintype.linearIndependent_iffₛ.mp a.family.independent
    (fun j => (a.decomposition i j : ℂ)) (fun j => (coeff j : ℂ)) hsum
  funext j
  exact_mod_cast heq j

/-- The sum of squared ordinary block degrees is the Cartan quadratic form
on the degrees of the genuine irreducible Brauer characters. -/
theorem sum_degree_sq :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 =
      ∑ j, ∑ k, (a.cartan j k : ℂ) *
        (a.family.degree j : ℂ) * (a.family.degree k : ℂ) := by
  calc
    _ = ∑ i ∈ d.block, ∑ j, ∑ k,
        ((a.decomposition i j : ℂ) * (a.decomposition i k : ℂ)) *
          (a.family.degree j : ℂ) * (a.family.degree k : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [a.degree_eq i hi, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [cartan, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]

end PrincipalDecompositionData
end Cartan
end ModularBlock
