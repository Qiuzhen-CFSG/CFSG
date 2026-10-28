module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.Representation.BinaryNaturalDual
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finite.GaloisField


/-!
# A symplectic natural module and its graph conjugate

The representations below use the actual four-by-four symplectic matrices.
`pair τ` is the natural representation plus its pullback along `τ`;
`binaryPair τ` restricts scalars and `derivedPair τ` restricts the acting group
to its actual commutator subgroup. Thus the binary field does not silently
identify Sp₄(2) with Sp₄(2)′.

For the constructed exceptional graph automorphism, every nonidentity element
of any of the eight root groups fixes precisely the kernel of the displayed
three-coordinate projection. Surjectivity of that projection gives binary
codimension 3n over a field of order 2ⁿ, also for every nontrivial subgroup
of a root group. Separately, a binary involution exchanging complementary
summands has fixed space equal to its displacement image and fixed codimension
equal to the dimension of either summand.

These are model calculations for Aschbacher–Smith, combined manuscript of
1 March 2004, H.7, printed pp.388–389. They do not classify all involutions
or elementary subgroups in an acting overgroup, nor assert the parameters
of H.7 before those additional arguments are supplied.
-/

@[expose] public section

open scoped Matrix
open Representation Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Representation.BinaryOffender
namespace SymplecticConjugatePair
variable {F : Type*} [Field F]
abbrev Space (F : Type*) := Vector F × Vector F
/-- Natural plus the representation conjugated by the specified automorphism. -/
noncomputable def pair (τ : MulAut (Sp F)) : Representation F (Sp F) (Space F) :=
  (symplecticNatural 2).prod ((symplecticNatural 2).comp τ.toMonoidHom)
/-- The same action on the underlying binary space, with its compatible field algebra. -/
noncomputable def binaryPair [Algebra (ZMod 2) F] (τ : MulAut (Sp F)) :
    Representation (ZMod 2) (Sp F) (Space F) := restrictScalars (pair τ)
lemma binaryPair_injective [Algebra (ZMod 2) F] (τ : MulAut (Sp F)) :
    Function.Injective (binaryPair τ) := by
  intro g h he
  apply Subtype.ext
  ext i j
  have hv := congrArg (fun f : Module.End (ZMod 2) (Space F) =>
    (f (Pi.single j 1, 0)).1 i) he
  change (g.val *ᵥ Pi.single j 1) i = (h.val *ᵥ Pi.single j 1) i at hv
  simpa [Matrix.mulVec_single] using hv

/-- Restriction to the genuine derived group, including over the binary field. -/
noncomputable def derivedPair [Algebra (ZMod 2) F] (τ : MulAut (Sp F)) :
    Representation (ZMod 2) (commutator (Sp F)) (Space F) :=
  (binaryPair τ).comp (commutator (Sp F)).subtype
variable [CharP F 2] [Finite F]
noncomputable abbrev graphPair [Algebra (ZMod 2) F] :
    Representation (ZMod 2) (Sp F) (Space F) := binaryPair graphAut

local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

/-- The three coordinates forced to vanish by each nonidentity root element. -/
def rootCoordinates (r : Fin 8) : Space F →ₗ[F] (Fin 3 → F) where
  toFun v := ![![v.1 c, v.2 c, v.2 d], ![v.1 a, v.2 a, v.2 b],
    ![v.1 d, v.2 b, v.2 c], ![v.1 b, v.2 a, v.2 d],
    ![v.1 c, v.1 d, v.2 c], ![v.1 a, v.1 b, v.2 a],
    ![v.1 b, v.1 c, v.2 d], ![v.1 a, v.1 d, v.2 b]] r
  map_add' v w := by fin_cases r <;> ext i <;> fin_cases i <;> rfl
  map_smul' t v := by fin_cases r <;> ext i <;> fin_cases i <;> rfl

omit [CharP F 2] [Finite F] in
lemma rootCoordinates_surjective (r : Fin 8) :
    Function.Surjective (rootCoordinates (F := F) r) := by
  intro z
  let e : Fin 8 → Space F := ![
    (Sum.elim ![0,0] ![z 0,0], Sum.elim ![0,0] ![z 1,z 2]),
    (Sum.elim ![z 0,0] ![0,0], Sum.elim ![z 1,z 2] ![0,0]),
    (Sum.elim ![0,0] ![0,z 0], Sum.elim ![0,z 1] ![z 2,0]),
    (Sum.elim ![0,z 0] ![0,0], Sum.elim ![z 1,0] ![0,z 2]),
    (Sum.elim ![0,0] ![z 0,z 1], Sum.elim ![0,0] ![z 2,0]),
    (Sum.elim ![z 0,z 1] ![0,0], Sum.elim ![z 2,0] ![0,0]),
    (Sum.elim ![0,z 0] ![z 1,0], Sum.elim ![0,0] ![0,z 2]),
    (Sum.elim ![z 0,0] ![0,z 1], Sum.elim ![0,z 2] ![0,0])]
  refine ⟨e r, ?_⟩
  fin_cases r <;> ext i <;> fin_cases i <;> rfl

lemma root_fixed_iff (r : Fin 8) {t : F} (ht : t ≠ 0) (v : Space F) :
    pair graphAut (rootElement r t) v = v ↔ rootCoordinates r v = 0 := by
  change (symplecticNatural 2 (rootElement r t) v.1,
    symplecticNatural 2 (graphAut (rootElement r t)) v.2) = v ↔ _
  rw [graphAut_apply, graphEnd_root]
  have ht2 : t^2 ≠ 0 := pow_ne_zero _ ht
  fin_cases r <;>
    simp [Prod.ext_iff, funext_iff, Sum.forall,
      symplecticNatural_apply, rootElement, rootMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, rootPermutation, rootParameter, rootCoordinates,
      Fin.forall_fin_succ, CharTwo.neg_eq, ht, ht2, mul_eq_zero,
      add_eq_left, add_eq_right, and_comm, and_assoc]

variable [Algebra (ZMod 2) F]
lemma root_fixedSpace (r : Fin 8) {t : F} (ht : t ≠ 0) :
    fixedSpace (graphPair (F := F)) (Subgroup.zpowers (rootElement r t)) =
      (rootCoordinates r).ker.restrictScalars (ZMod 2) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  exact root_fixed_iff r ht v

lemma root_fixedCodim (r : Fin 8) {t : F} (ht : t ≠ 0) :
    fixedCodim (graphPair (F := F)) (Subgroup.zpowers (rootElement r t)) =
      3 * Module.finrank (ZMod 2) F := by
  unfold fixedCodim
  rw [root_fixedSpace r ht]
  rw [(Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (rootCoordinates (F := F) r).ker).finrank_eq]
  rw [← Module.finrank_mul_finrank (ZMod 2) F,
    ((rootCoordinates (F := F) r).quotKerEquivOfSurjective
      (rootCoordinates_surjective r)).finrank_eq]
  simp [Nat.mul_comm]

omit [CharP F 2] in

lemma coefficient_finrank {n : ℕ} (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) F = n := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF

omit [CharP F 2] in
lemma finrank_vector {n : ℕ} (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) (Vector F) = 4*n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F]
  simp [Theory.SpecificGroups.SymplecticFour.Vector, coefficient_finrank hF, Nat.mul_comm]

omit [CharP F 2] in
lemma finrank_space {n : ℕ} (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) (Space F) = 8*n := by
  rw [Module.finrank_prod, finrank_vector hF]
  omega

lemma root_fixedCodim_of_card {n : ℕ} (hF : Nat.card F = 2^n)
    (r : Fin 8) {t : F} (ht : t ≠ 0) :
    fixedCodim (graphPair (F := F)) (Subgroup.zpowers (rootElement r t)) = 3*n := by
  rw [root_fixedCodim r ht, coefficient_finrank hF]

omit [Finite F] [Algebra (ZMod 2) F] in
lemma root_involution (r : Fin 8) {t : F} (ht : t ≠ 0) :
    orderOf (rootElement r t) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, RootSubgroup.element_add, CharTwo.add_self_eq_zero,
      RootSubgroup.element_zero]
  · intro he
    apply ht
    apply RootSubgroup.element_injective r
    rw [he, RootSubgroup.element_zero]

/-- Every nontrivial subgroup of one root group has the same fixed space. -/
lemma root_subgroup_fixedSpace (r : Fin 8) (B : Subgroup (Sp F))
    (hB : B ≤ RootSubgroup.group r) (hne : B ≠ ⊥) :
    fixedSpace (graphPair (F := F)) B =
      (rootCoordinates r).ker.restrictScalars (ZMod 2) := by
  obtain ⟨g, hg, hgone⟩ := B.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r g).mp (hB hg)
  have ht : t ≠ 0 := fun he => hgone (he ▸ RootSubgroup.element_zero r)
  ext v
  constructor
  · intro hv
    exact (root_fixed_iff r ht v).mp (hv ⟨_, hg⟩)
  · intro hv g
    obtain ⟨s, hs⟩ := (RootSubgroup.mem_group_iff r g).mp (hB g.property)
    change graphPair g.val v = v
    rw [← hs]
    by_cases hsz : s = 0
    · rw [hsz, RootSubgroup.element_zero, map_one]
      rfl
    · exact (root_fixed_iff r hsz v).mpr hv

lemma root_subgroup_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (r : Fin 8) (B : Subgroup (Sp F)) (hB : B ≤ RootSubgroup.group r) (hne : B ≠ ⊥) :
    fixedCodim (graphPair (F := F)) B = 3*n := by
  have he : fixedSpace (graphPair (F := F)) B =
      fixedSpace graphPair (Subgroup.zpowers (rootElement r (1 : F))) := by
    rw [root_subgroup_fixedSpace r B hB hne, root_fixedSpace r one_ne_zero]
  unfold fixedCodim
  rw [he]
  exact root_fixedCodim_of_card hF r one_ne_zero

end SymplecticConjugatePair

namespace SymplecticConjugatePair
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The intrinsic freeness identity for a swapping binary involution. -/
lemma swapping_fixedSpace_eq_displacement (ρ : Representation (ZMod 2) G V)
    {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : G) (hs : s^2 = 1)
    (hU : ∀ u ∈ U, ρ s u ∈ W) (hW : ∀ w ∈ W, ρ s w ∈ U) :
    fixedSpace ρ (Subgroup.zpowers s) = LinearMap.range (ρ s - LinearMap.id) := by
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (ρ s) (ρ.apply_bijective s)
  have he : ∀ v, e (e v) = v := by
    intro v
    change (ρ s * ρ s) v = v
    rw [← map_mul, ← pow_two, hs, map_one]
    rfl
  have hf : BinaryNaturalDual.fixedSpace e = fixedSpace ρ (Subgroup.zpowers s) := by
    ext v
    rw [BinaryNaturalDual.mem_fixedSpace, mem_fixedSpace_zpowers_iff]
    rfl
  rw [← hf]
  exact BinaryNaturalDual.fixedSpace_eq_displacement hUW e he hU hW

variable [FiniteDimensional (ZMod 2) V]
lemma swapping_fixedCodim (ρ : Representation (ZMod 2) G V)
    {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : G) (hs : s^2 = 1)
    (hU : ∀ u ∈ U, ρ s u ∈ W) (hW : ∀ w ∈ W, ρ s w ∈ U) :
    fixedCodim ρ (Subgroup.zpowers s) = Module.finrank (ZMod 2) W := by
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (ρ s) (ρ.apply_bijective s)
  have he : ∀ v, e (e v) = v := by
    intro v
    change (ρ s * ρ s) v = v
    rw [← map_mul, ← pow_two, hs, map_one]
    rfl
  have hf : BinaryNaturalDual.fixedSpace e = fixedSpace ρ (Subgroup.zpowers s) := by
    ext v
    rw [BinaryNaturalDual.mem_fixedSpace, mem_fixedSpace_zpowers_iff]
    rfl
  have hfixed := BinaryNaturalDual.finrank_fixedSpace hUW e he hU hW
  rw [hf] at hfixed
  have hsum := (Submodule.prodEquivOfIsCompl U W hUW).finrank_eq
  rw [Module.finrank_prod] at hsum
  have hdim := fixedCodim_add_finrank ρ (Subgroup.zpowers s)
  omega
end SymplecticConjugatePair


namespace SymplecticConjugatePair
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

abbrev firstSummand : Submodule (ZMod 2) (Space F) :=
  LinearMap.range (LinearMap.inl (ZMod 2) (Vector F) (Vector F))
abbrev secondSummand : Submodule (ZMod 2) (Space F) :=
  LinearMap.range (LinearMap.inr (ZMod 2) (Vector F) (Vector F))

lemma summands_isCompl : IsCompl (firstSummand (F := F)) secondSummand :=
  LinearMap.isCompl_range_inl_inr

lemma finrank_secondSummand :
    Module.finrank (ZMod 2) (secondSummand (F := F)) =
      Module.finrank (ZMod 2) (Vector F) := by
  exact LinearMap.finrank_range_of_inj (LinearMap.inr_injective (R := ZMod 2))

variable [Finite F]
lemma swapping_fixedCodim_of_card {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G (Space F)) {n : ℕ} (hF : Nat.card F = 2^n)
    (s : G) (hs : s^2 = 1)
    (hU : ∀ u ∈ firstSummand, ρ s u ∈ secondSummand)
    (hW : ∀ w ∈ secondSummand, ρ s w ∈ firstSummand) :
    fixedCodim ρ (Subgroup.zpowers s) = 4*n := by
  rw [swapping_fixedCodim ρ summands_isCompl s hs hU hW, finrank_secondSummand,
    finrank_vector hF]
end SymplecticConjugatePair
