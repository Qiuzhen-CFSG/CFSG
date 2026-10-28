module

public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Construction.Coordinates
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Construction.Singular
public import BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.GroupTheory.IsPerfect

/-!
# The Hermitian five-point quadratic action comparison

Transport the Hermitian SL₂(4) action through the explicit quadratic
coordinates on the five-point core. Every transported operator permutes the
five nonzero singular vectors, and their spanning property identifies that
permutation's action on the whole module. Faithfulness of the Hermitian
action makes the resulting homomorphism injective. Perfectness puts its
image in A₅; the SL₂ order formula and |A₅| = 60 give surjectivity.

The resulting `comparison` fills the published contract without extra
premises. It retains the actual Hermitian action, the determinant quadratic
form, and hence the previously chosen minus form through
`Comparison.minus_form`. It supplies the five-point identification in
Aschbacher–Smith, K.3.1.2, printed p.454, using the core/natural-module
conventions of B.3, pp.83–84.
-/

public noncomputable section
namespace Representation.OrthogonalFourMinus.FivePoint.Construction
open FiniteModel HermitianEquiv BinaryPermutation

local instance : Algebra (ZMod 2) (fixedField 1) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space 1) :=
  Module.compHom (Space 1) (algebraMap (ZMod 2) (fixedField 1))

private abbrev Actor := Matrix.SpecialLinearGroup (Fin 2) (Field 1)

private def transported (g : Actor) : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5) :=
  coordinates.symm.trans
    ((LinearEquiv.ofBijective (SL2.BinarySmall.hermitian 1 g)
      ((SL2.BinarySmall.hermitian 1).apply_bijective g)).trans coordinates)

private lemma transported_form (g : Actor) (w : core (Fin 5)) :
    FiveGeometry.form (transported g w) = FiveGeometry.form w := by
  change FiveGeometry.form (coordinates (SL2.BinarySmall.hermitian 1 g (coordinates.symm w))) = _
  apply (algebraMap (ZMod 2) (fixedField 1)).injective
  rw [← coordinates_form]
  change form 1 (action 1 g (coordinates.symm w)) = _
  rw [form_preserved, coordinates_form, LinearEquiv.apply_symm_apply]

private def permutation (g : Actor) : Equiv.Perm (Fin 5) :=
  (exists_permutation_of_isometry (transported g) (transported_form g)).choose

private lemma permutation_intertwines (g : Actor) (v : Space 1) :
    coordinates (SL2.BinarySmall.hermitian 1 g v) =
      coreRepresentation (Fin 5) (permutation g) (coordinates v) := by
  have h := (exists_permutation_of_isometry (transported g)
    (transported_form g)).choose_spec (coordinates v)
  change coordinates (SL2.BinarySmall.hermitian 1 g (coordinates.symm (coordinates v))) = _ at h
  simpa only [LinearEquiv.symm_apply_apply, permutation] using h

private def permutationHom : Actor →* Equiv.Perm (Fin 5) where
  toFun := permutation
  map_one' := by
    apply core_permutation_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := coordinates.surjective w
    rw [← permutation_intertwines]
    simp
  map_mul' g h := by
    apply core_permutation_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := coordinates.surjective w
    rw [map_mul, Module.End.mul_apply, ← permutation_intertwines,
      ← permutation_intertwines, ← permutation_intertwines, map_mul, Module.End.mul_apply]

private lemma permutationHom_injective : Function.Injective permutationHom := by
  intro g h he
  apply action_injective 1
  apply LinearMap.ext
  intro v
  apply coordinates.injective
  change coordinates (SL2.BinarySmall.hermitian 1 g v) =
    coordinates (SL2.BinarySmall.hermitian 1 h v)
  rw [permutation_intertwines, permutation_intertwines]
  exact congrArg (fun p => coreRepresentation (Fin 5) p (coordinates v)) he

private lemma permutation_even (g : Actor) : permutationHom g ∈ alternatingGroup (Fin 5) := by
  let : Group.IsPerfect Actor := ⟨sl2_commutator_eq_top 1⟩
  let sign : Actor →* ℤˣ := Equiv.Perm.sign.comp permutationHom
  let : Group.IsPerfect sign.range := Group.IsPerfect.range sign
  apply Equiv.Perm.mem_alternatingGroup.mpr
  exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict g) 1)

private def alternatingHom : Actor →* alternatingGroup (Fin 5) :=
  permutationHom.codRestrict _ permutation_even

private lemma alternatingHom_bijective : Function.Bijective alternatingHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fun g h he => permutationHom_injective (congrArg Subtype.val he), ?_⟩
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) (Field 1)) = _
  have hc : Nat.card (Field 1) = 4 := GaloisField.card 2 2 (by decide)
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    hc, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The Hermitian action over GF(4), with its determinant, is the actual
five-point alternating action on the binary augmentation core. -/
def comparison : Comparison where
  groupEquiv := MulEquiv.ofBijective alternatingHom alternatingHom_bijective
  coordinates := coordinates
  intertwines := permutation_intertwines
  preserves_form := coordinates_form

end Representation.OrthogonalFourMinus.FivePoint.Construction
