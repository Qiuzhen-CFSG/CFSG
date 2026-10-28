module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Nontrivial character-weight decomposition

For a finite abelian group acting on a finite-dimensional vector space over an
algebraically closed field, invertibility of the group order makes every group
operator semisimple: it is annihilated by the separable polynomial `X^|K| - 1`.
The simultaneous eigenspace theorem therefore gives an internal decomposition
indexed by all joint eigenvalue functions. A nonzero joint eigenspace forces
its eigenvalue function to be a unit-valued multiplicative character. The
trivial character weight is exactly the invariant submodule, so an absence of
invariants leaves precisely the nontrivial character weights.

The argument uses Mathlib's simultaneous eigenspace API and does not assume
characteristic zero or irreducibility.
-/

namespace Representation

open Polynomial
open scoped IsMulCommutative

variable {E K V : Type*} [Field E] [IsAlgClosed E] [Group K]
  [IsMulCommutative K] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

private theorem weight_semisimple {E K V : Type*} [Field E] [Group K]
    [AddCommGroup V] [Module E V] (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (kernel : K) :
    Module.End.IsSemisimple (sigma kernel) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : E[X]) ^ Nat.card K - 1)
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr horder).squarefree
  · have hpow : sigma kernel ^ Nat.card K = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    simp [hpow]

private theorem weight_character {E K V : Type*} [Field E] [Group K]
    [AddCommGroup V] [Module E V] (sigma : Representation E K V) (weight : K → E)
    (hweight : (⨅ kernel, Module.End.eigenspace (sigma kernel) (weight kernel)) ≠ ⊥) :
    ∃ character : K →* Eˣ, ∀ kernel, (character kernel : E) = weight kernel := by
  obtain ⟨vector, hvector, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hweight
  have heigen : ∀ kernel, sigma kernel vector = weight kernel • vector := by
    simpa only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] using hvector
  have hone : weight 1 = 1 := by
    apply smul_left_injective E hne
    simpa using (heigen 1).symm
  have hmul : ∀ left right, weight (left * right) = weight left * weight right := by
    intro left right
    apply smul_left_injective E hne
    change weight (left * right) • vector = (weight left * weight right) • vector
    rw [← heigen (left * right), map_mul, Module.End.mul_apply, heigen right,
      map_smul, heigen left, smul_smul, mul_comm]
  have hnonzero : ∀ kernel, weight kernel ≠ 0 := by
    intro kernel hzero
    have := hmul kernel kernel⁻¹
    rw [mul_inv_cancel, hone, hzero, zero_mul] at this
    exact one_ne_zero this
  refine ⟨{ toFun := fun kernel => Units.mk0 (weight kernel) (hnonzero kernel)
            map_one' := Units.ext hone
            map_mul' := fun left right => Units.ext (hmul left right) }, ?_⟩
  intro kernel
  rfl

attribute [local instance] Classical.decEq

public theorem isInternal_nontrivial_characterWeightSpaces
    [Finite K] (sigma : Representation E K V) (horder : (Nat.card K : E) ≠ 0)
    (hfix : sigma.invariants = ⊥) :
    DirectSum.IsInternal (fun character : {character : K →* Eˣ // character ≠ 1} =>
      ⨅ kernel : K, Module.End.eigenspace (sigma kernel) (character.val kernel : E)) := by
  classical
  have hcomm : ∀ left right, Commute (sigma left) (sigma right) := by
    intro left right
    change sigma left * sigma right = sigma right * sigma left
    simp [← map_mul, mul_comm]
  have hmaps : ∀ left right eigenvalue,
      Set.MapsTo (sigma left) (Module.End.maxGenEigenspace (sigma right) eigenvalue)
        (Module.End.maxGenEigenspace (sigma right) eigenvalue) := by
    intro left right eigenvalue
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm right left) eigenvalue
  have heq : ∀ kernel eigenvalue,
      Module.End.maxGenEigenspace (sigma kernel) eigenvalue =
        Module.End.eigenspace (sigma kernel) eigenvalue := by
    intro kernel eigenvalue
    exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (weight_semisimple sigma horder kernel).isFinitelySemisimple eigenvalue
  have hind : iSupIndep (fun weight : K → E =>
      ⨅ kernel, Module.End.eigenspace (sigma kernel) (weight kernel)) := by
    simpa only [heq] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo sigma hmaps
  have htop : (⨆ weight : K → E, ⨅ kernel,
      Module.End.eigenspace (sigma kernel) (weight kernel)) = ⊤ := by
    have hsingle : ∀ kernel, ⨆ eigenvalue,
        Module.End.maxGenEigenspace (sigma kernel) eigenvalue = ⊤ := by
      intro kernel
      simpa only [heq] using (weight_semisimple sigma horder kernel).iSup_eigenspace_eq_top
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo sigma hmaps hsingle
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply hind.comp (f := fun character : {character : K →* Eˣ // character ≠ 1} =>
        fun kernel => (character.val kernel : E))
    intro left right hequal
    apply Subtype.ext
    apply MonoidHom.ext
    intro kernel
    exact Units.ext (congr_fun hequal kernel)
  · apply top_unique
    rw [← htop]
    refine iSup_le fun weight => ?_
    by_cases hweight : (⨅ kernel, Module.End.eigenspace (sigma kernel) (weight kernel)) = ⊥
    · rw [hweight]
      exact bot_le
    obtain ⟨character, hcharacter⟩ := weight_character sigma weight hweight
    have hnontrivial : character ≠ 1 := by
      intro htrivial
      apply hweight
      have hinv : (⨅ kernel, Module.End.eigenspace (sigma kernel) (weight kernel)) =
          sigma.invariants := by
        ext vector
        simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, mem_invariants]
        simp [← hcharacter, htrivial]
      exact hinv.trans hfix
    simpa only [hcharacter] using
      (le_iSup (fun character : {character : K →* Eˣ // character ≠ 1} =>
        ⨅ kernel, Module.End.eigenspace (sigma kernel) (character.val kernel : E))
        ⟨character, hnontrivial⟩)

end Representation
