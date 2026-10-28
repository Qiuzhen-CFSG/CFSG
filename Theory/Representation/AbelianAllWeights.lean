module

public import Theory.Representation.AbelianWeightDecomposition
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# All occurring character weights

A finite abelian representation in cross characteristic over an algebraically
closed field is the sum of its simultaneous character eigenspaces, including
the trivial character. Distinct weights are independent, so the number of
nonzero weight spaces is at most the dimension. This extends the nontrivial-weight
interface without imposing vanishing of invariants.

The proof uses the separable annihilator `X^|K| - 1` and Mathlib's simultaneous
eigenspace decomposition. This is the weight-space input to Aschbacher–Smith,
Lemma A.3.21(c), printed pp. 55–56.
-/

namespace Representation

open Polynomial
open scoped IsMulCommutative

variable {E K V : Type*} [Field E] [Group K]
  [AddCommGroup V] [Module E V]

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

public section

/-- The simultaneous eigenspace of a unit-valued character. -/
@[expose] def characterWeightSpace (sigma : Representation E K V) (chi : K →* Eˣ) :
    Submodule E V :=
  ⨅ k, Module.End.eigenspace (sigma k) (chi k : E)

/-- The occurring characters, including the trivial character when it occurs. -/
abbrev CharacterWeight (sigma : Representation E K V) :=
  {chi : K →* Eˣ // sigma.characterWeightSpace chi ≠ ⊥}

variable [IsMulCommutative K] [FiniteDimensional E V] [IsAlgClosed E]

omit [FiniteDimensional E V] [IsAlgClosed E] in
/-- Distinct simultaneous character spaces are independent. -/
theorem characterWeightSpace_independent (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) : iSupIndep sigma.characterWeightSpace := by
  have hcomm : ∀ a b, Commute (sigma a) (sigma b) := by
    intro a b
    change sigma a * sigma b = sigma b * sigma a
    simp [← map_mul, mul_comm]
  have hmaps : ∀ a b c, Set.MapsTo (sigma a)
      (Module.End.maxGenEigenspace (sigma b) c)
      (Module.End.maxGenEigenspace (sigma b) c) := by
    intro a b c
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) c
  have heq : ∀ k c, Module.End.maxGenEigenspace (sigma k) c =
      Module.End.eigenspace (sigma k) c := by
    intro k c
    exact (weight_semisimple sigma horder k).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace c
  have hind : iSupIndep (fun w : K → E => ⨅ k, Module.End.eigenspace (sigma k) (w k)) := by
    simpa only [heq] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo sigma hmaps
  apply hind.comp (f := fun chi : K →* Eˣ => fun k => (chi k : E))
  intro a b h
  exact MonoidHom.ext fun k => Units.ext (congr_fun h k)

/-- All the occurring character spaces together span the representation. -/
theorem iSup_characterWeightSpace_eq_top (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) :
    (⨆ chi : sigma.CharacterWeight, sigma.characterWeightSpace chi.val) = ⊤ := by
  have hcomm : ∀ a b, Commute (sigma a) (sigma b) := by
    intro a b
    change sigma a * sigma b = sigma b * sigma a
    simp [← map_mul, mul_comm]
  have heq : ∀ k c, Module.End.maxGenEigenspace (sigma k) c =
      Module.End.eigenspace (sigma k) c := by
    intro k c
    exact (weight_semisimple sigma horder k).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace c
  have htop : (⨆ w : K → E, ⨅ k, Module.End.eigenspace (sigma k) (w k)) = ⊤ := by
    have hsingle : ∀ k, ⨆ c, Module.End.maxGenEigenspace (sigma k) c = ⊤ := by
      intro k
      simpa only [heq] using (weight_semisimple sigma horder k).iSup_eigenspace_eq_top
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        sigma (fun a b _ => hcomm a b) hsingle
  apply top_unique
  rw [← htop]
  refine iSup_le fun w => ?_
  by_cases hw : (⨅ k, Module.End.eigenspace (sigma k) (w k)) = ⊥
  · simp [hw]
  obtain ⟨chi, hchi⟩ := weight_character sigma w hw
  have hn : sigma.characterWeightSpace chi ≠ ⊥ := by
    simpa only [characterWeightSpace, hchi] using hw
  simpa only [characterWeightSpace, hchi] using
    (le_iSup (fun chi : sigma.CharacterWeight => sigma.characterWeightSpace chi.val) ⟨chi, hn⟩)

omit [IsAlgClosed E] in
/-- There are at most as many occurring characters as dimensions. -/
theorem characterWeight_card_le (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) :
    Finite sigma.CharacterWeight ∧ Nat.card sigma.CharacterWeight ≤ Module.finrank E V := by
  let := (characterWeightSpace_independent sigma horder).fintypeNeBotOfFiniteDimensional
  exact ⟨inferInstance, by
    simpa only [Nat.card_eq_fintype_card] using
      (characterWeightSpace_independent sigma horder).subtype_ne_bot_le_finrank⟩

end
end Representation
