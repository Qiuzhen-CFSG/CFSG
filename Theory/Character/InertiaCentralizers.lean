module

public import Theory.Character.BrauerPermutation

/-!
# Character inertia from centralizers

Brauer permutation identifies the number of fixed irreducible characters with
that of fixed conjugacy classes. A fixed nonprincipal character therefore gives
a nonidentity fixed class. Correcting the acting element by an inner conjugation
places it in a centralizer, and hence in any subgroup containing the normal
subgroup and all its nonidentity centralizers.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.3, pp. 84–85; the Brauer permutation argument is formalized in
`Theory.Character.BrauerPermutation`.
-/

public section
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite

/-- Brauer permutation turns character inertia into a centralizer condition. -/
theorem inertia_le_of_centralizers_le
    {L : Type*} [Group L] [Finite L]
    (N M : Subgroup L) [N.Normal] (hNM : N ≤ M)
    (hc : ∀ x : N, x ≠ 1 → centralizer ({(x : L)} : Set L) ≤ M)
    {χ : ClassFunction N} (hχ : IsIrreducibleCharacter χ) (hne : χ ≠ 1)
    (g : L) (hfix : ∀ x, χ (normalSubgroupConjMulEquiv N g x) = χ x) : g ∈ M := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let τ : Representation ℂ N ℂ := Representation.trivial ℂ N ℂ
  have hτ : IsIrreducibleConjCharacter (characterClassFunction τ) :=
    isIrreducibleCharacter_characterClassFunction τ trivial_complex_irreducible
  have hρfix : classFunctionConjLinearEquiv N g (characterClassFunction ρ) =
      characterClassFunction ρ := by
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    change characterClassFunction ρ ((conjClassesConjPerm N g).symm (ConjClasses.mk x)) = _
    rw [conjClassesConjPerm_symm_mk]
    change ρ.character ((normalSubgroupConjMulEquiv N g).symm x) = ρ.character x
    simpa using (hfix ((normalSubgroupConjMulEquiv N g).symm x)).symm
  have hτfix : classFunctionConjLinearEquiv N g (characterClassFunction τ) =
      characterClassFunction τ := by
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    rfl
  have hne' : characterClassFunction ρ ≠ characterClassFunction τ := by
    intro he
    apply hne
    funext x
    have hx := congrFun he (ConjClasses.mk x)
    change ρ.character x = τ.character x at hx
    simpa [τ, Representation.character] using hx
  obtain ⟨x, hx, hxconj⟩ := exists_nontrivial_fixed_conjClass_of_two_fixed_irreducible
    N g (isIrreducibleCharacter_characterClassFunction ρ hρ) hτ hρfix hτfix hne'
  obtain ⟨a, ha⟩ := isConj_iff.mp hxconj
  have ha' : (a : L) * (g * (x : L) * g⁻¹) * (a : L)⁻¹ = (x : L) :=
    congrArg Subtype.val ha
  have hag : (a : L) * g ∈ M := by
    apply hc x hx
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [mul_inv_rev, mul_assoc] using ha'
  have hh := M.mul_mem (M.inv_mem (hNM a.property)) hag
  simpa only [inv_mul_cancel_left] using hh

