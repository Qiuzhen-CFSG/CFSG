module

public import Theory.Representation.AffineNine.Model
public import Theory.Representation.AbelianAllWeights
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Uniform nontrivial character weights in the affine-nine model

The translation subgroup is the additive ternary plane.  After passing to an
algebraically closed coefficient field, its simultaneous character spaces span
the module.  Conjugation by the actual linear complement transports these
spaces by the contragredient character action.  Consequently, transitivity of
the complement on the nontrivial characters makes all eight nontrivial weight
spaces have one common dimension.  The trivial weight is kept as a separate
space throughout.
-/

open scoped BigOperators MatrixGroups
open Matrix

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

public section

noncomputable section

namespace Representation.AffineNine

variable {E V L : Type*} [Field E] [hAlg : IsAlgClosed E] [Group L]
  [AddCommGroup V] [Module E V] [hFD : FiniteDimensional E V]
  (j : L →* LinearGroup)

abbrev translationRepresentation (rho : Representation E (Affine j) V) :
    Representation E Translation V :=
  rho.comp (SemidirectProduct.inl : Translation →* Affine j)

/-- The character obtained by conjugating a translation character by a
complement element.  The inverse occurs because a vector in the image of a
weight space is tested at the conjugated translation. -/
@[expose] def conjugateCharacter (l : L) (χ : Translation →* Eˣ) :
    Translation →* Eˣ :=
  χ.comp (naturalAction (j l)).symm.toMonoidHom

omit [IsAlgClosed E] in
@[simp] theorem conjugateCharacter_apply (l : L) (χ : Translation →* Eˣ)
    (x : Translation) :
    conjugateCharacter j l χ x = χ ((naturalAction (j l)).symm x) := rfl

private theorem complement_conjugates_translation (l : L) (x : Translation) :
    (SemidirectProduct.inr l : Affine j) * SemidirectProduct.inl
        ((naturalAction (j l)).symm x) * (SemidirectProduct.inr l)⁻¹ =
      SemidirectProduct.inl x := by
  rw [conjugate_translation]
  simp [linearPart]

omit hAlg hFD in
private theorem complement_mem_characterWeightSpace
    (rho : Representation E (Affine j) V) (l : L) (χ : Translation →* Eˣ)
    (v : V) (hv : v ∈ (translationRepresentation j rho).characterWeightSpace χ) :
    rho (SemidirectProduct.inr l) v ∈
      (translationRepresentation j rho).characterWeightSpace
        (conjugateCharacter j l χ) := by
  rw [characterWeightSpace, Submodule.mem_iInf]
  intro x
  rw [Module.End.mem_eigenspace_iff]
  let y : Translation := (naturalAction (j l)).symm x
  have hv' : ∀ k, v ∈ Module.End.eigenspace ((translationRepresentation j rho) k) (χ k : E) := by
    simpa only [characterWeightSpace, Submodule.mem_iInf] using hv
  have hy := hv' y
  rw [Module.End.mem_eigenspace_iff] at hy
  have hc := complement_conjugates_translation j l x
  change rho (SemidirectProduct.inl x) (rho (SemidirectProduct.inr l) v) =
    ((conjugateCharacter j l χ x : Eˣ) : E) • rho (SemidirectProduct.inr l) v
  rw [← hc]
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  change rho (SemidirectProduct.inr l) ((translationRepresentation j rho) y v) = _
  rw [hy, map_smul]
  rfl

include hAlg hFD
private theorem finrank_characterWeightSpace_conjugate_aux
    (rho : Representation E (Affine j) V) (l : L) (χ : Translation →* Eˣ) :
    Module.finrank E
    ((translationRepresentation j rho).characterWeightSpace χ) =
      Module.finrank E
        ((translationRepresentation j rho).characterWeightSpace
          (conjugateCharacter j l χ)) := by
  let σ : Representation E Translation V := translationRepresentation j rho
  let e : V ≃ₗ[E] V := LinearEquiv.ofBijective (rho (SemidirectProduct.inr l))
    (Representation.apply_bijective rho (SemidirectProduct.inr l))
  have hmap :
      (σ.characterWeightSpace χ).map (rho (SemidirectProduct.inr l)) ≤
        σ.characterWeightSpace (conjugateCharacter j l χ) := by
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact complement_mem_characterWeightSpace j rho l χ v hv
  have hmap' :
      (σ.characterWeightSpace χ).map (rho (SemidirectProduct.inr l)) =
        σ.characterWeightSpace (conjugateCharacter j l χ) := by
    apply le_antisymm hmap
    intro w hw
    let z : V := rho (SemidirectProduct.inr l)⁻¹ w
    have hz : z ∈ σ.characterWeightSpace χ := by
      rw [characterWeightSpace, Submodule.mem_iInf]
      intro x
      rw [Module.End.mem_eigenspace_iff]
      let y : Translation := (naturalAction (j l)) x
      have hw' : ∀ k, w ∈ Module.End.eigenspace ((translationRepresentation j rho) k)
          ((conjugateCharacter j l χ) k : E) := by
        simpa only [characterWeightSpace, Submodule.mem_iInf] using hw
      have hy := hw' y
      rw [Module.End.mem_eigenspace_iff] at hy
      have hc := complement_conjugates_translation j l y
      have hcxy : (SemidirectProduct.inr l : Affine j) * SemidirectProduct.inl x *
          (SemidirectProduct.inr l)⁻¹ = SemidirectProduct.inl y := by
        simpa [y] using hc
      have hxy : (naturalAction (j l)).symm y = x := by simp [y]
      change rho (SemidirectProduct.inl x) z = ((χ x : Eˣ) : E) • z
      have hc' : (SemidirectProduct.inr l : Affine j)⁻¹ *
          SemidirectProduct.inl y * SemidirectProduct.inr l =
          SemidirectProduct.inl x := by
        calc
          (SemidirectProduct.inr l : Affine j)⁻¹ * SemidirectProduct.inl y *
              SemidirectProduct.inr l =
              (SemidirectProduct.inr l)⁻¹ *
                ((SemidirectProduct.inr l) * SemidirectProduct.inl x *
                  (SemidirectProduct.inr l)⁻¹) * SemidirectProduct.inr l := by rw [hcxy]
          _ = SemidirectProduct.inl x := by group
      rw [← hc']
      simp only [map_mul, Module.End.mul_apply]
      have hzmap : rho (SemidirectProduct.inr l) z = w := by simp [z]
      rw [hzmap]
      change rho (SemidirectProduct.inr l)⁻¹
        ((translationRepresentation j rho) y w) = _
      rw [hy, map_smul]
      simp [z, hxy, conjugateCharacter]
    exact ⟨z, hz, by simp [z]⟩
  rw [← hmap']
  exact (e.finrank_map_eq (σ.characterWeightSpace χ)).symm

/-- Conjugation by the concrete complement preserves the dimension of every
translation character space. -/
public theorem finrank_characterWeightSpace_conjugate
    (rho : Representation E (Affine j) V) (l : L) (χ : Translation →* Eˣ) :
    Module.finrank E
        ((translationRepresentation j rho).characterWeightSpace χ) =
      Module.finrank E
        ((translationRepresentation j rho).characterWeightSpace
          (conjugateCharacter j l χ)) := by
  exact finrank_characterWeightSpace_conjugate_aux (j := j) (rho := rho) (l := l) (χ := χ)

private theorem exists_nontrivial_characterWeightSpace
    (rho : Representation E (Affine j) V) (hfaith : Function.Injective rho)
    (horder : (Nat.card Translation : E) ≠ 0) :
    ∃ χ : Translation →* Eˣ, χ ≠ 1 ∧
      (translationRepresentation j rho).characterWeightSpace χ ≠ ⊥ := by
  let σ : Representation E Translation V := translationRepresentation j rho
  by_contra h
  push Not at h
  have hle : (⨆ χ : σ.CharacterWeight, σ.characterWeightSpace χ.val) ≤
      σ.characterWeightSpace 1 := by
    refine iSup_le fun χ => ?_
    by_cases hχ : χ.val = 1
    · simpa [hχ]
    · rw [h χ.val hχ]
      exact bot_le
  have hspace : σ.characterWeightSpace 1 = ⊤ := by
    apply top_unique
    rw [← σ.iSup_characterWeightSpace_eq_top horder]
    exact hle
  have htrivial : ∀ t : Translation, σ t = LinearMap.id := by
    intro t
    ext v
    have hv : v ∈ σ.characterWeightSpace 1 := by
      rw [hspace]
      trivial
    have hv' : ∀ k, v ∈ Module.End.eigenspace (σ k)
        (((1 : Translation →* Eˣ) k : E)) := by
      simpa only [characterWeightSpace, Submodule.mem_iInf] using hv
    have hvt := hv' t
    rw [Module.End.mem_eigenspace_iff] at hvt
    simpa using hvt
  let t : Translation := Multiplicative.ofAdd (fun _ : Fin 2 => (1 : ZMod 3))
  have ht : t ≠ 1 := by decide
  have hrt : rho (SemidirectProduct.inl t) = rho 1 := by
    change σ t = rho 1
    calc
      σ t = LinearMap.id := htrivial t
      _ = rho 1 := by simp [Module.End.one_eq_id]
  have he : (SemidirectProduct.inl t : Affine j) = 1 := hfaith (by simpa using hrt)
  exact ht (SemidirectProduct.inl_injective he)

/-- A uniformity witness for the eight nontrivial translation characters.
The dimension of the trivial character space is deliberately omitted from the
uniform clause and remains available as its own weight space. -/
structure UniformWeights (rho : Representation E (Affine j) V) where
  nontrivialDim : ℕ
  positive : 0 < nontrivialDim
  nontrivial_finrank : ∀ χ : Translation →* Eˣ, χ ≠ 1 →
    Module.finrank E
        ((translationRepresentation j rho).characterWeightSpace χ) =
      nontrivialDim

/-- The actual affine-nine complement gives uniform positive dimensions as soon
as its contragredient action is transitive on nontrivial characters. -/
public noncomputable def uniformWeights_of_transitive
    (rho : Representation E (Affine j) V) (hfaith : Function.Injective rho)
    (horder : (Nat.card Translation : E) ≠ 0)
    (htrans : ∀ χ ψ : Translation →* Eˣ, χ ≠ 1 → ψ ≠ 1 →
      ∃ l : L, conjugateCharacter j l χ = ψ) :
    UniformWeights j rho := by
  let h_exists := exists_nontrivial_characterWeightSpace j rho hfaith horder
  let χ₀ : Translation →* Eˣ := Classical.choose h_exists
  have hχ₀ : χ₀ ≠ 1 ∧
      (translationRepresentation j rho).characterWeightSpace χ₀ ≠ ⊥ :=
    Classical.choose_spec h_exists
  have hspace₀ := hχ₀.2
  let n := Module.finrank E
    ((translationRepresentation j rho).characterWeightSpace χ₀)
  refine ⟨n, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspace₀
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, hv⟩, by simpa using hv0⟩
  · intro χ hχ
    obtain ⟨l, hl⟩ := htrans χ₀ χ hχ₀.1 hχ
    calc
      Module.finrank E ((translationRepresentation j rho).characterWeightSpace χ) =
          Module.finrank E ((translationRepresentation j rho).characterWeightSpace χ₀) := by
        rw [← hl]
        exact (finrank_characterWeightSpace_conjugate (j := j) (rho := rho)
          (l := l) (χ := χ₀)).symm
      _ = n := rfl

/-- The trivial character space is exactly the invariant submodule of the
translation restriction, so its dimension is retained separately. -/
theorem characterWeightSpace_one_eq_invariants
    (rho : Representation E (Affine j) V) :
    (translationRepresentation j rho).characterWeightSpace 1 =
      (translationRepresentation j rho).invariants := by
  ext v
  rw [characterWeightSpace, Submodule.mem_iInf, Representation.mem_invariants]
  simp only [Module.End.mem_eigenspace_iff, MonoidHom.one_apply, Units.val_one, one_smul]

omit hAlg hFD

/-! The following construction is the concrete character table over the
algebraic closure of `𝔽₂`.  A nontrivial character of the cyclic scalar group
`𝔽₃ˣ` is pulled back along the dot products with vectors in the ternary
plane.  The resulting map is injective by the nondegeneracy of that pairing,
and hence bijective by the finite cardinality formula for character groups.
-/

abbrev algebraicClosureE9 := AlgebraicClosure (ZMod 2)

private local instance algebraicClosure_scalarExponent_ne_zero :
    NeZero (Monoid.exponent (Multiplicative (ZMod 3)) : ZMod 2) := by
  refine ⟨?_⟩
  rw [IsCyclic.exponent_eq_card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  change (3 : ZMod 2) ≠ 0
  intro h
  have hd : 2 ∣ 3 := (CharP.cast_eq_zero_iff (ZMod 2) 2 3).mp h
  omega

private local instance algebraicClosure_scalar_card_prime :
    Fact (Nat.Prime (Nat.card (Multiplicative (ZMod 3)))) := by
  rw [show Nat.card (Multiplicative (ZMod 3)) = 3 by simp]
  exact ⟨by decide⟩

private noncomputable def algebraicClosure_scalarHom :
    Multiplicative (ZMod 3) →* algebraicClosureE9ˣ :=
  Classical.choose (CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Multiplicative (ZMod 3)) algebraicClosureE9
    (a := Multiplicative.ofAdd (1 : ZMod 3)) (by decide))

private lemma algebraicClosure_scalarHom_gen_ne_one :
    algebraicClosure_scalarHom (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 :=
  Classical.choose_spec (CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Multiplicative (ZMod 3)) algebraicClosureE9
    (a := Multiplicative.ofAdd (1 : ZMod 3)) (by decide))

private lemma algebraicClosure_scalarHom_injective :
    Function.Injective algebraicClosure_scalarHom := by
  apply (MonoidHom.ker_eq_bot_iff algebraicClosure_scalarHom).mp
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card algebraicClosure_scalarHom.ker with hk | hk
  · exact hk
  · exfalso
    apply algebraicClosure_scalarHom_gen_ne_one
    apply (MonoidHom.mem_ker).mp
    rw [hk]
    exact Subgroup.mem_top _

private noncomputable def algebraicClosure_dotLinear (w : Plane) : Plane →+ ZMod 3 where
  toFun x := dotProduct w x
  map_zero' := by simp [dotProduct]
  map_add' x y := by
    simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private noncomputable def algebraicClosure_charOf (w : Plane) :
    Translation →* algebraicClosureE9ˣ :=
  algebraicClosure_scalarHom.comp ((algebraicClosure_dotLinear w).toMultiplicative)

private noncomputable def algebraicClosure_coordinateHom :
    Translation →* (Translation →* algebraicClosureE9ˣ) where
  toFun w := algebraicClosure_charOf w.toAdd
  map_one' := by
    ext x
    simp [algebraicClosure_charOf, algebraicClosure_dotLinear, dotProduct]
  map_mul' w z := by
    apply MonoidHom.ext
    intro x
    change algebraicClosure_scalarHom
        (Multiplicative.ofAdd (dotProduct (w.toAdd + z.toAdd) x.toAdd)) =
      algebraicClosure_scalarHom (Multiplicative.ofAdd (dotProduct w.toAdd x.toAdd)) *
        algebraicClosure_scalarHom (Multiplicative.ofAdd (dotProduct z.toAdd x.toAdd))
    have hdot : dotProduct (w.toAdd + z.toAdd) x.toAdd =
        dotProduct w.toAdd x.toAdd + dotProduct z.toAdd x.toAdd := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.add_apply]
      ring
    rw [hdot, ofAdd_add, map_mul]

private lemma algebraicClosure_coordinateHom_injective :
    Function.Injective algebraicClosure_coordinateHom := by
  intro w z hwz
  apply Multiplicative.toAdd.injective
  ext i
  have hdot (x : Plane) : dotProduct w.toAdd x = dotProduct z.toAdd x := by
    apply algebraicClosure_scalarHom_injective
    have h₂ := congrArg
      (fun f : Translation →* algebraicClosureE9ˣ => f (Multiplicative.ofAdd x)) hwz
    change algebraicClosure_scalarHom
        (Multiplicative.ofAdd (dotProduct w.toAdd x)) =
      algebraicClosure_scalarHom (Multiplicative.ofAdd (dotProduct z.toAdd x)) at h₂
    exact h₂
  have hi := hdot (Pi.single i 1)
  simpa only [dotProduct_single, mul_one] using hi

private local instance algebraicClosure_translationExponent_ne_zero :
    NeZero (Monoid.exponent Translation : ZMod 2) := by
  have hdvd : Monoid.exponent Translation ∣ 3 := by
    apply (Monoid.exponent_dvd_iff_forall_pow_eq_one).2
    intro x
    exact translation_cube x
  rcases (Nat.dvd_prime (by decide)).mp hdvd with h | h
  · rw [h]
    exact ⟨by norm_num⟩
  · rw [h]
    exact ⟨by
      change (3 : ZMod 2) ≠ 0
      intro hz
      have : 2 ∣ 3 := (CharP.cast_eq_zero_iff (ZMod 2) 2 3).mp hz
      omega⟩

/-- The actual equivariant character table of the ternary translation plane
over `AlgebraicClosure (ZMod 2)`. -/
public noncomputable def algebraicClosureTranslationCharacterEquiv :
    Translation ≃* (Translation →* algebraicClosureE9ˣ) := by
  apply MulEquiv.ofBijective algebraicClosure_coordinateHom
  refine (Nat.bijective_iff_injective_and_card algebraicClosure_coordinateHom).2
    ⟨algebraicClosure_coordinateHom_injective, ?_⟩
  symm
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Translation algebraicClosureE9

private lemma algebraicClosureTranslationCharacterEquiv_apply (w x : Plane) :
    algebraicClosureTranslationCharacterEquiv (Multiplicative.ofAdd w)
        (Multiplicative.ofAdd x) =
      algebraicClosure_scalarHom (Multiplicative.ofAdd (dotProduct w x)) := by
  rfl

public theorem algebraicClosureTranslationCharacterEquiv_equivariant (g : LinearGroup)
    (w : Plane) :
    conjugateCharacter (MonoidHom.id LinearGroup) g
        (algebraicClosureTranslationCharacterEquiv (Multiplicative.ofAdd w)) =
      algebraicClosureTranslationCharacterEquiv
        (Multiplicative.ofAdd (dualPerm g w)) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  change algebraicClosureTranslationCharacterEquiv (Multiplicative.ofAdd w)
      ((naturalAction g).symm (Multiplicative.ofAdd v)) =
    algebraicClosureTranslationCharacterEquiv
      (Multiplicative.ofAdd (dualPerm g w)) (Multiplicative.ofAdd v)
  let A : LinearGroup := Inv.inv g
  have hA : (naturalAction g).symm (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (Matrix.mulVec A.val v) := by
    rfl
  rw [hA, algebraicClosureTranslationCharacterEquiv_apply,
    algebraicClosureTranslationCharacterEquiv_apply]
  congr 1
  calc
    dotProduct w (Matrix.mulVec A.val v) =
        dotProduct v (Matrix.mulVec A.val.transpose w) := by
      simpa using (Matrix.dotProduct_transpose_mulVec (A := A.val.transpose)
        (x := w) (y := v))
    _ = dotProduct (Matrix.mulVec A.val.transpose w) v := dotProduct_comm _ _

/-- A concrete parametrization of the translation characters by the dual
ternary plane.  The equivariance clause is the genuine contragredient
comparison used by the two affine-nine models. -/
structure CharacterCoordinates (j : L →* LinearGroup) where
  /-- The character table is indexed by the additive translation group. -/
  equiv : Translation ≃* (Translation →* Eˣ)
  equivariant : ∀ (l : L) (w : Plane),
    conjugateCharacter j l (equiv (Multiplicative.ofAdd w)) =
      equiv (Multiplicative.ofAdd (dualPerm (j l) w))

/-- Character coordinates for the full `GL₂(3)` complement over the binary
algebraic closure. -/
public noncomputable def algebraicClosureFullCharacterCoordinates :
    CharacterCoordinates (E := algebraicClosureE9) (MonoidHom.id LinearGroup) where
  equiv := algebraicClosureTranslationCharacterEquiv
  equivariant l w := algebraicClosureTranslationCharacterEquiv_equivariant l w

/-- Character coordinates for the special `SL₂(3)` complement over the binary
algebraic closure. -/
public noncomputable def algebraicClosureSpecialCharacterCoordinates :
    CharacterCoordinates (E := algebraicClosureE9)
      (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup) where
  equiv := algebraicClosureTranslationCharacterEquiv
  equivariant l w := by
    exact algebraicClosureTranslationCharacterEquiv_equivariant
      (SpecialLinearGroup.toGL l) w

theorem characterTransitive_of_coordinates
    (coords : CharacterCoordinates (E := E) j)
    (hplane : ∀ w z : Plane, w ≠ 0 → z ≠ 0 →
      ∃ l : L, dualPerm (j l) w = z) :
    ∀ χ ψ : Translation →* Eˣ, χ ≠ 1 → ψ ≠ 1 →
      ∃ l : L, conjugateCharacter j l χ = ψ := by
  intro χ ψ hχ hψ
  let w := coords.equiv.symm χ
  let z := coords.equiv.symm ψ
  have hw : w.toAdd ≠ 0 := by
    intro hw
    have hw1 : w = Multiplicative.ofAdd 0 := by
      rw [← ofAdd_toAdd w, hw]
    apply hχ
    calc
      χ = coords.equiv w := (coords.equiv.apply_symm_apply χ).symm
      _ = coords.equiv (Multiplicative.ofAdd 0) := by rw [hw1]
      _ = 1 := map_one coords.equiv
  have hz : z.toAdd ≠ 0 := by
    intro hz
    have hz1 : z = Multiplicative.ofAdd 0 := by
      rw [← ofAdd_toAdd z, hz]
    apply hψ
    calc
      ψ = coords.equiv z := (coords.equiv.apply_symm_apply ψ).symm
      _ = coords.equiv (Multiplicative.ofAdd 0) := by rw [hz1]
      _ = 1 := map_one coords.equiv
  obtain ⟨l, hl⟩ := hplane w.toAdd z.toAdd hw hz
  refine ⟨l, ?_⟩
  rw [show χ = coords.equiv w by simp [w], show ψ = coords.equiv z by simp [z]]
  change conjugateCharacter j l (coords.equiv (Multiplicative.ofAdd w.toAdd)) =
    coords.equiv (Multiplicative.ofAdd z.toAdd)
  rw [coords.equivariant, hl]

end Representation.AffineNine
