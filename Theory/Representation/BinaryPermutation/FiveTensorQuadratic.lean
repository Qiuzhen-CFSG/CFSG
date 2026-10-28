module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.Defs

/-!
# A quadratic obstruction on the S₅ natural tensor module

On the even-weight core of the binary five-point permutation module,
the second displacement by (01)(23) and (02)(13) of e₀+e₄ has coordinate
zero equal to one. Tensoring with any nonzero vector in a second module
preserves this obstruction, as contraction in the first coordinate shows.

The core is a concrete model of the four-dimensional natural module;
`BinaryPermutation.coreEquivNatural` identifies it with the natural quotient
model. The transport theorem requires actual group and module equivalences
and marked double transpositions.

Source: the external-X S₅ × S₃ case in Aschbacher–Smith 13.8.20,
printed p.954 (combined manuscript, 1 March 2004). The second factor may
be any nonzero module, so the natural S₃ factor is included.
-/

@[expose] public section

open TensorProduct
open Representation.BinaryOffender
namespace BinaryPermutation.FiveTensorQuadratic

private abbrev a : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
private abbrev b : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3
private def v : BinaryPermutation.core (Fin 5) :=
  ⟨![1,0,0,0,1], by rw [BinaryPermutation.mem_core]; decide⟩
private def evaluation : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 0).comp (BinaryPermutation.core (Fin 5)).subtype

private theorem displacement :
    evaluation (BinaryPermutation.coreRepresentation (Fin 5) a
        (BinaryPermutation.coreRepresentation (Fin 5) b v - v) -
      (BinaryPermutation.coreRepresentation (Fin 5) b v - v)) = 1 := by decide

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- The external tensor product of the natural S₅ core and a D-module. -/
noncomputable def tensorAction (σ : Representation (ZMod 2) D W) :
    Representation (ZMod 2) ((Equiv.Perm (Fin 5)) × D)
      ((BinaryPermutation.core (Fin 5)) ⊗[ZMod 2] W) :=
  Representation.tprod
    ((BinaryPermutation.coreRepresentation (Fin 5)).comp (MonoidHom.fst _ _))
    (σ.comp (MonoidHom.snd _ _))

/-- A subgroup containing the marked Klein four is not quadratic on the tensor module. -/
theorem tensor_not_quadratic (σ : Representation (ZMod 2) D W)
    (w : W) (hw : w ≠ 0) (A : Subgroup ((Equiv.Perm (Fin 5)) × D))
    (ha : (Equiv.swap 0 1 * Equiv.swap 2 3, 1) ∈ A)
    (hb : (Equiv.swap 0 2 * Equiv.swap 1 3, 1) ∈ A) :
    ¬ IsQuadratic (tensorAction σ) A := by
  intro hq
  have h := sub_eq_zero.mpr (hq (a, 1) ha (b, 1) hb (v ⊗ₜ[ZMod 2] w))
  have he :
      (BinaryPermutation.coreRepresentation (Fin 5) a
        (BinaryPermutation.coreRepresentation (Fin 5) b v - v) -
      (BinaryPermutation.coreRepresentation (Fin 5) b v - v)) ⊗ₜ[ZMod 2] w = 0 := by
    change TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 5) a) (σ 1)
      (TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 5) b) (σ 1)
        (v ⊗ₜ[ZMod 2] w) - v ⊗ₜ[ZMod 2] w) -
      (TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 5) b) (σ 1)
        (v ⊗ₜ[ZMod 2] w) - v ⊗ₜ[ZMod 2] w) = 0 at h
    rw [map_one] at h
    simpa only [map_sub, TensorProduct.map_tmul, Module.End.one_apply,
      ← TensorProduct.sub_tmul] using h
  have hc := congrArg
    (fun z => TensorProduct.lid (ZMod 2) W
      (TensorProduct.map evaluation (LinearMap.id : W →ₗ[ZMod 2] W) z)) he
  exact hw (by simpa only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
    displacement, one_smul, map_zero] using hc)

/-- Transport the obstruction through an actual group and module identification. -/
theorem not_quadratic_of_tensor_equiv
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (e : H ≃* (Equiv.Perm (Fin 5)) × D)
    (ρ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) D W)
    (f : V ≃ₗ[ZMod 2] ((BinaryPermutation.core (Fin 5)) ⊗[ZMod 2] W))
    (heq : ∀ g v, f (ρ g v) = tensorAction σ (e g) (f v))
    (w : W) (hw : w ≠ 0) (A : Subgroup H)
    (ha : e.symm (Equiv.swap 0 1 * Equiv.swap 2 3, 1) ∈ A)
    (hb : e.symm (Equiv.swap 0 2 * Equiv.swap 1 3, 1) ∈ A) :
    ¬ IsQuadratic ρ A := by
  intro hq
  apply tensor_not_quadratic σ w hw (A.map e.toMonoidHom)
    (Subgroup.mem_map.mpr ⟨_, ha, e.apply_symm_apply _⟩)
    (Subgroup.mem_map.mpr ⟨_, hb, e.apply_symm_apply _⟩)
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ u
  obtain ⟨v, rfl⟩ := f.surjective u
  have he := congrArg f (hq g hg h hh v)
  simpa only [MulEquiv.coe_toMonoidHom, heq, map_sub] using he

/-- Inside a marked four-group, a quadratic subgroup on this tensor module
has order at most two. -/
theorem card_le_two_of_quadratic_in_four
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
    (e : H ≃* (Equiv.Perm (Fin 5)) × D)
    (ρ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) D W)
    (f : V ≃ₗ[ZMod 2] ((BinaryPermutation.core (Fin 5)) ⊗[ZMod 2] W))
    (heq : ∀ g v, f (ρ g v) = tensorAction σ (e g) (f v))
    (w : W) (hw : w ≠ 0) (A R : Subgroup H)
    (hAR : A ≤ R) (hR : Nat.card R = 4)
    (ha : e.symm (Equiv.swap 0 1 * Equiv.swap 2 3, 1) ∈ R)
    (hb : e.symm (Equiv.swap 0 2 * Equiv.swap 1 3, 1) ∈ R)
    (hq : IsQuadratic ρ A) : Nat.card A ≤ 2 := by
  by_contra! hlarge
  have hdvd : Nat.card A ∣ 4 := hR ▸ Subgroup.card_dvd_of_le hAR
  have hle : Nat.card A ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hc : Nat.card A = 4 := by
    have hc : Nat.card A = 3 ∨ Nat.card A = 4 := by omega
    rcases hc with hc | hc
    · rw [hc] at hdvd
      norm_num at hdvd
    · exact hc
  have he : A = R := Subgroup.eq_of_le_of_card_ge hAR (by omega)
  exact not_quadratic_of_tensor_equiv e ρ σ f heq w hw A (he ▸ ha) (he ▸ hb) hq

end BinaryPermutation.FiveTensorQuadratic

end
