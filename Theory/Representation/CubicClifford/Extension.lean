module

public import Theory.Representation.Clifford
public import Theory.Representation.Quotient
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.Field.ZMod

/-!
# The Hom-space construction for an extending Clifford constituent

For an `H`-representation `ρ`, an extending representation `τ`, and a normal
subgroup `K`, the multiplicity space is the `K`-fixed subspace of the natural
`H`-action on `Hom(E,V)`.  This file records the actual construction and the
elementary identities used by the Clifford extension argument.  The final
evaluation equivalence and simplicity theorem are intentionally kept as a
separate source-level obligation: they require the complete homogeneous
restriction argument.
-/

@[expose] public section

open scoped TensorProduct
open _root_.Representation

namespace Representation.CubicClifford

universe u v w

variable {H K : Type u} [Group H] [Finite H]
  (Ksub : Subgroup H) [Ksub.Normal]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {E : Type w} [AddCommGroup E] [Module (ZMod 2) E]

/-- The ambient Hom representation used to define the multiplicity module. -/
noncomputable abbrev homAction
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    Representation (ZMod 2) H (E →ₗ[ZMod 2] V) :=
  Representation.linHom τ ρ

/-- `Hom_K(τ|K,ρ|K)`, represented as an actual subspace of `Hom(E,V)`. -/
noncomputable abbrev homSpace
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    Submodule (ZMod 2) (E →ₗ[ZMod 2] V) :=
  Representation.invariants ((homAction τ ρ).comp Ksub.subtype)

/- The multiplicity space is finite-dimensional whenever both input modules are. -/
instance homSpace_finiteDimensional
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V)
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V] :
    FiniteDimensional (ZMod 2) (homSpace Ksub τ ρ) :=
  FiniteDimensional.of_injective (homSpace Ksub τ ρ).subtype Subtype.val_injective

omit [Finite H] [Ksub.Normal] in
private theorem homSpace_mem_iff
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V)
    (f : E →ₗ[ZMod 2] V) :
    f ∈ homSpace Ksub τ ρ ↔
      ∀ k : Ksub, ρ k ∘ₗ f ∘ₗ τ (k : H)⁻¹ = f := by
  rw [Representation.mem_invariants]
  change (∀ k : Ksub, (homAction τ ρ) (k : H) f = f) ↔ _
  simp only [Representation.linHom_apply]


omit [Finite H] in
 /-- The Hom-space is stable under the full `H`-action. -/
theorem homSpace_stable
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V)
    (h : H) (f : E →ₗ[ZMod 2] V) (hf : f ∈ homSpace Ksub τ ρ) :
    (homAction τ ρ h) f ∈ homSpace Ksub τ ρ := by
  rw [homSpace_mem_iff] at hf ⊢
  intro k
  have hconj : (h⁻¹ * (k : H) * h : H) ∈ Ksub :=
    by simpa using
      (Subgroup.Normal.conj_mem (inferInstance : Ksub.Normal) (k : H) k.property h⁻¹)
  have hfk := hf ⟨h⁻¹ * (k : H) * h, hconj⟩
  change ρ (k : H) ∘ₗ ((homAction τ ρ h) f) ∘ₗ τ (k : H)⁻¹ =
    (homAction τ ρ h) f
  rw [Representation.linHom_apply]
  have hh := congrArg (fun q : E →ₗ[ZMod 2] V => (ρ h) ∘ₗ q ∘ₗ τ h⁻¹) hfk
  apply LinearMap.ext
  intro e
  simp only [LinearMap.comp_apply] at hh ⊢
  have hleft :
      (ρ (k : H)) ((ρ h) (f ((τ h⁻¹) ((τ (k : H)⁻¹) e)))) =
        (ρ h) ((ρ (h⁻¹ * ((k : H) * h)))
          (f ((τ (h⁻¹ * ((k : H) * h))⁻¹) ((τ h⁻¹) e)))) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← Module.End.mul_apply, ← Module.End.mul_apply]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1 <;> group
  have hh' := congrArg (fun q : E →ₗ[ZMod 2] V => q e) hh
  have hh'' :
      (ρ h) ((ρ (h⁻¹ * ((k : H) * h)))
        (f ((τ (h⁻¹ * ((k : H) * h))⁻¹) ((τ h⁻¹) e)))) =
        (ρ h) (f ((τ h⁻¹) e)) := by
    simpa only [LinearMap.comp_apply, mul_assoc] using hh'
  exact hleft.trans hh''

/-- The actual multiplicity representation on `Hom_K(τ|K,ρ|K)`. -/
noncomputable def homRepresentation
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    Representation (ZMod 2) H (homSpace Ksub τ ρ) where
  toFun h := (homAction τ ρ h).restrict (homSpace_stable Ksub τ ρ h)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun q : Module.End (ZMod 2) (E →ₗ[ZMod 2] V) => q f.1)
      (MonoidHom.map_one (homAction τ ρ))
  map_mul' h₁ h₂ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun q : Module.End (ZMod 2) (E →ₗ[ZMod 2] V) => q f.1)
      (MonoidHom.map_mul (homAction τ ρ) h₁ h₂)

omit [Finite H] in
@[simp] theorem homRepresentation_apply
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V)
    (h : H) (f : homSpace Ksub τ ρ) :
    (homRepresentation Ksub τ ρ h f).1 = (homAction τ ρ h) f.1 := rfl

omit [Finite H] in
/-- The normal subgroup acts trivially on the multiplicity representation. -/
theorem homSubgroup_le_ker
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    Ksub ≤ (homRepresentation Ksub τ ρ).ker := by
  intro k hk
  let k' : Ksub := ⟨k, hk⟩
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change (homAction τ ρ k) f.1 = f.1
  have hf : f.1 ∈ homSpace Ksub τ ρ := f.2
  have hfix := (Representation.mem_invariants ((homAction τ ρ).comp Ksub.subtype) f.1).mp hf k'
  exact hfix

/-- The multiplicity action descends through the quotient by `Ksub`. -/
noncomputable def homQuotientRepresentation
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    Representation (ZMod 2) (H ⧸ Ksub) (homSpace Ksub τ ρ) :=
  Representation.quotientOfLEKer (homRepresentation Ksub τ ρ) Ksub
    (homSubgroup_le_ker Ksub τ ρ)

omit [Finite H] in
theorem homQuotientRepresentation_irreducible_iff
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    IsIrreducible (homQuotientRepresentation Ksub τ ρ) ↔
      IsIrreducible (homRepresentation Ksub τ ρ) := by
  exact Representation.quotientOfLEKer_irreducible_iff
    (homRepresentation Ksub τ ρ) Ksub (homSubgroup_le_ker Ksub τ ρ)

/-- Evaluation from the tensor product of the extending constituent and the
    multiplicity space to the ambient module. -/
noncomputable def evaluation
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) :
    E ⊗[ZMod 2] homSpace Ksub τ ρ →ₗ[ZMod 2] V :=
  TensorProduct.lift {
    toFun := fun e => {
      toFun := fun f => f.1 e
      map_add' := by intro f g; simp
      map_smul' := by intro a f; simp }
    map_add' := by intro e₁ e₂; ext f; simp
    map_smul' := by intro a e; ext f; simp }

omit [Finite H] [Ksub.Normal] in
@[simp] theorem evaluation_tmul
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V)
    (e : E) (f : homSpace Ksub τ ρ) :
    evaluation Ksub τ ρ (e ⊗ₜ[ZMod 2] f) = f.1 e := by
  rfl

omit [Finite H] in
/-- Evaluation is an intertwining map for the constructed `H`-action. -/
theorem evaluation_intertwining
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) (h : H) :
    evaluation Ksub τ ρ ∘ₗ (τ.tprod (homRepresentation Ksub τ ρ) h) =
      ρ h ∘ₗ evaluation Ksub τ ρ := by
  apply TensorProduct.ext'
  intro e f
  simp only [LinearMap.comp_apply, Representation.tprod_apply,
    TensorProduct.map_tmul, evaluation_tmul, homRepresentation_apply,
    Representation.linHom_apply, LinearMap.comp_apply]
  have hτ : τ h⁻¹ (τ h e) = e := by
    have := congrArg (fun q : Module.End (ZMod 2) E => q e)
      (show τ h⁻¹ * τ h = (1 : Module.End (ZMod 2) E) by
        rw [← map_mul, inv_mul_cancel, map_one])
    exact this
  rw [hτ]

omit [Finite H] in
/-- An actual occurrence of the extending constituent makes evaluation
surjective.  The proof uses only irreducibility of the ambient representation;
injectivity is the separate homogeneous-restriction step. -/
theorem evaluation_surjective_of_occurrence
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    [Fact (Nat.Prime 2)]
    (hσabs : IsAbsolutelyIrreducible (F := ZMod 2) (G := Ksub) (V := E)
      (show Representation (ZMod 2) Ksub E from τ.comp Ksub.subtype))
    (A : Subrepresentation (ρ.comp Ksub.subtype))
    (hA : Nonempty
      (A.toRepresentation ≃ₗ
        (show Representation (ZMod 2) Ksub E from τ.comp Ksub.subtype))) :
    Function.Surjective (evaluation Ksub τ ρ) := by
  let sigma : Representation (ZMod 2) Ksub E := τ.comp Ksub.subtype
  let : IsAbsolutelyIrreducible sigma := hσabs
  let : IsIrreducible sigma :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible sigma
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial sigma
  let e : A.toRepresentation ≃ₗ sigma := hA.some
  let inclA : A.toRepresentation →ₗ (ρ.comp Ksub.subtype) := by
    refine Representation.RepMap.mk A.toSubmodule.subtype ?_
    intro k
    ext a
    rfl
  let u : sigma →ₗ (ρ.comp Ksub.subtype) :=
    inclA.comp e.symm.toRepMap
  have hu : u ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    intro hz
    have hz' := congrArg (fun q : sigma →ₗ (ρ.comp Ksub.subtype) => q x) hz
    have hxe : e.symm x ≠ 0 := by
      intro hzero
      apply hx
      have := congrArg (fun z : A.toSubmodule => e z) hzero
      rw [e.apply_symm_apply, e.map_zero] at this
      exact this
    apply hxe
    apply Subtype.ext
    simpa [u, inclA] using hz'
  let mf : (sigma.linHom (ρ.comp Ksub.subtype)).invariants :=
    (Representation.invariantsEquivIntertwiningMap sigma (ρ.comp Ksub.subtype)).symm u
  let m : homSpace Ksub τ ρ :=
    ⟨mf.1, by
      rw [homSpace_mem_iff]
      have hmf := (Representation.mem_invariants
        (sigma.linHom (ρ.comp Ksub.subtype)) mf.1).mp mf.2
      simpa [sigma, Representation.linHom_apply] using hmf⟩
  have hm : (m.1 : E →ₗ[ZMod 2] V) ≠ 0 := by
    intro hz
    apply hu
    have hmf : mf = 0 := by
      apply Subtype.ext
      exact hz
    have hu0 := congrArg
      (fun q => (Representation.invariantsEquivIntertwiningMap sigma
        (ρ.comp Ksub.subtype)) q) hmf
    simpa [mf] using hu0
  let ev : (τ.tprod (homRepresentation Ksub τ ρ)).IntertwiningMap ρ :=
    Representation.IntertwiningMap.mk (evaluation Ksub τ ρ)
      (fun h => evaluation_intertwining Ksub τ ρ h)
  have hev : ev ≠ 0 := by
    intro hz
    have hzero : evaluation Ksub τ ρ = 0 := by
      exact congrArg Representation.IntertwiningMap.toLinearMap hz
    have hmzero : (m.1 : E →ₗ[ZMod 2] V) = 0 := by
      apply LinearMap.ext
      intro e0
      have heval := congrArg (fun q : E ⊗[ZMod 2] homSpace Ksub τ ρ →ₗ[ZMod 2] V =>
          q (e0 ⊗ₜ[ZMod 2] m)) hzero
      simpa [evaluation_tmul] using heval
    exact hm hmzero
  rcases Representation.IsIrreducible.surjective_or_eq_zero ev with hev' | hev'
  · exact hev'
  · exact (hev hev').elim

/- The dimension comparison needed for the final homogeneous Clifford step turns
   the proved surjectivity into the desired representation equivalence. -/
omit [Finite H] in
theorem evaluation_repEquiv_of_finrank_eq
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    [Fact (Nat.Prime 2)]
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
    (hσabs : IsAbsolutelyIrreducible (F := ZMod 2) (G := Ksub) (V := E)
      (show Representation (ZMod 2) Ksub E from τ.comp Ksub.subtype))
    (A : Subrepresentation (ρ.comp Ksub.subtype))
    (hA : Nonempty
      (A.toRepresentation ≃ₗ
        (show Representation (ZMod 2) Ksub E from τ.comp Ksub.subtype)))
    (hfin : Module.finrank (ZMod 2)
        (E ⊗[ZMod 2] homSpace Ksub τ ρ) =
      Module.finrank (ZMod 2) V) :
    Nonempty ((τ.tprod (homRepresentation Ksub τ ρ)).Equiv ρ) := by
  let ev : (τ.tprod (homRepresentation Ksub τ ρ)).IntertwiningMap ρ :=
    Representation.IntertwiningMap.mk (evaluation Ksub τ ρ)
      (fun h => evaluation_intertwining Ksub τ ρ h)
  have hsurj : Function.Surjective (evaluation Ksub τ ρ) :=
    evaluation_surjective_of_occurrence Ksub τ ρ hσabs A hA
  have hinj : Function.Injective (evaluation Ksub τ ρ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj
  exact ⟨ev.ofBijective ⟨hinj, hsurj⟩⟩

end Representation.CubicClifford
