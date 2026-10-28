module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Contracts
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
public import Theory.Representation.IrreducibleScalarEmbedding
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Universal binary section placement from concrete Golay models

A family of thirteen pairwise inequivalent simple modules over an algebraic
closure is exhaustive by the p-regular conjugacy-class bound. The family
consists of the trivial module, four small binary models after scalar
extension, and eight modules of degree greater than forty-eight.

For an arbitrary binary irreducible of degree forty-four, choose a simple
subrepresentation after scalar extension. Its dimension excludes the larger
family. A coefficient projection of its embedding gives a nonzero binary
intertwiner from the corresponding small model. Schur's lemma makes this an
equivalence, and dimension excludes the trivial and eleven-dimensional
models. Transporting the actual section map gives the literal Golay section.
This argument proves the field-of-definition step without assuming absolute
irreducibility of the input or invoking a numerical spectrum theorem.

The concrete binary section models, large models and odd-class bound remain
explicit construction inputs. The unconditional `golayExteriorPlacement`
will be assembled here once these inputs are proved. The separate exterior
fixed-space calculation is not used in this module.

Source: G. D. James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, M₂₄ paragraph, manuscript p.17.
-/

public section
open scoped TensorProduct
namespace Representation.MathieuM24Degree44.FiveSpace.Placement
open Sporadic.Mathieu
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
universe v

private theorem equiv_of_extended_embedding
    {F E G V W : Type*} [Field F] [Field E] [Algebra F E] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (ρ : Representation F G V) (τ : Representation F G W)
    [ρ.IsIrreducible] [τ.IsIrreducible]
    (f : (extendScalars E τ).IntertwiningMap (extendScalars E ρ))
    (hf : Function.Injective f) : Nonempty (τ.Equiv ρ) := by
  let j : W →ₗ[F] E ⊗[F] V :=
    (f.toLinearMap.restrictScalars F).comp (TensorProduct.mk F E W 1)
  have hj : Function.Injective j :=
    hf.comp (Module.FaithfullyFlat.tensorProduct_mk_injective W)
  obtain ⟨e⟩ := ScalarConstituents.equiv_of_scalar_embedding ρ τ j hj (fun g w => by
    change f (1 ⊗ₜ[F] τ g w) = extendScalars E ρ g (f (1 ⊗ₜ[F] w))
    simpa only [LinearMap.comp_apply, extendScalars_apply, LinearMap.baseChange_tmul,
      IntertwiningMap.coe_toLinearMap] using
      LinearMap.congr_fun (f.isIntertwining' g) (1 ⊗ₜ[F] w))
  exact ⟨e.toRepresentationEquiv⟩

private theorem irreducible_of_finrank_one {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hd : Module.finrank F V = 1) : ρ.IsIrreducible := by
  let : IsSimpleModule F V := isSimpleModule_iff_finrank_eq_one.mpr hd
  let : Nontrivial V := IsSimpleModule.nontrivial F V
  constructor
  intro S
  rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private abbrev SmallIndex := Option (Fin 4)
private abbrev CandidateIndex := SmallIndex ⊕ Fin 8

/-- Saturation over an algebraic closure and coefficient descent identify every
binary irreducible of degree forty-four with one of the actual small models.
The input representation need not be absolutely irreducible. -/
theorem exists_small_equiv_of_families
    {E V : Type v} [Field E] [IsAlgClosed E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (d : Fin 4 → ℕ) (e : Fin 8 → ℕ)
    (τ : ∀ i, Representation (ZMod 2) M24 (Fin (d i) → ZMod 2))
    (π : ∀ i, Representation E M24 (Fin (e i) → E))
    [∀ i, (τ i).IsAbsolutelyIrreducible] [∀ i, (π i).IsIrreducible]
    (hτ : Pairwise fun i j => IsEmpty ((τ i).Equiv (τ j)))
    (hπ : Pairwise fun i j => IsEmpty ((π i).Equiv (π j)))
    (hd : ∀ i, d i = 11 ∨ d i = 44) (he : ∀ i, 48 < e i)
    (hclasses : OddClassBound)
    (ρ : Representation (ZMod 2) M24 V) [ρ.IsIrreducible]
    (hV : Module.finrank (ZMod 2) V = 44) :
    ∃ i, d i = 44 ∧ Nonempty ((τ i).Equiv ρ) := by
  classical
  let U : SmallIndex → Type := fun i => match i with
    | none => ZMod 2
    | some j => Fin (d j) → ZMod 2
  let addU : ∀ i, AddCommGroup (U i) := fun i => by
    cases i <;> dsimp [U] <;> infer_instance
  let modU : ∀ i, Module (ZMod 2) (U i) := fun i => by
    cases i <;> dsimp [U] <;> infer_instance
  let small : ∀ i, Representation (ZMod 2) M24 (U i) := fun i => match i with
    | none => Representation.trivial (ZMod 2) M24 (ZMod 2)
    | some j => τ j
  have finU : ∀ i, FiniteDimensional (ZMod 2) (U i) := by
    intro i
    cases i <;> dsimp [U] <;> infer_instance
  have irrU : ∀ i, (small i).IsIrreducible := by
    intro i
    cases i with
    | none => exact irreducible_of_finrank_one _ (Module.finrank_self _)
    | some i => exact IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible (τ i)
  have extIrrU : ∀ i, (extendScalars E (small i)).IsIrreducible := by
    intro i
    cases i with
    | none =>
      apply irreducible_of_finrank_one
      rw [Module.finrank_baseChange]
      exact Module.finrank_self _
    | some i => exact IsAbsolutelyIrreducible.irreducible_of_extension (τ i) E
  have smallBound : ∀ i, Module.finrank (ZMod 2) (U i) ≤ 44 := by
    intro i
    cases i with
    | none => simp [U]
    | some i =>
      simp only [U, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      rcases hd i with h | h <;> omega
  have smallDistinct : Pairwise fun i j => IsEmpty ((small i).Equiv (small j)) := by
    intro i j hij
    constructor
    intro f
    have hdim := f.toLinearEquiv.finrank_eq
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j =>
        simp only [U, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at hdim
        have := hd j
        omega
    | some i =>
      cases j with
      | none =>
        simp only [U, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at hdim
        have := hd i
        omega
      | some j => exact (hτ (fun h => hij (congrArg some h))).false f
  let W : CandidateIndex → Type v := fun i => match i with
    | .inl j => E ⊗[ZMod 2] U j
    | .inr j => Fin (e j) → E
  let addW : ∀ i, AddCommGroup (W i) := fun i => by
    cases i <;> dsimp [W] <;> infer_instance
  let modW : ∀ i, Module E (W i) := fun i => by
    cases i <;> dsimp [W] <;> infer_instance
  let rep : ∀ i, Representation E M24 (W i) := fun i => match i with
    | .inl j => extendScalars E (small j)
    | .inr j => π j
  have finW : ∀ i, FiniteDimensional E (W i) := by
    intro i
    cases i <;> dsimp [W] <;> infer_instance
  have irrW : ∀ i, (rep i).IsIrreducible := by
    intro i
    cases i <;> dsimp [rep] <;> infer_instance
  have distinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro f
    have hdim := f.toLinearEquiv.finrank_eq
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        obtain ⟨q⟩ := equiv_of_extended_embedding (small j) (small i)
          f.toIntertwiningMap f.toLinearEquiv.injective
        exact (smallDistinct (fun h => hij (congrArg Sum.inl h))).false q
      | inr j =>
        simp only [W, Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at hdim
        have := smallBound i
        have := he j
        omega
    | inr i =>
      cases j with
      | inl j =>
        simp only [W, Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at hdim
        have := smallBound j
        have := he i
        omega
      | inr j => exact (hπ (fun h => hij (congrArg Sum.inr h))).false f
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial (E ⊗[ZMod 2] V) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (ZMod 2) E).mpr inferInstance
  obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (extendScalars E ρ)
  let := hS
  have hc : Nat.card CandidateIndex = 13 := by
    simp [CandidateIndex, SmallIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨f⟩⟩ := exists_equiv_of_pRegular_class_bound (W := S.toSubmodule) W rep 2 distinct
    (hc ▸ hclasses) S.toRepresentation
  cases i with
  | inl i =>
    let inc : S.toRepresentation.IntertwiningMap (extendScalars E ρ) :=
      .mk S.toSubmodule.subtype (fun _ => rfl)
    obtain ⟨q⟩ := equiv_of_extended_embedding ρ (small i)
      (inc.comp f.symm.toIntertwiningMap)
      (Subtype.val_injective.comp f.symm.toLinearEquiv.injective)
    have hdim := q.toLinearEquiv.finrank_eq
    cases i with
    | none =>
      simp only [U, Module.finrank_self] at hdim
      omega
    | some i =>
      refine ⟨i, ?_, ⟨q⟩⟩
      simpa only [U, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hV] using hdim
  | inr i =>
    have hdim := f.toLinearEquiv.finrank_eq
    have hbound := S.toSubmodule.finrank_le
    simp only [W, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    rw [Module.finrank_baseChange, hV] at hbound
    have := he i
    omega

end Representation.MathieuM24Degree44.FiveSpace.Placement

namespace Representation.MathieuM24Degree44.FiveSpace
open Placement Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
universe v

/-- Compose the literal quotient map with an equivariant equivalence. -/
theorem IsSectionOf.of_equiv
    {F G V W U : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    {ρ : Representation F G V} {τ : Representation F G W} {σ : Representation F G U}
    (h : IsSectionOf ρ σ) (e : ρ.Equiv τ) : IsSectionOf τ σ := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨S, e.toIntertwiningMap.comp f, e.toLinearEquiv.surjective.comp hf⟩

/-- The native section-placement contract follows from three concrete
construction inputs. None of these inputs asserts universal placement. -/
theorem golayExteriorPlacement_of_binary_models
    (hsmall : BinarySectionModels) (hlarge : LargeModelsExist.{v})
    (hclasses : OddClassBound) : GolayExteriorPlacement.{v} := by
  intro V _ _ _ ρ _ hi hV
  let := hi
  let E := AlgebraicClosure (ULift.{v} (ZMod 2))
  obtain ⟨d, τ, habs, hτ, hd, hsections⟩ := hsmall
  obtain ⟨e, π, hirr, hπ, he⟩ := hlarge E
  let := habs
  let := hirr
  obtain ⟨i, hdi, ⟨f⟩⟩ := exists_small_equiv_of_families d e τ π hτ hπ hd he hclasses ρ hV
  exact (hsections i hdi).imp (fun h => h.of_equiv f) (fun h => h.of_equiv f)

end Representation.MathieuM24Degree44.FiveSpace
