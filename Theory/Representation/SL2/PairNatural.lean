module
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.ProductIsotypic
public import Theory.Representation.QuadraticFourGroup.TensorClassification
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Natural constituents in both factors of a binary SL₂ product

An irreducible product representation is isotypic on either factor. Actual
copy coordinates lift the natural constituent's fixed-point-free cubic action
to the whole restriction. Applying the binary cubic-free tensor classification
to both factors gives dimension 4n over the prime field, with no faithfulness
assumption on an auxiliary actor.

The Chapter D two-kernel consumer uses this degree to construct the exact
natural tensor coordinates. Source: Aschbacher--Smith D.3.7, printed pp.198--199,
and the tensor recognition in GLS2 Theorem 25.14, Step 5 and its remarks.
-/

public noncomputable section
open Representation Subgroup
open Representation.QuadraticFourGroup Representation.QuadraticFourGroup.TensorClassification
open scoped MatrixGroups
namespace Representation.SL2.PairNatural
variable {F H V : Type*} [Field F] [Finite F] [CharP F 2] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite F] in
/-- A natural constituent detects every cubic fixed vector of its full factor restriction. -/
theorem cubic_free_of_constituent
    (σ : Representation (ZMod 2) (SL(2,F) × H) V) [σ.IsIrreducible]
    (I : Subrepresentation (ProductIsotypic.left σ)) (hI : I.toRepresentation.IsIrreducible)
    (hN : BinarySmall.IsNatural I.toRepresentation) :
    ∀ g : SL(2,F), orderOf g = 3 → FixedPointFreeAt σ (g,1) := by
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let := hI
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  let f : I.toRepresentation.IntertwiningMap (ProductIsotypic.left σ) :=
    .mk I.toSubmodule.subtype (by intro g; ext v; rfl)
  have hf : f ≠ 0 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : I.toSubmodule)
    intro hz
    exact hv (Subtype.ext (congrArg (fun f : I.toRepresentation.IntertwiningMap
      (ProductIsotypic.left σ) => f v) hz))
  obtain ⟨m,a,ha⟩ := ProductIsotypic.exists_copy_coordinates σ I.toRepresentation f hf
  obtain ⟨b⟩ := hN
  intro g hg v hv
  apply a.injective
  rw [map_zero]
  funext i
  have hfix : I.toRepresentation g (a v i) = a v i := by
    have hh := congrArg (fun w : V => a w i) hv
    simpa only [ha] using hh
  have hn : FixedPointFreeAt I.toRepresentation g :=
    (show FixedPointFreeAt BinarySmall.natural g from Matrix.SL2.cubic_fixed_eq_zero g hg).of_equiv b.symm
  exact hn _ hfix

variable {n : ℕ}

/-- Two actual natural constituents identify the full binary dimension of the square. -/
theorem degree_of_natural_constituents
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    [σ.IsIrreducible] (hn : 1 < n)
    (hl : ∃ I : Subrepresentation (σ.comp (MonoidHom.inl _ _)),
      I.toRepresentation.IsIrreducible ∧ BinarySmall.IsNatural I.toRepresentation)
    (hr : ∃ I : Subrepresentation (σ.comp (MonoidHom.inr _ _)),
      I.toRepresentation.IsIrreducible ∧ BinarySmall.IsNatural I.toRepresentation) :
    Module.finrank (ZMod 2) V = 4*n := by
  obtain ⟨I,hI,hIN⟩ := hl
  obtain ⟨J,hJ,hJN⟩ := hr
  have hl := cubic_free_of_constituent σ I hI hIN
  let swap : (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) ≃*
      (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) := MulEquiv.prodComm
  let τ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V :=
    σ.comp swap.toMonoidHom
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff swap.toMonoidHom swap.surjective σ).mpr inferInstance
  have hr := cubic_free_of_constituent τ J hJ hJN
  let e := specialLinearEquivFactor n
  let a := e.symm.prodCongr e.symm
  let μ : Representation (ZMod 2) (Factor n × Factor n) V := σ.comp a.toMonoidHom
  let : μ.IsIrreducible :=
    (irreducible_comp_surjective_iff a.toMonoidHom a.surjective σ).mpr inferInstance
  have hc : CubicFreeOnFactors μ := by
    constructor
    · intro g hg v hv
      apply hl (e.symm g) ((e.symm.orderOf_eq g).trans hg) v
      change σ (e.symm g,e.symm 1) v = v at hv
      simpa only [map_one] using hv
    · intro g hg v hv
      apply hr (e.symm g) ((e.symm.orderOf_eq g).trans hg) v
      change σ (e.symm 1,e.symm g) v = v at hv
      change σ (1,e.symm g) v = v
      simpa only [map_one] using hv
  obtain ⟨_,_,_,_,⟨b⟩⟩ := isNaturalTensorAlong_of_cubicFreeOnFactors μ hn hc
  rw [b.toLinearEquiv.finrank_eq]
  rw [← Module.finrank_mul_finrank (ZMod 2) (GaloisField 2 n) (TensorSpace n),
    GaloisField.finrank 2 (by omega)]
  simp [TensorSpace, NaturalSpace]
  omega
end Representation.SL2.PairNatural
