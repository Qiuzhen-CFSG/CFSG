module
public import Theory.Representation.ProductIsotypic.TwoConstituents
public import Theory.Representation.BinaryTensorThree.NormalizerNonFF
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Absolute
public import Theory.Representation.BinaryAbsoluteExtension
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Recognizing tensors from the two original factor restrictions

An irreducible product module moved by a factor contains a nontrivial simple
type for that factor: otherwise the isotypic copy coordinates make its whole
action trivial. If both factor types are natural binary three-spaces, absolute
irreducibility and the two-constituent tensor theorem construct the actual
nine-dimensional tensor marking. The coordinate equivalence is the literal
matrix tensor equivalence used by the normalizer and offender calculations.

The group marking may change independently on the two factors, so this includes
both natural and dual orientations. An arbitrary product isomorphism is retained
when transporting back to the original normal component orbit.
Source: Aschbacher--Smith D.3.7 and F.9.18(5), printed pp.197--199,325--326;
the terminal14.6.22 consumer is in ComponentSupports/Modules/Recognition.
-/

public noncomputable section
open Representation Representation.ProductIsotypic
open Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace BinaryTensorThree
variable {D J L V : Type*} [_root_.Group D] [_root_.Group J] [_root_.Group L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A moving factor has a natural constituent map when all of its nontrivial simple types are natural. -/
theorem exists_natural_map_of_moving_left
    (ρ : Representation (ZMod 2) (J × L) V) [ρ.IsIrreducible]
    (hm : ρ.comp (MonoidHom.inl J L) ≠ 1)
    (htypes : ∀ S : Subrepresentation (ρ.comp (MonoidHom.inl J L)),
      S.toRepresentation.IsIrreducible → S.toRepresentation ≠ 1 →
        ∃ e : J ≃* BinaryLinearThree.Group,
          Nonempty (S.toRepresentation.Equiv (BinaryLinearThree.W.comp e.toMonoidHom))) :
    ∃ e : J ≃* BinaryLinearThree.Group,
      ∃ f : Representation.IntertwiningMap (BinaryLinearThree.W.comp e.toMonoidHom)
        (ρ.comp (MonoidHom.inl J L)), f ≠ 0 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨S,hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp (MonoidHom.inl J L))
  let := hS
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  let inc : S.toRepresentation.IntertwiningMap (ρ.comp (MonoidHom.inl J L)) :=
    .mk S.toSubmodule.subtype (fun _ => rfl)
  have hi : inc ≠ 0 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
    intro hz
    exact hv (Subtype.ext (congrArg
      (fun q : S.toRepresentation.IntertwiningMap (ρ.comp (MonoidHom.inl J L)) => q v) hz))
  have hmove : S.toRepresentation ≠ 1 := by
    intro hz
    obtain ⟨n,c,hc⟩ := exists_copy_coordinates ρ S.toRepresentation inc hi
    apply hm
    ext j v
    apply c.injective
    change c (ρ (j,1) v) = c v
    rw [hc,hz]
    rfl
  obtain ⟨e,⟨b⟩⟩ := htypes S hS hmove
  let f := inc.comp b.symm.toIntertwiningMap
  refine ⟨e,f,?_⟩
  intro hz
  apply hi
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hh := congrArg (fun q : Representation.IntertwiningMap
    (BinaryLinearThree.W.comp e.toMonoidHom) (ρ.comp (MonoidHom.inl J L)) => q (b v)) hz
  change inc (b.toLinearEquiv.symm (b.toLinearEquiv v)) = 0 at hh
  rw [b.toLinearEquiv.symm_apply_apply] at hh
  exact hh

/-- Natural types occurring on both factors construct the full tensor marking. -/
theorem exists_marking_of_natural_factor_maps
    (ρ : Representation (ZMod 2) (J × L) V) [ρ.IsIrreducible]
    (eJ : J ≃* BinaryLinearThree.Group) (eL : L ≃* BinaryLinearThree.Group)
    (f : Representation.IntertwiningMap (BinaryLinearThree.W.comp eJ.toMonoidHom)
      (ρ.comp (MonoidHom.inl J L))) (hf : f ≠ 0)
    (g : Representation.IntertwiningMap (BinaryLinearThree.W.comp eL.toMonoidHom)
      (ρ.comp (MonoidHom.inr J L))) (hg : g ≠ 0) :
    ∃ e : (J × L) ≃* (Factor × Factor),
      Nonempty (ρ.Equiv (baseRepresentation.comp e.toMonoidHom)) := by
  let σ : Representation (ZMod 2) J BinaryLinearThree.Vector := BinaryLinearThree.W.comp eJ.toMonoidHom
  let τ : Representation (ZMod 2) L BinaryLinearThree.Vector := BinaryLinearThree.W.comp eL.toMonoidHom
  let : σ.IsAbsolutelyIrreducible := binary_absolute_comp_surjective
    BinaryLinearThree.W eJ.toMonoidHom eJ.surjective BinaryLinearThree.IrreducibleCatalogue.natural_absolute
  let : σ.IsIrreducible := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible σ
  let : τ.IsAbsolutelyIrreducible := binary_absolute_comp_surjective
    BinaryLinearThree.W eL.toMonoidHom eL.surjective BinaryLinearThree.IrreducibleCatalogue.natural_absolute
  let : τ.IsIrreducible := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible τ
  obtain ⟨b⟩ := externalTensor_of_two_constituents ρ σ τ f hf g hg
  let a := BinaryLinear.OuterCyclic.slEquivLinear 3
  let e := (eJ.trans a).prodCongr (eL.trans a)
  let c : (externalTensor σ τ).Equiv (baseRepresentation.comp e.toMonoidHom) :=
    Representation.Equiv.mk coordinates (by
      intro x
      apply LinearMap.ext
      intro z
      induction z using _root_.TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simpa only [LinearMap.comp_apply,map_add] using congrArg₂ (· + ·) hz hw
      | tmul u v =>
        change coordinates (σ x.1 u ⊗ₜ[ZMod 2] τ x.2 v) =
          baseAction (e x) (coordinates (u ⊗ₜ[ZMod 2] v))
        rw [baseAction_tmul]
        rfl)
  exact ⟨e,⟨b.trans c⟩⟩

/-- A product constituent moved by both factors is the tensor when their simple types are natural. -/
theorem exists_marking_of_moving_natural_types
    (ρ : Representation (ZMod 2) (J × L) V) [ρ.IsIrreducible]
    (hJ : ρ.comp (MonoidHom.inl J L) ≠ 1)
    (hL : ρ.comp (MonoidHom.inr J L) ≠ 1)
    (htJ : ∀ S : Subrepresentation (ρ.comp (MonoidHom.inl J L)),
      S.toRepresentation.IsIrreducible → S.toRepresentation ≠ 1 →
        ∃ e : J ≃* BinaryLinearThree.Group,
          Nonempty (S.toRepresentation.Equiv (BinaryLinearThree.W.comp e.toMonoidHom)))
    (htL : ∀ S : Subrepresentation (ρ.comp (MonoidHom.inr J L)),
      S.toRepresentation.IsIrreducible → S.toRepresentation ≠ 1 →
        ∃ e : L ≃* BinaryLinearThree.Group,
          Nonempty (S.toRepresentation.Equiv (BinaryLinearThree.W.comp e.toMonoidHom))) :
    ∃ e : (J × L) ≃* (Factor × Factor),
      Nonempty (ρ.Equiv (baseRepresentation.comp e.toMonoidHom)) := by
  obtain ⟨eJ,f,hf⟩ := exists_natural_map_of_moving_left ρ hJ htJ
  let a : (L × J) ≃* (J × L) := MulEquiv.prodComm
  let σ : Representation (ZMod 2) (L × J) V := ρ.comp a.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff a.toMonoidHom a.surjective ρ).mpr inferInstance
  obtain ⟨eL,g,hg⟩ := exists_natural_map_of_moving_left σ hL htL
  exact exists_marking_of_natural_factor_maps ρ eJ eL f hf g hg

/-- Transport tensor recognition back through the original product isomorphism. -/
theorem exists_marking_of_restricted_natural_maps
    (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible]
    (a : D ≃* (J × L))
    (eJ : J ≃* BinaryLinearThree.Group) (eL : L ≃* BinaryLinearThree.Group)
    (f : Representation.IntertwiningMap (BinaryLinearThree.W.comp eJ.toMonoidHom)
      ((ρ.comp a.symm.toMonoidHom).comp (MonoidHom.inl J L))) (hf : f ≠ 0)
    (g : Representation.IntertwiningMap (BinaryLinearThree.W.comp eL.toMonoidHom)
      ((ρ.comp a.symm.toMonoidHom).comp (MonoidHom.inr J L))) (hg : g ≠ 0) :
    ∃ e : D ≃* (Factor × Factor),
      Nonempty (ρ.Equiv (baseRepresentation.comp e.toMonoidHom)) := by
  let σ : Representation (ZMod 2) (J × L) V := ρ.comp a.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective ρ).mpr inferInstance
  obtain ⟨e,⟨b⟩⟩ := exists_marking_of_natural_factor_maps σ eJ eL f hf g hg
  refine ⟨a.trans e,⟨Representation.Equiv.mk b.toLinearEquiv ?_⟩⟩
  intro d
  have hb := b.isIntertwining' (a d)
  simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,a.symm_apply_apply,
    MulEquiv.trans_apply] using hb

end BinaryTensorThree

namespace BinaryTensorThree
variable {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- Every simple constituent of the normal pair on an irreducible ambient
subquotient is supported on one of the two marked factors. -/
@[expose] def HasSingleFactorConstituents
    (ρ : Representation (ZMod 2) D V) (N K : Subgroup D) (p : N ≃* (K × K)) : Prop :=
  ∀ (S : Subrepresentation ρ) (L : Subrepresentation S.toRepresentation),
    IsIrreducible L.quotientRepresentation →
    ∀ U : Subrepresentation (L.quotientRepresentation.comp N.subtype),
      IsIrreducible U.toRepresentation →
      let σ := U.toRepresentation.comp p.symm.toMonoidHom
      σ.comp (MonoidHom.inl K K) = 1 ∨ σ.comp (MonoidHom.inr K K) = 1

end BinaryTensorThree
