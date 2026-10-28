module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Defs
public import Theory.Representation.CentralizerField
public import Theory.FieldTheory.EightElementSubfield
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The actual F₈-linear centralizer in dimension six

The centralizer C of W contains the regular cyclic group X, so C acts
irreducibly. Its finite intertwining ring is therefore a field by Schur
and Wedderburn. The elements of W embed in that field. The fixed field
of the third Frobenius iterate has exactly eight elements, since it
contains the seven distinct images of W and has at most eight roots
of X⁸ − X.

These field elements act on the actual V as intertwining endomorphisms,
so every member of C is linear over that subfield. Cardinalities give
dimension two, and a basis supplies the faithful GL₂(8) representation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.12, printed p.22.
-/

open Representation Subgroup
namespace CFSG.Quasithin.ChapterA.Singer.Six
universe u

private theorem regular_overgroup_irreducible {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Nontrivial V] (X C : Subgroup (V ≃ₗ[ZMod 2] V))
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXC : X ≤ C) :
    IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp C.subtype) := by
  constructor
  intro U
  rcases hreg.invariant_eq_bot_or_top U.toSubmodule (fun x v hv =>
    U.apply_mem_toSubmodule ⟨x.val, hXC x.property⟩ hv) with h | h
  · left
    exact Subrepresentation.toSubmodule_injective h
  · right
    exact Subrepresentation.toSubmodule_injective h

/-- The full linear centralizer of the order-seven subgroup has a faithful
representation in GL₂(F₈). The scalars act on the original additive group V
by actual intertwining endomorphisms. -/
public theorem exists_centralizer_embedding {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (hn : Module.finrank (ZMod 2) V = 6)
    (X W : Subgroup (V ≃ₗ[ZMod 2] V)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X) (hWX : W ≤ X) (hW : Nat.card W = 7) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F), Nat.card F = 8 ∧
      ∃ f : centralizer (W : Set (V ≃ₗ[ZMod 2] V)) →*
        Matrix.GeneralLinearGroup (Fin 2) F, Function.Injective f := by
  classical
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  let C := centralizer (W : Set (V ≃ₗ[ZMod 2] V))
  have hXC : X ≤ C := by
    change X ≤ centralizer (W : Set (V ≃ₗ[ZMod 2] V))
    rw [← hreg.centralizer_eq]
    exact centralizer_le hWX
  let ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp C.subtype
  let : IsIrreducible ρ := regular_overgroup_irreducible X C hreg hXC
  let E := IntertwiningMap ρ ρ
  let : Field E := CentralizerField.endField ρ
  let : Finite E := CentralizerField.end_finite ρ
  let : CharP E 2 := CentralizerField.end_charP ρ 2
  let f : W →* E :=
    { toFun w :=
        { toLinearMap := w.val.toLinearMap
          isIntertwining' c := LinearMap.ext fun v =>
            LinearEquiv.congr_fun (mem_centralizer_iff.mp c.property w.val w.property) v }
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    ext v
    exact congrArg (fun e : E => e v) hab
  let F := FiniteField.eightSubfield E
  have hF : Nat.card F = 8 := FiniteField.eightSubfield_card_eq hW f hf
  let : Module E V := End.applyModule
  let : Module F V := inferInstance
  let : FiniteDimensional F V := Module.Finite.of_finite
  have hd : Module.finrank F V = 2 := by
    have hcard := Module.natCard_eq_pow_finrank (K := F) (V := V)
    rw [hF] at hcard
    have hv : Nat.card V = 64 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hn]
      norm_num
    rw [hv] at hcard
    exact Nat.pow_right_injective (by decide : 1 < 8) hcard.symm
  let σ : C →* (V ≃ₗ[F] V) :=
    { toFun c :=
        { c.val.toAddEquiv with
          map_smul' a v := by
            change c.val ((a.val : E) v) = (a.val : E) (c.val v)
            exact (IntertwiningMap.isIntertwining ρ ρ a.val c v).symm }
      map_one' := by ext v; rfl
      map_mul' _ _ := by ext v; rfl }
  have hσ : Function.Injective σ := by
    intro c d he
    apply Subtype.ext
    ext v
    exact LinearEquiv.congr_fun he v
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' (Module.finBasisOfFinrankEq F V hd)).symm
  exact ⟨↥F, inferInstance, inferInstance, hF, e.toMonoidHom.comp σ, e.injective.comp hσ⟩

end CFSG.Quasithin.ChapterA.Singer.Six
