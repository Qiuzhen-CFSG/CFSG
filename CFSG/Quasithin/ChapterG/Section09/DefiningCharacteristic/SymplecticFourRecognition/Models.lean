module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.FirstCohomologyCyclic
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Mathlib.Algebra.Module.ZMod

/-!
# The natural module in G.9.3(9)

The model is the actual commutator subgroup of the symplectic matrix group,
acting on four coordinates over its defining field, restricted to F₂.
Entrywise field transport intertwines these actions, including at the
smallest parameter. Its binary dimension is four times the field degree.
These constructions specify the recognition target; they do not classify
arbitrary irreducible modules.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(9),
printed pp.354,356--357. The defining-field convention also occurs in I.1.6(5).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition

open Representation
open Theory.SpecificGroups.SymplecticFour.Binary

/-- The binary natural action of the literal derived matrix group. -/
abbrev binaryNatural (F : Type*) [Field F] [Algebra (ZMod 2) F] :
    Representation (ZMod 2) (commutator (Matrix.symplecticGroup (Fin 2) F))
      ((Fin 2 ⊕ Fin 2) → F) :=
  restrictScalars (k := ZMod 2) (symplecticDerivedNatural (k := F) 2)

variable {F E : Type*} [Field F] [Algebra (ZMod 2) F]
  [Field E] [Algebra (ZMod 2) E]

/-- Restricting coefficients does not lose faithfulness of the matrix action. -/
theorem binaryNatural_faithful : Function.Injective (binaryNatural F) := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact congrArg (fun f : Module.End (ZMod 2) ((Fin 2 ⊕ Fin 2) → F) => f v) hgh

/-- Dimension over the prime field, retaining its actual scalar restriction. -/
theorem binaryNatural_finrank [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) ((Fin 2 ⊕ Fin 2) → F) = 4 * n := by
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  rw [Module.finrank_pi_fintype]
  simp [Representation.OneCohomology.coefficient_finrank_of_card 2 n hF]

private noncomputable def derivedFieldEquiv (e : F ≃+* E) :
    commutator (Matrix.symplecticGroup (Fin 2) F) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) E) :=
  ((fieldEquivSp e).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (fieldEquivSp e).surjective, commutator_def]))

private def vectorFieldEquiv (e : F ≃+* E) :
    ((Fin 2 ⊕ Fin 2) → F) ≃ₗ[ZMod 2] ((Fin 2 ⊕ Fin 2) → E) :=
  { AddEquiv.piCongrRight (fun _ => e.toAddEquiv) with
    map_smul' := ZMod.map_smul (AddEquiv.piCongrRight (fun _ : Fin 2 ⊕ Fin 2 => e.toAddEquiv)) }

/-- Actual group and module equivalences accompany every change of field model. -/
theorem binaryNatural_quasiequivalent_of_fieldEquiv (e : F ≃+* E) :
    Quasiequivalent (binaryNatural F) (binaryNatural E) := by
  refine ⟨derivedFieldEquiv e, vectorFieldEquiv e, ?_⟩
  intro g v
  funext i
  change e (∑ j, g.val.val i j * v j) = ∑ j, e (g.val.val i j) * e (v j)
  simp only [map_sum, map_mul]

variable {D : Type*} [Group D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- Recognition is unchanged when the finite-field witness is replaced by an
isomorphic field. The intertwining linear map is transported, not inferred from dimension. -/
theorem quasiequivalent_natural_field_iff (e : F ≃+* E) :
    Quasiequivalent ρ (binaryNatural F) ↔ Quasiequivalent ρ (binaryNatural E) := by
  constructor
  · rintro ⟨a, b, hb⟩
    obtain ⟨c, d, hd⟩ := binaryNatural_quasiequivalent_of_fieldEquiv e
    refine ⟨a.trans c, b.trans d, ?_⟩
    intro g v
    exact (congrArg d (hb g v)).trans (hd (a g) (b v))
  · rintro ⟨a, b, hb⟩
    obtain ⟨c, d, hd⟩ := binaryNatural_quasiequivalent_of_fieldEquiv e.symm
    refine ⟨a.trans c, b.trans d, ?_⟩
    intro g v
    exact (congrArg d (hb g v)).trans (hd (a g) (b v))

/-- At the smallest parameter, scalar restriction to the literal binary field
preserves the actual module identification. -/
theorem quasiequivalent_natural_binary_iff [Finite F] (hF : Nat.card F = 2) :
    Quasiequivalent ρ (binaryNatural F) ↔ Quasiequivalent ρ (binaryNatural (ZMod 2)) :=
  quasiequivalent_natural_field_iff (fieldEquivZModTwo F hF)

/-- An actual natural-module identification gives the degree in G.9.3(9). -/
theorem finrank_of_quasiequivalent [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h : Quasiequivalent ρ (binaryNatural F)) : Module.finrank (ZMod 2) V = 4 * n := by
  obtain ⟨_, f, _⟩ := h
  exact f.finrank_eq.trans (binaryNatural_finrank hF)

/-- Transport a recognition theorem on the model back to the original component. -/
theorem quasiequivalent_of_comp_equiv
    (e : D ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    (h : Quasiequivalent (ρ.comp e.symm.toMonoidHom) (binaryNatural F)) :
    Quasiequivalent ρ (binaryNatural F) := by
  obtain ⟨a, b, hb⟩ := h
  refine ⟨e.trans a, b, ?_⟩
  intro g v
  have hh := hb (e g) v
  change b (ρ (e.symm (e g)) v) = binaryNatural F (a (e g)) (b v) at hh
  simpa only [MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using hh

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
