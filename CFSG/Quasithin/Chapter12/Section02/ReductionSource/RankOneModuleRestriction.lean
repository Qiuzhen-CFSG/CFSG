module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.AlternatingCopies
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# Restricting the whole rank-one module exit to the original choice

The chosen Irr⁺ subgroup may be properly contained in the commutator layer.
The one-copy and two-copy coordinate systems are converted to an embedded
indexed sum, preserving the given L/O₂(L) marking. The existing irreducible
section theorem then identifies the original subgroup with one A₅ module.

Source: Aschbacher--Smith, 12.2.2(3d), p.795, using 6.2.20 and A.1.40.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V W : Subgroup G}
  (D : ChosenModule T L V)
include D

private theorem model_of_coordinates {ι : Type*}
    (hVW : V ≤ W)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : W ≃* Multiplicative (ι → BinaryPermutation.natural (Fin 5)))
    (ha : ∀ (l : L) (w : W),
      ((f.symm (Multiplicative.ofAdd (fun i => Chapter6.Source.a5Module
        (e (QuotientGroup.mk' (pCore 2 L) l)) ((f w).toAdd i)))) : G) =
          (l : G) * (w : G) * (l : G)⁻¹) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  apply D.a5_model_of_embedded_copies e (W.subtype.comp f.symm.toMonoidHom)
    (W.subtype_injective.comp f.symm.injective)
  · intro v hv
    exact ⟨f ⟨v, hVW hv⟩, congrArg (fun w : W => (w : G)) (f.symm_apply_apply _)⟩
  · intro l v
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, toAdd_ofAdd, f.apply_symm_apply] using
      ha l (f.symm (Multiplicative.ofAdd v))

/-- A model on an overgroup restricts to the original Irr⁺ choice, with
no normalization or reducedness assumption on the choice. -/
theorem a5_model_of_one_or_two_on_overgroup (hVW : V ≤ W) (h : Chapter6.Source.IsOneOrTwoA5Modules L W) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  rcases h with ⟨e, f, hf⟩ | ⟨e, f, hf⟩
  · let c : (Unit → BinaryPermutation.natural (Fin 5)) ≃+
        BinaryPermutation.natural (Fin 5) := AddEquiv.funUnique Unit _
    apply D.model_of_coordinates hVW e (f.trans c.toMultiplicative.symm)
    intro l w
    exact hf l w
  · let c := (LinearEquiv.finTwoArrow (ZMod 2)
        (BinaryPermutation.natural (Fin 5))).toAddEquiv
    apply D.model_of_coordinates hVW e (f.trans c.toMultiplicative.symm)
    intro l w
    exact hf l w
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
