module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Mathlib.FieldTheory.Finiteness

/-!
# The binary A₅ module as a conjugation action

The coordinates identify a normal subgroup with the four-dimensional
augmentation kernel on five letters and identify its actual quotient actor
with A₅. The conjugation equation retains every element of the extension.
The module has order sixteen. It cannot be the natural SL₂ plane over a
field of characteristic two: a cubic element has a nonzero fixed vector
in the permutation core, whereas a nonidentity cubic matrix has none in
that plane.

Source application: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, and
the L₂(4)-block alternatives (6)–(7) of A.3.14, printed p.49. The theorem
constructing the particular local section is a separate obligation.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace BinaryPermutation
universe u
variable (X : Type u) [Group X]

/-- Actual group and module coordinates for a binary A₅ conjugation action. -/
structure FiveConjugation (V : Subgroup X) [V.Normal] where
  coordinates : V ≃* Multiplicative (BinaryPermutation.core (Fin 5))
  actor : (X ⧸ V) ≃* alternatingGroup (Fin 5)
  equivariant : ∀ (g : X) (v : V),
    coordinates ⟨g * v * g⁻¹, (inferInstance : V.Normal).conj_mem v v.property g⟩ =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
        (actor (QuotientGroup.mk' V g)).val (coordinates v).toAdd)

variable {X} {V : Subgroup X} [V.Normal]

/-- The normal module has exactly sixteen elements. -/
theorem FiveConjugation.card (h : FiveConjugation X V) : Nat.card V = 16 := by
  calc
    Nat.card V = Nat.card (BinaryPermutation.core (Fin 5)) :=
      Nat.card_congr h.coordinates.toEquiv
    _ = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        BinaryPermutation.finrank_core]
      rfl

/-- Conjugation in the binary A₅ module cannot also be a natural SL₂
plane in characteristic two, even after changing both coordinate systems. -/
theorem FiveConjugation.no_natural_plane {F : Type*} [Field F] [CharP F 2]
    (h : FiveConjugation X V)
    (e : V ≃* Multiplicative (Fin 2 → F))
    (ρ : (X ⧸ V) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hρ : ∀ (g : X) (v : V),
      e ⟨g * v * g⁻¹, (inferInstance : V.Normal).conj_mem v v.property g⟩ =
        Multiplicative.ofAdd
          (Matrix.mulVec (ρ (QuotientGroup.mk' V g)).val (e v).toAdd)) : False := by
  let f := (h.actor.symm.trans ρ).toMonoidHom
  let eadd : BinaryPermutation.core (Fin 5) →+ (Fin 2 → F) :=
    { toFun := fun w => (e (h.coordinates.symm (Multiplicative.ofAdd w))).toAdd
      map_zero' := by simp
      map_add' := by
        intro w w'
        change (e (h.coordinates.symm (Multiplicative.ofAdd w *
          Multiplicative.ofAdd w'))).toAdd = _
        rw [map_mul, map_mul]
        rfl }
  have hei : Function.Injective eadd := by
    intro w w' he
    exact h.coordinates.symm.injective (e.injective he)
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_core_injection
    f (h.actor.symm.trans ρ).injective eadd hei
  intro a w
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective V (h.actor.symm a)
  let v := h.coordinates.symm (Multiplicative.ofAdd w)
  have ha : h.actor (QuotientGroup.mk' V g) = a := by rw [hg]; simp
  have hv := h.equivariant g v
  rw [ha] at hv
  have hw : h.coordinates v = Multiplicative.ofAdd w := h.coordinates.apply_symm_apply _
  rw [hw] at hv
  change (e (h.coordinates.symm (Multiplicative.ofAdd
    (BinaryPermutation.coreRepresentation (Fin 5) a.val w)))).toAdd = _
  calc
    _ = (e ⟨g * v * g⁻¹, (inferInstance : V.Normal).conj_mem v v.property g⟩).toAdd := by
      simpa only [MulEquiv.symm_apply_apply, toAdd_ofAdd] using
        congrArg (fun y => (e (h.coordinates.symm y)).toAdd) hv.symm
    _ = _ := by
      simpa [hg, f, eadd, v] using congrArg Multiplicative.toAdd (hρ g v)

end BinaryPermutation
