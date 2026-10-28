module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Seven.Descent
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# The A₇ and triple-A₇ Sylow-fixing actions in E.6.8

The literal model isomorphism, or the central quotient isomorphism of the
quasisimple triple cover, supplies the equivariant projection onto A₇.
In the cover case its kernel is exactly the original center of order three,
and perfectness gives faithful descent of automorphisms. The seven-letter
calculation then bounds the actor by four and proves fixed-point generation
when its order is four.

This is an intrinsic model calculation. Constructing the ambient action,
pulling its lines back to hyperplanes, and E.6.8's final source assembly
remain with the importing source owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.8(4),
printed pp.247--248, and 1.1.5(3)(d), printed pp.501--502.
-/

public section

open Subgroup Equiv
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
namespace Seven
variable {X : Type*} [Group X]

open Theory.GroupTheory

/-- The intrinsic calculation for an actual A₇ model. -/
theorem equiv_calculations [Finite X] (e : X ≃* A7)
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (S : Sylow 2 X) (hfix : ∀ α ∈ E, ∀ x ∈ (S : Subgroup X), α x = x) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (⊤ : Subgroup X) ≤ ⨆ (α : E) (_ : α ≠ 1), fixedSubgroup (α : MulAut X)) := by
  let : Group.IsPerfect A7 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hker (c : X) (hc : c ∈ e.toMonoidHom.ker) : c = 1 :=
    e.injective ((MonoidHom.mem_ker.mp hc).trans e.map_one.symm)
  apply projection_calculations e.toMonoidHom e.surjective
    (fun c hc => hker c hc ▸ (center X).one_mem)
    (fun c hc => by rw [hker c hc, one_pow])
    (MulAut.congr e).toMonoidHom (MulAut.congr e).injective ?_ E S hfix
  intro α x
  change e (α (e.symm (e x))) = e (α x)
  rw [e.symm_apply_apply]

/-- The intrinsic calculation for the genuine perfect triple cover of A₇.
Only injective descent is used; surjectivity on automorphism groups is unnecessary. -/
theorem cover_calculations [Finite X] [IsQuasisimple X]
    (e : (X ⧸ center X) ≃* A7) (hZ : Nat.card (center X) = 3)
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (S : Sylow 2 X) (hfix : ∀ α ∈ E, ∀ x ∈ (S : Subgroup X), α x = x) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (⊤ : Subgroup X) ≤ ⨆ (α : E) (_ : α ≠ 1), fixedSubgroup (α : MulAut X)) := by
  let f : X →* A7 := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hker : f.ker = center X := by
    ext x
    change e ((QuotientGroup.mk' (center X)) x) = 1 ↔ x ∈ center X
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let F : PerfectCentralCovering.Cover X A7 :=
    { toMonoidHom := f
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := hker.le }
  have hcube (c : X) (hc : c ∈ f.ker) : c ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨c, hker ▸ hc⟩ : center X))
    rw [hZ] at hh
    exact congrArg Subtype.val hh
  exact projection_calculations f F.surjective hker.le hcube
    (F.autMap hker) (F.autMap_injective hker) (F.autMap_apply hker) E S hfix

end Seven
open Seven Theory.GroupTheory Chapter15.Section03.Candidates.ComponentStructure

/-- The intrinsic A₇ and triple-A₇ calculations used in E.6.8(4).
The stronger model calculations above hold for every Sylow-fixing elementary
actor; the marked cycle-type action is retained in this source-facing interface. -/
theorem seven_image_calculations {X : Type*} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (S : Sylow 2 X) (hfix : ∀ a ∈ E, ∀ x ∈ (S : Subgroup X), a x = x)
    (α : MulAut X) (_hα : α ∈ E) (σ : Equiv.Perm (Fin 7))
    (_hσ : σ.cycleType = {2, 2, 2}) (ha : AlternatingAction α 7 σ) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (⊤ : Subgroup X) ≤ ⨆ (a : E) (_ : a ≠ 1), fixedSubgroup (a : MulAut X)) := by
  rcases ha with ⟨e, _⟩ | ⟨hq, ⟨eZ⟩, e, _⟩
  · exact equiv_calculations e E S hfix
  · let : IsQuasisimple X := hq
    have hZ : Nat.card (center X) = 3 := by
      rw [Nat.card_congr eZ.toEquiv, Nat.card_eq_fintype_card]
      decide
    exact cover_calculations e hZ E S hfix

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
