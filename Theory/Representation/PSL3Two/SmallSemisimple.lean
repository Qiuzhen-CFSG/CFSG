module
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.SemisimpleCoinvariants

/-!
# Small semisimple binary SL₃(2) modules

The actual irreducible catalogue gives degree three or eight for every
nontrivial constituent. Thus a fixed-point-free semisimple module below
dimension six is simple, and below dimension nine it is simple or two
natural/dual-natural summands. Complementary subspaces supply literal
representation equivalences, including both mixed orientations.

Source: Aschbacher–Smith H.6.1 and 10.1.1, printed pp.386,741.
-/

public noncomputable section
open scoped MonoidAlgebra
open Representation
namespace BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Group V)

theorem constituent_finrank_ge_three_of_invariants_eq_bot
    (hfix : ρ.invariants = ⊥) (A : Subrepresentation ρ)
    (hA : A.toRepresentation.IsIrreducible) : 3 ≤ Module.finrank (ZMod 2) A.toSubmodule := by
  let : A.toRepresentation.IsIrreducible := hA
  have hn : ∃ g v, A.toRepresentation g v ≠ v := by
    by_contra! hh
    have hb : A = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      apply hfix.le
      intro g
      exact congrArg Subtype.val (hh g ⟨v,hv⟩)
    exact ((Subrepresentation.irreducible_iff_isAtom A).mp hA).ne_bot hb
  rcases IrreducibleCatalogue.classify_nontrivial A.toRepresentation hn with
    h | h | h
  · obtain ⟨e⟩ := h
    rw [e.toLinearEquiv.finrank_eq]
    simp [Vector, Matrix.PSL3Two.Fano.Vector]
  · obtain ⟨e⟩ := h
    rw [e.toLinearEquiv.finrank_eq,Subspace.dual_finrank_eq]
    simp [Vector, Matrix.PSL3Two.Fano.Vector]
  · obtain ⟨e⟩ := h
    rw [e.toLinearEquiv.finrank_eq,finrank_steinberg]
    decide

theorem submodule_finrank_ge_three_of_invariants_eq_bot
    (hfix : ρ.invariants = ⊥) (A : Subrepresentation ρ) (hA : A ≠ ⊥) :
    3 ≤ Module.finrank (ZMod 2) A.toSubmodule := by
  obtain ⟨B,hB,hBA⟩ := (eq_bot_or_exists_atom_le A).resolve_left hA
  exact (constituent_finrank_ge_three_of_invariants_eq_bot ρ hfix B
    ((Subrepresentation.irreducible_iff_isAtom B).mpr hB)).trans
    (Submodule.finrank_mono hBA)

theorem irreducible_of_semisimple_of_finrank_lt_six
    [IsSemisimpleModule (ZMod 2)[Group] ρ.asModule] [Nontrivial V]
    (hfix : ρ.invariants = ⊥) (hdim : Module.finrank (ZMod 2) V < 6) :
    ρ.IsIrreducible := by
  let : IsSemisimpleRepresentation ρ :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mpr inferInstance
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun A => ?_⟩
  by_cases hA : A = ⊥
  · exact Or.inl hA
  obtain ⟨B,hB⟩ := exists_isCompl A
  by_cases hBb : B = ⊥
  · exact Or.inr (by simpa only [hBb,sup_bot_eq] using hB.sup_eq_top)
  have ha := submodule_finrank_ge_three_of_invariants_eq_bot ρ hfix A hA
  have hb := submodule_finrank_ge_three_of_invariants_eq_bot ρ hfix B hBb
  have hdim' := Submodule.finrank_sup_add_finrank_inf_eq A.toSubmodule B.toSubmodule
  rw [←Subrepresentation.toSubmodule_sup,hB.sup_eq_top,
    ←Subrepresentation.toSubmodule_inf,hB.inf_eq_bot] at hdim'
  change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) +
    Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = _ at hdim'
  rw [finrank_top,finrank_bot,add_zero] at hdim'
  omega
end BinaryLinearThree

namespace BinaryLinearThree
open Representation
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Group V)

private theorem constituent_natural_of_small
    (hfix : ρ.invariants = ⊥) (A : Subrepresentation ρ)
    (hA : A.toRepresentation.IsIrreducible)
    (hdim : Module.finrank (ZMod 2) A.toSubmodule < 8) :
    Nonempty (A.toRepresentation.Equiv W) ∨ Nonempty (A.toRepresentation.Equiv W.dual) := by
  let : A.toRepresentation.IsIrreducible := hA
  have hn : ∃ g v, A.toRepresentation g v ≠ v := by
    by_contra! hh
    have hb : A = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      apply hfix.le
      intro g
      exact congrArg Subtype.val (hh g ⟨v,hv⟩)
    exact ((Subrepresentation.irreducible_iff_isAtom A).mp hA).ne_bot hb
  rcases IrreducibleCatalogue.classify_nontrivial A.toRepresentation hn with ha | hb | hc
  · exact Or.inl ha
  · exact Or.inr hb
  · obtain ⟨e⟩ := hc
    rw [e.toLinearEquiv.finrank_eq,finrank_steinberg] at hdim
    omega

private def sumEquiv (A B : Subrepresentation ρ) (h : IsCompl A B) :
    (A.toRepresentation.prod B.toRepresentation).Equiv ρ where
  toLinearEquiv := A.toSubmodule.prodEquivOfIsCompl B.toSubmodule
    ⟨by
      rw [disjoint_iff,←Subrepresentation.toSubmodule_inf,h.inf_eq_bot]
      rfl,
     by
      rw [codisjoint_iff,←Subrepresentation.toSubmodule_sup,h.sup_eq_top]
      rfl⟩
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact (map_add (ρ g) v.1.val v.2.val).symm

private def prodEquiv {X Y X' Y' : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup X'] [Module (ZMod 2) X']
    [AddCommGroup Y'] [Module (ZMod 2) Y']
    {α : Representation (ZMod 2) Group X} {β : Representation (ZMod 2) Group Y}
    {α' : Representation (ZMod 2) Group X'} {β' : Representation (ZMod 2) Group Y'}
    (a : α.Equiv α') (b : β.Equiv β') : (α.prod β).Equiv (α'.prod β') where
  toLinearEquiv := a.toLinearEquiv.prodCongr b.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (a.isIntertwining' g) v.1) (LinearMap.congr_fun (b.isIntertwining' g) v.2)

/-- Below dimension nine a nonzero semisimple fixed-point-free SL₃(2)-module is
simple or a sum of two natural or dual-natural modules. -/
theorem small_semisimple_alternatives
    [IsSemisimpleModule (ZMod 2)[Group] ρ.asModule] [Nontrivial V]
    (hfix : ρ.invariants = ⊥) (hdim : Module.finrank (ZMod 2) V < 9) :
    ρ.IsIrreducible ∨ Nonempty (ρ.Equiv (W.prod W)) ∨
      Nonempty (ρ.Equiv (W.prod W.dual)) ∨
      Nonempty (ρ.Equiv (W.dual.prod W)) ∨
      Nonempty (ρ.Equiv (W.dual.prod W.dual)) := by
  let : IsSemisimpleRepresentation ρ :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mpr inferInstance
  obtain ⟨A,hA⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  obtain ⟨B,hB⟩ := exists_isCompl A
  by_cases hBb : B = ⊥
  · have ht : A = ⊤ := by simpa only [hBb,sup_bot_eq] using hB.sup_eq_top
    exact Or.inl (isSimpleOrder_iff_isAtom_top.mpr
      (ht ▸ (Subrepresentation.irreducible_iff_isAtom A).mp hA))
  have ha := constituent_finrank_ge_three_of_invariants_eq_bot ρ hfix A hA
  have hb := submodule_finrank_ge_three_of_invariants_eq_bot ρ hfix B hBb
  have hd := (sumEquiv ρ A B hB).toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at hd
  have hBfix : B.toRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfix.le (fun g => congrArg Subtype.val (hv g))
  let : Nontrivial B.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h => hBb (Subrepresentation.toSubmodule_injective h))
  let i : B.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := B.toSubmodule.subtype
    isIntertwining' _ := rfl }
  let : IsSemisimpleModule (ZMod 2)[Group] B.toRepresentation.asModule :=
    IsSemisimpleModule.of_injective (IntertwiningMap.equivLinearMapAsModule _ _ i)
      Subtype.val_injective
  have hBi := irreducible_of_semisimple_of_finrank_lt_six B.toRepresentation hBfix (by omega)
  have hAc := constituent_natural_of_small ρ hfix A hA (by omega)
  have hBc := constituent_natural_of_small ρ hfix B hBi (by omega)
  let e := (sumEquiv ρ A B hB).symm
  rcases hAc with ha | ha <;> rcases hBc with hb | hb <;>
    obtain ⟨a⟩ := ha <;> obtain ⟨b⟩ := hb
  · exact Or.inr (Or.inl ⟨e.trans (prodEquiv a b)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans (prodEquiv a b)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans (prodEquiv a b)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans (prodEquiv a b)⟩)))
end BinaryLinearThree
