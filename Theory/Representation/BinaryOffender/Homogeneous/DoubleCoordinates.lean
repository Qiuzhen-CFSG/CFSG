module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry
public import Mathlib.LinearAlgebra.Projection
/-!
# Coordinates on a proper homogeneous double

A proper simple constituent cannot contain the whole homogeneous component.
Thus a second copy exists. Distinct simple submodules are disjoint; if the
ambient degree is at most twice the constituent degree, these copies span
and their addition map gives an actual intertwining product equivalence.

This is the multiplicity-two step used in Aschbacher--Smith G.11.7,
printed p.366. The application to the original terminal A₆ action is in
Chapter14's SmallRows.AlternatingSixActionSourceMultiplicity.
-/

public noncomputable section
open Representation Module
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

/-- A proper homogeneous constituent fills the module with exactly two copies
once the degree bound is supplied. -/
theorem double_coordinates_of_degree_le (I : Subrepresentation ρ) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤) (hp : I.toSubmodule ≠ ⊤)
    (hd : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) I.toSubmodule) :
    Nonempty (ρ.Equiv (I.toRepresentation.prod I.toRepresentation)) := by
  classical
  obtain ⟨J,hJ,hJI⟩ : ∃ J : Subrepresentation ρ, SameModule I J ∧ ¬ J ≤ I := by
    by_contra! h
    apply hp
    apply top_unique
    rw [← hh]
    exact iSup_le fun J => iSup_le fun hJ => h J hJ.2
  have hj : IsIrreducible J.toRepresentation := hJ.irreducible hi
  have heq : I ≠ J := fun he => hJI (he ▸ le_rfl)
  have hdis : Disjoint I.toSubmodule J.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      (((Subrepresentation.irreducible_iff_isAtom I).mp hi).disjoint_of_ne
        ((Subrepresentation.irreducible_iff_isAtom J).mp hj) heq).eq_bot
  obtain ⟨e,he⟩ := hJ
  have hcompl : IsCompl I.toSubmodule J.toSubmodule := by
    refine ⟨hdis,codisjoint_iff.mpr ?_⟩
    apply Submodule.eq_top_of_finrank_eq
    have hs := Submodule.finrank_sup_add_finrank_inf_eq I.toSubmodule J.toSubmodule
    rw [hdis.eq_bot,finrank_bot,add_zero,← e.finrank_eq] at hs
    exact le_antisymm (Submodule.finrank_le _) (by omega)
  let q := Submodule.prodEquivOfIsCompl I.toSubmodule J.toSubmodule hcompl
  let c := (LinearEquiv.refl (ZMod 2) I.toSubmodule).prodCongr e
  let f : (I.toRepresentation.prod I.toRepresentation).Equiv ρ :=
    .mk (c.trans q) (by
      intro a
      apply LinearMap.ext
      intro w
      change (I.toRepresentation a w.1 : V) + (e (I.toRepresentation a w.2) : V) =
        ρ a ((w.1 : V) + (e w.2 : V))
      rw [he,map_add]
      rfl)
  exact ⟨f.symm⟩
end Representation.BinaryOffender.Homogeneous
