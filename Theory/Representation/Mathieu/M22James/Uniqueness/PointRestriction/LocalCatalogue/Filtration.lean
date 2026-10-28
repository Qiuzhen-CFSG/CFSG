module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.SmallConstituents

/-!
# Two-step filtrations for twelve-dimensional binary SL₃(4) modules

The central quadratic relation descends to every submodule and quotient.
The small irreducible catalogue forces every nonzero simple submodule of a
module of dimension at most twelve to have dimension six. Consequently a
six-dimensional module with this relation is simple, and a twelve-dimensional
one has a simple submodule and simple quotient, both identified by actual
representation equivalences with the natural or dual binary action.

No faithfulness or semisimplicity hypothesis is needed. This supplies the
finite-length step for the local catalogue supporting James (1973), Lemma 8.3,
cited in Aschbacher–Smith H.12.1, printed pp.393–394.
-/

public noncomputable section
namespace Representation.SL3FourLocalCatalogue
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U)

/-- A six-dimensional module with the central relation is already simple. -/
theorem isIrreducible_of_finrank_six (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U = 6) : IsIrreducible σ := by
  let : FiniteDimensional (ZMod 2) U := .of_finrank_pos (by omega)
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) U)
  obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
  let := hN
  have hn : Module.finrank (ZMod 2) N.toSubmodule = 6 :=
    finrank_eq_six_of_irreducible N.toRepresentation
      (centralQuadratic_subrepresentation σ hq N)
      ((Submodule.finrank_le N.toSubmodule).trans (by omega))
  have ht : N = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.eq_top_of_finrank_eq (hn.trans hd.symm)
  have ha := (Subrepresentation.irreducible_iff_isAtom N).mp hN
  rw [ht] at ha
  exact isSimpleOrder_iff_isAtom_top.mpr ha

/-- The actual submodule and its actual quotient are the two six-dimensional constituents. -/
theorem exists_constituent_filtration (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U = 12) :
    ∃ (N : Subrepresentation σ) (a b : Constituent),
      Nonempty (N.toRepresentation.Equiv (constituent a)) ∧
      Nonempty (N.quotientRepresentation.Equiv (constituent b)) := by
  let : FiniteDimensional (ZMod 2) U := .of_finrank_pos (by omega)
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) U)
  obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
  let := hN
  obtain ⟨a, ⟨ea⟩⟩ := exists_constituent_equiv N.toRepresentation
    (centralQuadratic_subrepresentation σ hq N)
    ((Submodule.finrank_le N.toSubmodule).trans hd.le)
  have hn : Module.finrank (ZMod 2) N.toSubmodule = 6 :=
    ea.toLinearEquiv.finrank_eq.trans constituent_finrank
  have hdim : Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 6 := by
    have he := Submodule.finrank_quotient_add_finrank N.toSubmodule
    omega
  have hq' := centralQuadratic_quotient σ hq N
  let := isIrreducible_of_finrank_six N.quotientRepresentation hq' hdim
  obtain ⟨b, eb⟩ := exists_constituent_equiv N.quotientRepresentation hq' (by omega)
  exact ⟨N, a, b, ⟨ea⟩, eb⟩
end Representation.SL3FourLocalCatalogue
