module

public import Theory.Representation.BinaryOffender.FixedGenerator
public import Mathlib.Order.Atoms.Finite

/-!
# Reducing a splitting problem to extensions of two factors

Among invariant supplements to W, choose one of least dimension. If its
intersection with W is nonzero, split the section above a maximal proper
submodule of that intersection. Lifting the complement gives a smaller
supplement, a contradiction. When W is maximal, every section used here has
exactly two simple factors. An invariant complement then gives a linear,
equivariant right inverse of the actual quotient map.

The final theorem combines this reduction with the unique-maximal obstruction.
It does not assert the two-factor splitting hypothesis: applying B.4.9(1)
requires natural-module identifications, the four-group with a common axis,
and quadratic action on the extension.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed p.92, and its uses in 13.8.25,
printed p.961 (PDF p.978).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- Splitting of every simple-kernel section of a supplement forces an actual
invariant complement. The proof minimizes the dimension of a supplement;
splitting a final simple layer would otherwise produce a smaller one. -/
theorem exists_complement_of_two_step_splitting
    (W : Subrepresentation ρ)
    (hstep : ∀ X : Subrepresentation ρ, X ⊔ W = ⊤ →
      ∀ Y : Subrepresentation ρ, Y ⋖ X ⊓ W →
        ∃ C : Subrepresentation ρ, C ≤ X ∧ C ⊔ (X ⊓ W) = X ∧
          C ⊓ (X ⊓ W) = Y) :
    ∃ X : Subrepresentation ρ, X ⊓ W = ⊥ ∧ X ⊔ W = ⊤ := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun X : Subrepresentation ρ => (X : Set U)) SetLike.coe_injective
  obtain ⟨X, hX, hmin⟩ := Set.exists_min_image
    {X : Subrepresentation ρ | X ⊔ W = ⊤}
    (fun X => Module.finrank (ZMod 2) X.toSubmodule) (Set.toFinite _) ⟨⊤, top_sup_eq _⟩
  refine ⟨X, ?_, hX⟩
  by_contra hbot
  obtain ⟨Y, _, hY⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr hbot)
  obtain ⟨C, hCX, hsup, hinf⟩ := hstep X hX Y hY
  have hCW : C ⊔ W = ⊤ := by
    apply top_unique
    rw [← hX, ← hsup]
    exact sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right)) le_sup_right
  have hlt : C < X := by
    refine lt_of_le_of_ne hCX ?_
    intro he
    have heY : X ⊓ W = Y := by simpa only [he, ← inf_assoc, inf_idem] using hinf
    exact hY.ne heY.symm
  have := hmin C hCW
  have := Submodule.finrank_lt_finrank_of_lt (show C.toSubmodule < X.toSubmodule from hlt)
  omega

omit [FiniteDimensional (ZMod 2) U] in
/-- An invariant complement supplies a section of the literal quotient map,
with equivariance checked against the induced quotient action. -/
theorem exists_equivariant_section_of_complement
    (W X : Subrepresentation ρ) (hinf : X ⊓ W = ⊥) (hsup : X ⊔ W = ⊤) :
    ∃ s : (U ⧸ W.toSubmodule) →ₗ[ZMod 2] U,
      (∀ g q, s (W.quotientRepresentation g q) = ρ g (s q)) ∧
      Function.RightInverse s W.toSubmodule.mkQ := by
  have hc : IsCompl W.toSubmodule X.toSubmodule := by
    constructor
    · apply disjoint_iff.mpr
      have he : X.toSubmodule ⊓ W.toSubmodule = ⊥ :=
        congrArg Subrepresentation.toSubmodule hinf
      simpa only [inf_comm] using he
    · apply codisjoint_iff.mpr
      have he : X.toSubmodule ⊔ W.toSubmodule = ⊤ :=
        congrArg Subrepresentation.toSubmodule hsup
      simpa only [sup_comm] using he
  let e := W.toSubmodule.quotientEquivOfIsCompl X.toSubmodule hc
  let s := X.toSubmodule.subtype.comp e.toLinearMap
  have hsection : Function.RightInverse s W.toSubmodule.mkQ := by
    intro q
    exact Submodule.mk_quotientEquivOfIsCompl_apply hc q
  refine ⟨s, ?_, hsection⟩
  intro g q
  have hmem : ρ g (s q) ∈ X := X.apply_mem_toSubmodule g (e q).property
  have hq : e.symm ⟨ρ g (s q), hmem⟩ = W.quotientRepresentation g q := by
    change W.toSubmodule.mkQ (ρ g (s q)) = _
    rw [← Subrepresentation.quotientRepresentation_mk, hsection]
  have := congrArg (fun x : X.toSubmodule => (x : U)) (e.apply_symm_apply ⟨ρ g (s q), hmem⟩)
  rw [hq] at this
  exact this

/-- The finite-length splitting induction, ending in an actual equivariant
section rather than a bare assertion that the module splits. -/
theorem equivariant_section_of_two_step_splitting
    (W : Subrepresentation ρ)
    (hstep : ∀ X : Subrepresentation ρ, X ⊔ W = ⊤ →
      ∀ Y : Subrepresentation ρ, Y ⋖ X ⊓ W →
        ∃ C : Subrepresentation ρ, C ≤ X ∧ C ⊔ (X ⊓ W) = X ∧
          C ⊓ (X ⊓ W) = Y) :
    ∃ s : (U ⧸ W.toSubmodule) →ₗ[ZMod 2] U,
      (∀ g q, s (W.quotientRepresentation g q) = ρ g (s q)) ∧
      Function.RightInverse s W.toSubmodule.mkQ := by
  obtain ⟨X, hinf, hsup⟩ := exists_complement_of_two_step_splitting ρ W hstep
  exact exists_equivariant_section_of_complement ρ W X hinf hsup

/-- A nonzero unique maximal submodule forces a nonsplit two-step section.
Thus a theorem about extensions of two simple factors suffices; no splitting
of the whole module is assumed. -/
theorem exists_nonsplit_two_step_of_unique_maximal
    (W : Subrepresentation ρ) (hW : IsCoatom W) (hW0 : W ≠ ⊥)
    (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W) :
    ∃ X : Subrepresentation ρ, X ⊔ W = ⊤ ∧
      ∃ Y : Subrepresentation ρ, Y ⋖ X ⊓ W ∧
        ¬ ∃ C : Subrepresentation ρ, C ≤ X ∧ C ⊔ (X ⊓ W) = X ∧
          C ⊓ (X ⊓ W) = Y := by
  classical
  by_contra h
  push Not at h
  exact Representation.BinaryOffender.not_equivariant_section_of_unique_maximal
    ρ W hW hW0 hunique (equivariant_section_of_two_step_splitting ρ W h)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
