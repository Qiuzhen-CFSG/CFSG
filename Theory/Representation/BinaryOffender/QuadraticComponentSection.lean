module
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# A component-irreducible section for a quadratic supplement

A nontrivial perfect component survives on a literal invariant subquotient.
Quadratic action and fixed-codimension bounds pass through both layers.
The homogeneous-orbit calculation then makes this whole-actor irreducible
section irreducible on the centerless component itself. The supplement and
its faithful conjugation action are retained unchanged.

This is the selected section step of Aschbacher--Smith F.9.18(3--4),
printed pp.325--326, used in the abelian branch of14.2.13, p.984.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- A surviving centerless component has an actual irreducible section retaining
its common faithful quadratic supplement and the supplement's original bound. -/
theorem exists_component_irreducible_quadratic_section
    (ρ : Representation (ZMod 2) G V) (K A : Subgroup G)
    [K.Normal] [IsQuasisimple K] (hZ : center K = ⊥) (hgen : K ⊔ A = ⊤)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set G) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      IsIrreducible (N.quotientRepresentation.comp K.subtype) ∧
      ¬ K ≤ N.quotientRepresentation.ker ∧
      IsQuadratic N.quotientRepresentation A ∧
      fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hn
  have hqU := quadratic_subrepresentation ρ U hq
  have hqN : IsQuadratic N.quotientRepresentation A :=
    quadratic_of_equivariant_surjection U.toRepresentation N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hqU
  have hcN : fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
    have hU := fixedCodim_subrepresentation_le ρ U A
    have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    omega
  have hnf : ¬ (⊤ : Submodule (ZMod 2) (U ⧸ N.toSubmodule)) ≤
      fixedSpace N.quotientRepresentation K := by
    intro hf
    apply hn
    intro k hk
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    exact hf (by trivial) ⟨k,hk⟩
  refine ⟨U,N,?_,hn,hqN,hcN⟩
  exact component_irreducible_of_quadratic_supplement N.quotientRepresentation
    K A hZ hgen hA hqN hcN hAC hi hnf
end Representation.BinaryOffender
