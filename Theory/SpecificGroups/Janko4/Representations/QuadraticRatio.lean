module

public import Theory.SpecificGroups.Janko4.Representations.CentralCoverDegree
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.Representation.BinaryOffender.CubicNormalizerDegree
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section

/-!
# Strict quadratic ratio for faithful binary J₄ actions

A faithful action of a simple copy of J₄ has an irreducible invariant section
on which the perfect group survives. Simplicity makes that section faithful.
The same quadratic actor acts on the section with no larger fixed codimension.
Three-conjugate generation and automorphism two-rank at most eleven would then
give degree at most sixty-six, contradicting the certified lower bound 110.

This removes irreducibility from the J₄ exclusion used in Aschbacher–Smith
K.4, printed p.457, and the original terminal action of §13.6, printed p.935.
The simple-group instance is inherited from the source component; no catalogue
recognition or SQTK assumption is needed for this representation calculation.
-/

public section
namespace Janko4.BinaryDegree
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

variable {X V : Type*} [Group X] [Finite X] [IsSimpleGroup X]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite X] in
private theorem perfect_of_equiv (e : X ≃* Model) : Group.IsPerfect X := by
  refine ⟨(inferInstance : (commutator X).Normal).eq_bot_or_eq_top.resolve_left ?_⟩
  intro hc
  let : IsMulCommutative X := (commutator_eq_bot_iff X).mp hc
  apply a_mul_b_ne_b_mul_a
  simpa only [map_mul, e.apply_symm_apply] using
    congrArg e (mul_comm' (e.symm a) (e.symm b))

/-- Even the cubic ratio is strictly greater than two on every faithful
irreducible binary representation of a simple copy of the actual J₄ model. -/
theorem cubicRatio_gt_two_of_irreducible
    (ρ : Representation (ZMod 2) X V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (e : X ≃* Model) : 2 < cubicRatio ρ := by
  let : Group.IsPerfect X := perfect_of_equiv e
  let : IsSimpleGroup Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let eZ : X ⧸ center X ≃* Model :=
    ((QuotientGroup.quotientMulEquivOfEq center_eq_bot_of_simple_perfect).trans
      QuotientGroup.quotientBot).trans e
  let : IsQuasisimple X := ⟨eZ.isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup X) := IsQuasisimple.of_mulEquiv topEquiv.symm
  let : IsSimpleGroup (⊤ : Subgroup X) := topEquiv.isSimpleGroup
  let eT : (⊤ : Subgroup X) ⧸ center (⊤ : Subgroup X) ≃* Model :=
    ((QuotientGroup.quotientMulEquivOfEq center_eq_bot_of_simple_perfect).trans
      QuotientGroup.quotientBot).trans (topEquiv.trans e)
  have hiT : Representation.IsIrreducible (ρ.comp (⊤ : Subgroup X).subtype) :=
    (irreducible_comp_surjective_iff (⊤ : Subgroup X).subtype
      (topEquiv (G := X)).surjective ρ).mpr hi
  let := hi
  have hl := faithful_irreducible_central_cover_degree ρ hf eZ
  by_contra! hq
  have hu := finrank_le_six_mul_of_cubic_central_quotient ρ (⊤ : Subgroup X)
    hf hiT eT ThreeConjugates.automorphisms TwoRank.automorphism_twoRank_le_eleven hq
  omega

/-- Every faithful finite-dimensional binary representation of a simple copy
of J₄ has quadratic ratio strictly greater than two, including reducible actions. -/
theorem quadraticRatio_gt_two
    (ρ : Representation (ZMod 2) X V) (hf : Function.Injective ρ)
    (e : X ≃* Model) : 2 < quadraticRatio ρ := by
  let : Group.IsPerfect X := perfect_of_equiv e
  let : Group.IsPerfect (⊤ : Subgroup X) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := X)).symm.toMonoidHom)
      topEquiv.symm.surjective
  have hn : ¬ (⊤ : Subgroup X) ≤ ρ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf]
    exact not_le_of_gt bot_lt_top
  obtain ⟨U, N, hi, hn⟩ :=
    QuadraticFourGroup.exists_irreducible_section_surviving_perfect (⊤ : Subgroup X) hn
  have hfN : Function.Injective N.quotientRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact (inferInstance : N.quotientRepresentation.ker.Normal).eq_bot_or_eq_top.resolve_right
      (fun he => hn he.ge)
  by_contra! hq
  obtain ⟨A, hA, ha, hc⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  have haN : IsQuadratic N.quotientRepresentation A :=
    quadratic_of_equivariant_surjection U.toRepresentation N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ U ha)
  have hcN : fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
    have hU := fixedCodim_subrepresentation_le ρ U A
    have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    omega
  have hqN := (quadraticRatio_le_two_iff N.quotientRepresentation).mpr ⟨A, hA, haN, hcN⟩
  exact (not_le_of_gt (cubicRatio_gt_two_of_irreducible N.quotientRepresentation hfN hi e))
    ((cubicRatio_le_quadraticRatio N.quotientRepresentation).trans hqN)

end Janko4.BinaryDegree
