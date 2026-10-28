module
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction

/-!
# Residues of literal left-coset geometries

Objects of G/P incident with the base point M in G/M have a representative
in M. Their representatives differ by P ∩ M, so they are precisely the
left cosets of P ∩ M inside M. The bijection below retains the actual ambient
coset and its incidence witness; no transitivity or geometry axiom is assumed.

This is the local coset identification used in Aschbacher, *Sporadic Groups*
(1994), 4.11 and 41.1, and in the Mathieu source point residue.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] (M P : Subgroup G)

/-- Objects incident with the base point of the actual left coset geometry. -/
abbrev Residue := {l : Vertex P // Incident M P (vertex M 1) l}

private def toResidue : (M ⧸ P.subgroupOf M) → Residue M P :=
  Quotient.lift (fun a : M => ⟨vertex P a, a, (vertex_eq_base M a).mpr a.property, rfl⟩)
    (by
      intro a b hab
      apply Subtype.ext
      apply QuotientGroup.eq.mpr
      have h := QuotientGroup.leftRel_apply.mp hab
      exact h)

private theorem toResidue_bijective : Function.Bijective (toResidue M P) := by
  constructor
  · intro q r
    induction q using QuotientGroup.induction_on with
    | H a =>
      induction r using QuotientGroup.induction_on with
      | H b =>
        intro he
        apply QuotientGroup.eq.mpr
        have hh : vertex P (a : G) = vertex P (b : G) := congrArg Subtype.val he
        exact (vertex_eq_iff P (a : G) (b : G)).mp hh
  · rintro ⟨l, a, ha, hl⟩
    have hM := (vertex_eq_base M a).mp ha
    exact ⟨QuotientGroup.mk (⟨a, hM⟩ : M), Subtype.ext hl⟩

/-- Residue objects are literal cosets of the flag stabilizer in the point stabilizer. -/
def residueEquiv : (M ⧸ P.subgroupOf M) ≃ Residue M P :=
  Equiv.ofBijective (toResidue M P) (toResidue_bijective M P)

@[simp] theorem residueEquiv_mk (a : M) :
    (residueEquiv M P (QuotientGroup.mk a)).val = vertex P a := by rfl

end Theory.GroupTheory.GraphUniquenessSystem.Cosets
