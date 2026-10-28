module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Reduction

/-!
# Contracts for the local plane calculations

The source argument needs the rank of an elementary subgroup's actual induced
automizer on V₂, and the commutator of a noncentral such subgroup when bounded
by a conjugate field line. These are local model outputs, not source assumptions
or additional fields of Geometry. Their consumers are the normalization and
alignment proofs in LineAlignment.lean. Movement.lean proves the commutator
contract from the original fixed-space and normalizer conditions; the rank
contract remains a separate obligation.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D}

/-- A finite elementary actor on the original plane has image rank at most n.
This is a model obligation, not a field supplied by the source geometry. -/
def PlaneActionRankBound : Prop :=
  ∀ A : Subgroup G, A ≤ (T : Subgroup G) → IsElementaryAbelian 2 A →
    rank (inducedAutomizer E.V₂ A) ≤ E.input.field.degree

/-- Single-line displacement on the original plane fills its invariant point.
Proved in Movement.lean; this contract involves no conjugate Vᵍ or alignment
conclusion. -/
def PlaneMovement : Prop :=
  ∀ A : Subgroup G, A ≤ (T : Subgroup G) → IsElementaryAbelian 2 A →
    ¬ E.V₂ ≤ centralizer (A : Set G) →
    (∃ l ∈ L, ⁅E.V₂, A⁆ ≤ E.V₁.map (MulAut.conj l).toMonoidHom) →
    ⁅E.V₂, A⁆ = E.V₁

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
