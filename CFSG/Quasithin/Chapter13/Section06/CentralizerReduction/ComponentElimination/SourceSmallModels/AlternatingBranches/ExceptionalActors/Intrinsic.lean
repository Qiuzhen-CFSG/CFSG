module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.PGroupCore

/-!
# The intrinsic actor contract and the full-subgroup fixed-space calculation

The source plane stabilizer contains three permitted two-perfect actors with
cubic two-core quotient. `PermittedActor` retains these exact hypotheses,
including the actual Sylow subgroup and the linear commutator. It is an input
contract, not a classification theorem.

Two structural witnesses suffice for the centralizer argument: a single
three-cycle, or an involution fixing the marked plane pointwise. In the latter
case the faithful A₇ involution theorem identifies its entire fixed space with
that plane. The full actor then has zero common fixed space if its restriction
to the plane does. This handles a noncyclic actor without asserting that one
of its double three-cycles is fixed-point-free. `Geometry` constructs the
required plane action, and `ExceptionalActors` supplies the source consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 13.6.22,
printed p.932. Exhaustion of the three actors remains a separate prerequisite.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
abbrev A7 := alternatingGroup (Fin 7)
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The intrinsic source hypotheses in the plane normalizer. -/
structure PermittedActor (ρ : Representation (ZMod 2) A7 W)
    (P : Submodule (ZMod 2) W) (S : Sylow 2 A7) (D : Subgroup A7) : Prop where
  sylow_stabilizes : (S : Subgroup A7) ≤ subspaceStabilizer ρ P
  stabilizes : D ≤ subspaceStabilizer ρ P
  normalized : (S : Subgroup A7) ≤ normalizer (D : Set A7)
  twoPerfect : IsPPerfect 2 D
  quotient_card : Nat.card (D ⧸ pCore 2 D) = 3
  commutator_eq : subspaceCommutator ρ P D = P

/-- Two sufficient structural witnesses. The second retains the full actor's
plane action; no assertion that a double three-cycle is fixed-point-free is made. -/
def ActorWitness (ρ : Representation (ZMod 2) A7 W)
    (P : Submodule (ZMod 2) W) (D : Subgroup A7) : Prop :=
  (∃ a ∈ D, Equiv.Perm.IsThreeCycle a.val) ∨
    ∃ t ∈ D, orderOf t = 2 ∧ ∀ w ∈ P, ρ t w = w

/-- An involution fixing the marked plane forces all common fixed vectors
into it. This uses the involution theorem for the original faithful action. -/
theorem fixed_eq_zero_of_plane_involution [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4) (P : Submodule (ZMod 2) W)
    (hP : Module.finrank (ZMod 2) P = 2) (D : Subgroup A7)
    (hplane : ∀ w ∈ P, (∀ d : D, ρ d w = w) → w = 0)
    (t : A7) (ht : t ∈ D) (ho : orderOf t = 2)
    (hfix : ∀ w ∈ P, ρ t w = w) :
    ∀ w : W, (∀ d : D, ρ d w = w) → w = 0 := by
  have hle : P ≤ fixedSpace ρ (zpowers t) := fun w hw =>
    (mem_fixedSpace_zpowers_iff ρ t w).mpr (hfix w hw)
  have hc := AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hρ hdim t ho
  have hd := fixedCodim_add_finrank ρ (zpowers t)
  have he : P = fixedSpace ρ (zpowers t) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hP]; omega)
  intro w hw
  apply hplane w
  · rw [he, mem_fixedSpace_zpowers_iff]
    exact hw ⟨t, ht⟩
  · exact hw

/-- Both structural witnesses give zero common fixed space, including the
noncyclic actor whose cubic elements may be double three-cycles. -/
theorem fixed_eq_zero_of_actorWitness [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4) (P : Submodule (ZMod 2) W)
    (hP : Module.finrank (ZMod 2) P = 2) (D : Subgroup A7)
    (hplane : ∀ w ∈ P, (∀ d : D, ρ d w = w) → w = 0)
    (hwitness : ActorWitness ρ P D) :
    ∀ w : W, (∀ d : D, ρ d w = w) → w = 0 := by
  rcases hwitness with ⟨a, ha, hc⟩ | ⟨t, ht, ho, hf⟩
  · intro w hw
    exact binaryAlternatingSeven_threeCycle_fixedPointFree ρ hρ hdim a hc w (hw ⟨a, ha⟩)
  · exact fixed_eq_zero_of_plane_involution ρ hρ hdim P hP D hplane t ht ho hf
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
