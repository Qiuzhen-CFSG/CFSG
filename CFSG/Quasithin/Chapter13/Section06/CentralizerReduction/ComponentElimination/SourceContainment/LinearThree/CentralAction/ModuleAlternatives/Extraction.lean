module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.SingleNatural

/-!
# Extracting one compatible doubled marking

A doubled action on the classifier's moved space transports to the literal
U_K through its proved group equivalence. Evaluation at the two coordinates
changes the repeated-module convention Fin 2 → W to W × W. The resulting
intertwiner uses the existing componentPlus map on the original K.

The final conditional extraction eliminates the natural central quotient
using 13.6.11. The universal-classifier application producing its module
alternative is not supplied here and remains necessary for source assembly.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.20,
printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentSelection ChapterB.QuasisimpleSource
section Doubled
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- Transport the classifier intertwiner to one marking of the actual U_K. -/
noncomputable def doubledCoordinates_of_actionEquiv
    (hK : K ≤ Gv v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : ActionEquiv (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)
      (repeated BinaryLinearThree.W 2)) : DoubledCoordinates K L T z v hK hL hz := by
  let c := movedEquivUK K L T z v hL hz s
  let f := e.linearEquiv.trans (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector)
  refine ⟨e.groupEquiv, c.symm.trans f.toAddEquiv.toMultiplicative, ?_⟩
  intro k u
  have hcu : c.symm (conjugationAction (UK K L T z v) K (K_normalizes_UK K L T z v hL hz) k u) =
      Multiplicative.ofAdd (s.space.toRepresentation
        (componentPlus K L T z v hK hL hz k) (c.symm u).toAdd) := by
    apply c.injective
    rw [c.apply_symm_apply]
    apply Subtype.ext
    change (k : G) * (u : G) * (k : G)⁻¹ =
      ((wkRepresentation K L T z v hL hz
        (componentPlus K L T z v hK hL hz k) (c.symm u).toAdd.val).toMul : G)
    rw [componentPlus_apply, wkRepresentation_apply]
    rfl
  change Multiplicative.ofAdd (f (c.symm (conjugationAction (UK K L T z v) K (K_normalizes_UK K L T z v hL hz) k u)).toAdd) = _
  rw [hcu]
  apply Multiplicative.ofAdd.injective
  exact congrArg (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector)
    (e.intertwines (componentPlus K L T z v hK hL hz k) (c.symm u).toAdd)


end Doubled

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- Extraction in the actual marked central-action branch. The classifier
application is still a separate premise, to be discharged by source assembly. -/
theorem doubled_of_moduleCase (s₀ : A5Module.Marking L V) (K T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s₀) (A5Module.markedV s₀))]
    [IsElementaryAbelian 2 (WK K L T (A5Module.markedZ s₀) (A5Module.markedV s₀))]
    (S : Sylow 2 (Gv (A5Module.markedV s₀)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s₀))).map
      (Gv (A5Module.markedV s₀)).subtype = Tv T (A5Module.markedV s₀))
    (hL : Tv T (A5Module.markedV s₀) ≤ normalizer (Lv L (A5Module.markedV s₀) : Set G))
    (hz : Tv T (A5Module.markedV s₀) ≤ centralizer ({A5Module.markedZ s₀} : Set G))
    (hK : K ∈ Yz L T (A5Module.markedZ s₀) (A5Module.markedV s₀))
    (hn : Tv T (A5Module.markedV s₀) ≤ normalizer (K : Set G))
    (hc : ⁅plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz K,
      plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz (Lv L (A5Module.markedV s₀))⁆ = ⊥)
    (hcase : LinearThreeModuleCase (wkRepresentation K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz)
      (plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz K)) :
    Nonempty (DoubledCoordinates K L T (A5Module.markedZ s₀) (A5Module.markedV s₀)
      hK.1.1 hL hz) := by
  cases hcase with
  | natural s hfull e =>
      exact (not_single_natural_of_marking K L T s₀ S hS hL hz hK hn s hfull e hc).elim
  | doubled s e =>
      exact ⟨doubledCoordinates_of_actionEquiv K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz hK.1.1 s e⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
