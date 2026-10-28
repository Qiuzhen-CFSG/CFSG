module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.ModelAlternatives

/-!
# Remaining intrinsic inputs for the exceptional action

The earlier balance, residual and model-pair assertions of 16.1.7 are kept
separate from the automorphism-centralizer calculations used in 16.3.5.
The latter calculations have to identify the actual conjugation image and
retain the HS possibility until its two centralizer layers are constructed.
None of the definitions in this file asserts an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.7 and 16.3.5, printed pp.1172–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
open Subgroup Theory.GroupTheory ClassificationModels
universe u
variable {G : Type u} [Group G]

/-- The literal solvable-residual clause of the earlier swapped alternative.
The model list and the geometric balance assertion are separate inputs. -/
def SwappedResidualInput (𝒦 : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  Hypothesis1611 𝒦 G → ∀ (t i : G) (L : Subgroup G),
    ComponentTransfer.Setup t i L →
    ComponentTransfer.SwappedComponents (involutionCentralizer i) t L
      (ComponentTransfer.layerClosure (involutionCentralizer i) L) →
    L = ComponentTransfer.centralizerResidual
      (ComponentTransfer.layerClosure (involutionCentralizer i) L) t

/-- The two model pairs in the final exceptional conclusion, on the actual
smaller group and the quotient of the actual enlargement by its two-core. -/
def ExceptionalModels (L I : Subgroup G) : Prop :=
  (Nonempty (L ≃* alternatingGroup (Fin 5)) ∧
    (Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.m12.Carrier) ∨
     Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.j2.Carrier))) ∨
  (Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∧
    Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.ru.Carrier))

/-- The intrinsic calculation preceding the HS elimination. Its conclusions
are obligations, not a replacement for the automorphism tables. -/
structure ActionCalculation (L I : Subgroup G) (hLI : L ≤ I) : Prop where
  centralizer_model : Nonempty
    (centralizer ((inducedAction L I (hLI.trans I.le_normalizer)).range : Set (MulAut I)) ≃*
      (Fin 2 → Multiplicative (ZMod 2)))
  models : ExceptionalModels L I ∨ Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.hs.Carrier)

/-- The particular HS witnesses used in the contradiction. Both layers
are subgroups of the actual covering group, not images in its quotient. -/
def MixedHSLayers (E I : Subgroup G) : Prop :=
  ∃ s t : G, s ∈ E ∧ s ≠ 1 ∧ t ∈ E ∧ t ≠ 1 ∧
    Nonempty (ComponentTransfer.layerIn (I ⊓ involutionCentralizer s) ≃*
      alternatingGroup (Fin 8)) ∧
    Nonempty (ComponentTransfer.layerIn (I ⊓ involutionCentralizer t) ≃*
      alternatingGroup (Fin 6))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
