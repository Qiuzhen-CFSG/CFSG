module

public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Basic
public import Theory.ElementaryAbelian.Basic

/-!
# The exact four-group transfer contracts

These specifications separate the new arguments in 16.3.4–8 from the earlier
component and automorphism tables. They do not assert those arguments or tables.
The exclusions in 16.3.4 concern the full simple group, whereas the alternatives
in 16.3.5 concern the quotient by the nontrivial two-core. An order-four subgroup
in the input is permitted to be cyclic; elementary abelianness is an output.

The enlargement is the actual closure under the layer of the indicated
centralizer. Its action is the restriction of ambient conjugation, and its
image is the full centralizer of the inner action of the smaller component.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.4–16.3.6, printed pp.1178–1179 / PDF pp.1195–1196.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G]

/-- The full simple groups excluded in 16.3.4. In the unitary case `n ≥ 2`
is the nonabelian simple range. No quotient of the supplied group occurs. -/
def IsExcludedSimple (K : Type*) [Group K] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU K 3 (2 ^ n)) ∨
  Nonempty (K ≃* SporadicName.m12.Carrier) ∨
  Nonempty (K ≃* SporadicName.j2.Carrier) ∨
  Nonempty (K ≃* SporadicName.hs.Carrier) ∨
  Nonempty (K ≃* SporadicName.ru.Carrier)

/-- All local hypotheses of 16.3.4, with relative normality from 16.2.4.
The global `Hypothesis1611` is supplied separately by a source caller. -/
structure ExclusionSetup (T : Sylow 2 G) (z : G) (L K : Subgroup G)
    (t i : G) : Prop where
  localSetup : CentralComponentSetup T z L
  normal : (L.subgroupOf (involutionCentralizer z)).Normal
  involution_t : orderOf t = 2
  t_mem : t ∈ commutingSylow T L
  componentK : IsCentralizerComponent t K
  involution_i : orderOf i = 2
  componentL : Theory.GroupTheory.IsComponentIn L (K ⊓ involutionCentralizer i)
  centralizes : i ∈ centralizer ((L ⊔ zpowers t : Subgroup G) : Set G)
  commutator_eq : ⁅K, zpowers i⁆ = K

/-- The concrete Sylow-center and order calculation consumed by 16.3.4.
This is an obligation for the five actual models, not their exclusion. -/
def ExcludedSylowGeometry (T : Sylow 2 G) (L K : Subgroup G) : Prop :=
  ∃ V R : Subgroup G,
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    Disjoint (commutingSylow T L) V ∧
    (∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = R) ∧
    (center R).map R.subtype = V ∧
    Nat.card T < Nat.card R * Nat.card (commutingSylow T L)

/-- Component membership for every nonidentity element, including elements
of order four. There is no assertion that E is elementary abelian. -/
def CentralizesAsComponent (E K : Subgroup G) : Prop :=
  ∀ e : G, e ∈ E → e ≠ 1 → IsCentralizerComponent e K

/-- Ambient conjugation restricted to a subgroup normalizing I. -/
def inducedAction (E I : Subgroup G) (hn : E ≤ normalizer (I : Set G)) : E →* MulAut I :=
  I.normalizerMonoidHom.comp (Subgroup.inclusion hn)

/-- The exceptional alternative (2) of 16.3.5, with the exact enlargement,
faithfulness, full automorphism-centralizer image, core, and model clauses. -/
structure ExceptionalEnlargement (E K : Subgroup G) (i : G) : Prop where
  proper : K < ComponentTransfer.layerClosure (involutionCentralizer i) K
  component : IsCentralizerComponent i
    (ComponentTransfer.layerClosure (involutionCentralizer i) K)
  normalizes : E ≤ normalizer
    (ComponentTransfer.layerClosure (involutionCentralizer i) K : Set G)
  faithful : Function.Injective (inducedAction E
    (ComponentTransfer.layerClosure (involutionCentralizer i) K) normalizes)
  elementary : IsElementaryAbelian 2 E
  four_model : Nonempty (E ≃* (Fin 2 → Multiplicative (ZMod 2)))
  image_eq : (inducedAction E
      (ComponentTransfer.layerClosure (involutionCentralizer i) K) normalizes).range =
    centralizer ((inducedAction K
      (ComponentTransfer.layerClosure (involutionCentralizer i) K)
      ((ComponentTransfer.le_layerClosure _ _).trans
        (ComponentTransfer.layerClosure (involutionCentralizer i) K).le_normalizer)).range : Set _)
  core_ne : pCore 2 (ComponentTransfer.layerClosure (involutionCentralizer i) K) ≠ ⊥
  models :
    (Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
      (Nonempty ((ComponentTransfer.layerClosure (involutionCentralizer i) K ⧸
        pCore 2 (ComponentTransfer.layerClosure (involutionCentralizer i) K)) ≃*
        SporadicName.m12.Carrier) ∨
       Nonempty ((ComponentTransfer.layerClosure (involutionCentralizer i) K ⧸
        pCore 2 (ComponentTransfer.layerClosure (involutionCentralizer i) K)) ≃*
        SporadicName.j2.Carrier))) ∨
    (Nonempty (K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∧
      Nonempty ((ComponentTransfer.layerClosure (involutionCentralizer i) K ⧸
        pCore 2 (ComponentTransfer.layerClosure (involutionCentralizer i) K)) ≃*
        SporadicName.ru.Carrier))

/-- The assertion to be proved in 16.3.6. The source theorem's owner must
establish this; declaring it does not supply the transfer argument. -/
def FourGroupComponentTransfer (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ commutingSylow T L → Nat.card E = 4 →
    CentralizesAsComponent E L → ∀ i : G, orderOf i = 2 →
      i ∈ centralizer ((E ⊔ L : Subgroup G) : Set G) → IsCentralizerComponent i L

end CFSG.Quasithin.Chapter16.FourGroupTransfer
