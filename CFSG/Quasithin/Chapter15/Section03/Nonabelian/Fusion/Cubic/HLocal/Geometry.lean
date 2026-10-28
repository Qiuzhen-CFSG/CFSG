module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Choices
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The precise recognized geometry used by the H-local calculations

The dihedral cube is the central product: the quotient of three dihedral
eights identifying their central involutions. The recognition data retain
an actual equivalence with that group, the source center, the exact actor
Aut(PSL₃(2)), and coordinates on the literal U/Z. The inner-action equation
uses the natural and contragredient representations for the same SL₃(2)
element. The square equation retains the hyperbolic quadratic form.

These are conditional inputs from 15.3.55, 15.3.58 and 15.3.59(1), not
assertions that those earlier source theorems have been proved.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal

/-- The three dihedral factors before identifying their centers. -/
abbrev DihedralTriple := DihedralGroup 4 × DihedralGroup 4 × DihedralGroup 4

/-- The two relations identifying all three central involutions. -/
def cubeRelations : Subgroup DihedralTriple := normalClosure
  {((DihedralGroup.r 2, DihedralGroup.r 2, 1) : DihedralTriple),
   ((DihedralGroup.r 2, 1, DihedralGroup.r 2) : DihedralTriple)}

instance cubeRelations_normal : cubeRelations.Normal := by
  unfold cubeRelations
  infer_instance

/-- The identifying relations lie in the center of the triple product. -/
lemma cubeRelations_le_center : cubeRelations ≤ center DihedralTriple := by
  apply normalClosure_le_normal
  have hc : ∀ x : DihedralGroup 4, x * DihedralGroup.r 2 = DihedralGroup.r 2 * x := by decide
  rintro x (rfl | rfl)
  · apply mem_center_iff.mpr
    intro a
    exact Prod.ext (hc a.1) (Prod.ext (hc a.2.1) (by simp))
  · apply mem_center_iff.mpr
    intro a
    exact Prod.ext (hc a.1) (Prod.ext (by simp) (hc a.2.2))

/-- The source's D₈³ is a central product, not the direct product. -/
abbrev DihedralCube := DihedralTriple ⧸ cubeRelations

/-- Coordinates on the six-dimensional natural-plus-dual module. -/
abbrev Coordinates := BinaryLinearThree.Vector ×
  Module.Dual (ZMod 2) BinaryLinearThree.Vector

variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- Exact earlier recognition and core data for the local calculation.
No centralizer order or centralizing cubic is a field of this structure. -/
structure Recognition where
  subgroup_le : ZS ≤ centralizerH Z
  center_le : Z ≤ ZS
  center_card : Nat.card Z = 2
  core_eq : closureU Z ZS = coreQ Z
  extraspecial : IsExtraspecial 2 (closureU Z ZS)
  center_eq : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS)
  plusType : closureU Z ZS ≃* DihedralCube
  actor : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.PSL
  coordinates : VectorQuotient Z ZS ≃* Multiplicative Coordinates
  inner_action : ∀ (h : centralizerH Z) (g : Matrix.PSL3Two.SL),
    actor (QuotientGroup.mk' (pCore 2 (centralizerH Z)) h) =
      MulAut.conj (Matrix.PSL3Two.equiv g) →
    ∀ u : VectorQuotient Z ZS,
      (coordinates (quotientAction Z ZS h u)).toAdd =
        (BinaryLinearThree.W g (coordinates u).toAdd.1,
         BinaryLinearThree.W.dual g (coordinates u).toAdd.2)
  quadratic : ∀ u : closureU Z ZS, u ^ 2 = 1 ↔
    (coordinates (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u)).toAdd.2
      (coordinates (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u)).toAdd.1 = 0

/-- The actual source action exchanges the marked natural and dual summands.
Both clauses refer to conjugation on the literal vector quotient. -/
def Swaps (d : Recognition Z ZS) (t : centralizerH Z) : Prop :=
  (∀ v : BinaryLinearThree.Vector,
    (d.coordinates (quotientAction Z ZS t
      (d.coordinates.symm (Multiplicative.ofAdd (v, 0))))).toAdd.1 = 0) ∧
  (∀ f : Module.Dual (ZMod 2) BinaryLinearThree.Vector,
    (d.coordinates (quotientAction Z ZS t
      (d.coordinates.symm (Multiplicative.ofAdd (0, f))))).toAdd.2 = 0)

/-- The recognized actor has its actual model order. -/
theorem actor_card (d : Recognition Z ZS) : Nat.card (ActorQuotient Z) = 336 :=
  (Nat.card_congr d.actor.toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut

/-- Every source Sylow three-group has order three. -/
theorem sylow_three_card [Finite G] (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) : Nat.card P = 3 :=
  sylow_three_card_of_actor_card Z (actor_card Z ZS d) P

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
