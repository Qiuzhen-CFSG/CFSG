module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.Plane

/-!
# Contracts for the source point/line marking and local action

The marking preserves the original qL and records the Sylow intersection,
the point parabolic as a line stabilizer, and an actual natural-to-dual
representation equivalence. Functoriality of the two-residual proves the
required identity for the original L₁ actor with the inverse twist.

The independent local-action contract asks for conjugating elements between
nonzero vectors of the literal U/V plane. Both witnesses must be constructed
from the source data before the conditional seed assembly proves 14.7.72.
Neither a cyclic vector nor an orbit dimension is a field of these contracts.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
using H.6.5, printed p.388 (PDF p.399), manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Chapter12.Section08 CriticalFusion.Source BinaryLinearThree.ParabolicCyclic
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- A change of actor coordinates compatible with the original qL, the
original Sylow intersection, the original point parabolic, and natural duality.
Constructing this record remains a separate source obligation. -/
structure Marking where
  twist : MulAut BinaryLinearThree.Group
  sylow : ((T : Subgroup G).subgroupOf L).map
    (twist.symm.toMonoidHom.comp d.qL) = Matrix.PSL3Two.borelSL
  parabolic : (F.H.subgroupOf L).map
    (twist.symm.toMonoidHom.comp d.qL) = Matrix.PSL3Two.lineParabolicSL
  naturalDual : Representation.Equiv (BinaryLinearThree.W.comp twist.toMonoidHom) BinaryLinearThree.W.dual

/-- The first flag actor is the embedded two-residual of the actual
point parabolic in L. This uses only the literal definition of L₁. -/
theorem relative_first_actor : (F.Li L 1).subgroupOf L =
    (pResidual 2 (F.H.subgroupOf L)).map (F.H.subgroupOf L).subtype := by
  apply map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
    map_embedded_pResidual, subgroupOf_map_subtype]
  simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
  change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype = _
  rw [inf_comm]

/-- The literal actor identity needed by the chief-factor exclusion, with
the inverse twist and the original quotient homomorphism displayed. -/
theorem Marking.residual (b : Marking d) :
    ((F.Li L 1).subgroupOf L).map (b.twist.symm.toMonoidHom.comp d.qL) =
      (pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
        Matrix.PSL3Two.lineParabolicSL.subtype := by
  rw [relative_first_actor, map_embedded_pResidual, b.parabolic]

variable [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- The outstanding local-action contract, on the original quotient plane
and the original first residual. It asks for actual conjugating elements.
It contains no cyclic vector, orbit dimension, or recognition alternative. -/
def LocalTransitive (a : QuotientAction d) : Prop :=
  ∀ v w : Additive (S F L ⧸ V.subgroupOf (S F L)),
    v ∈ plane (F := F) (L := L) (V := V) →
    w ∈ plane (F := F) (L := L) (V := V) → v ≠ 0 → w ≠ 0 →
    ∃ l : L, (l : G) ∈ F.Li L 1 ∧ a.representation (d.qL l) v = w


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
