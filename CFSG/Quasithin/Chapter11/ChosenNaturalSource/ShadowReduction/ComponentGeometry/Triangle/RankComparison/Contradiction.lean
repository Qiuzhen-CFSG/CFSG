module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.G2Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.LongRoot
public import Theory.Representation.G2NaturalOffenders
public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Theory.Representation.BinaryOffender.SmallMovedProducts

/-!
# The mutual-action contradiction in the field-four triangle

The selected symplectic actor gives an elementary subgroup of the actual
natural G₂(4) model whose rank and binary moved dimension are both four.
The small-moved theorem places this very subgroup in one conjugate of the
highest-root group, of order four and binary rank two. This contradicts
the rank-four actor supplied by the literal mutual-action comparison.

The normalizer action, original weak-closure conjugate and its image equality
are retained by the preceding comparison. No replacement quotient or
unmarked actor is used.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776, with the natural-offender
calculation from B.4.6(13), printed pp.89--90.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
attribute [local instance] ZMod.algebra

variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- A rank-four actor with four-dimensional movement cannot occur in natural G₂(4). -/
public theorem no_inner_four_actor (hF : Nat.card F = 4)
    (C : Subgroup (Atlas.G2.Model F)) [IsElementaryAbelian 2 C]
    (hCm : Module.finrank (ZMod 2)
      (subspaceCommutator (Atlas.G2.Natural.Normalizer.binary F) ⊤ C) = 4)
    (hCr : rank C = 4) : False := by
  have hr := Atlas.G2.NaturalSmallMovedRoot.rank_le_two hF C hCm.le
  omega

/-- The literal G₂ comparison output is impossible in the field-four row. -/
public theorem ofFlag_no_inner_four_actor
    {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F]
    [Finite G] [Finite F] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    (m : letI : Algebra (ZMod 2) S.field.Carrier := S.field.binaryAlgebra
      ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.g2 m))
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (hF : Nat.card F = 4) (hG2 : Nat.card S.field.Carrier = 4)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hchosen : normalizer (V : Set G) ≤ normalizer (L : Set G)) (I U : Subgroup G)
    (hout : ¬ I ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G))
    (hC : (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2)
    (hU : IsPGroup 2 U) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ (ofFlag S f X z H₀).R₂)
    (hs : (4 : ℕ∞) ≤ @globalS G _ V D.elementary)
    (hr : (4 : ℕ∞) < globalR V)
    (α : (ofFlag S f X z H₀).R₂ →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hact : ∀ (a : (ofFlag S f X z H₀).R₂) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hTU (LocalGeometry.localRadical_le_sylow _ a.property))
          u.val).mp u.property⟩).toAdd = α a • (e u).toAdd)
    (himage : α.range ≤ Plane.radical.map planeLocal.subtype) : False := by
  obtain ⟨_, _, _, _, C, _, _, _, hCe, hCm, hCr⟩ :=
    ofFlag_exists_inner_four_actor D S m f X z H₀ hF hG2 hfix hchosen I U hout hN hC hU hTU
      hW hs hr α e hact himage
  let : IsElementaryAbelian 2 C := hCe
  exact no_inner_four_actor hG2 C hCm hCr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
