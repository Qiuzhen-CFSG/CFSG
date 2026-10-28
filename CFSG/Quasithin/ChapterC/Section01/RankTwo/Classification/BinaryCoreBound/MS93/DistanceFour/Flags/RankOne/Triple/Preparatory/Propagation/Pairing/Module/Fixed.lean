module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Groups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport

/-!
# A nonzero opposite-parabolic fixed subgroup in U_alpha

The common central decomposition identifies the edge commutator with the
selected first core's displacement on the literal natural layer. Its order
is four by the early edge calculation. Under the original natural marking,
the incident pair is a common conjugate of the standard point-line pair,
possibly exchanged by the graph automorphism. A point radical displaces the
natural three-space only into its order-two point line, so the first member
must be the line parabolic. The opposite point parabolic fixes a nonzero
line, which faithful coordinates transfer back to U_alpha.

The actor in the conclusion is the untilded local residual. Its quotient
image is the full opposite parabolic; no tilded actor or orientation
hypothesis replaces it. The proof needs neither a single natural section
nor any later radius or flag-control conclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8)(2), printed p.906, applying the fixed-point hypothesis of
(1.7)(i), pp.847--848.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem point_displacement (a : SL) (ha : a ∈ pointV) (v : VectorGroup) :
    vectorAction a v * v⁻¹ ∈ pointLine := by
  change pointCorePred a at ha
  rcases ha with ⟨h00, h10, h20, h11, h12, h21, h22⟩
  change (a.val.mulVec v.toAdd + -v.toAdd) 1 = 0 ∧
    (a.val.mulVec v.toAdd + -v.toAdd) 2 = 0
  constructor <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h11, h12, h21, h22, CharTwo.add_self_eq_zero]

private theorem conjugate_point_displacement (k a : SL)
    (ha : a ∈ (pointParabolicSL.map (MulAut.conj k).toMonoidHom).pCoreIn 2)
    (v : VectorGroup) :
    vectorAction a v * v⁻¹ ∈ pointLine.map (vectorAction k).toMonoidHom := by
  rw [← Subgroup.map_pCoreIn_of_injective 2 _ _ (MulAut.conj k).injective,
    Matrix.PSL3Two.MarkedProduct.pointParabolic_core] at ha
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := (vectorAction k).surjective v
  change vectorAction (MulAut.conj k a) (vectorAction k v) * (vectorAction k v)⁻¹ ∈ _
  rw [action_conj, ← map_inv, ← map_mul]
  exact mem_map_of_mem _ (point_displacement a ha v)

private theorem coordinate_commutator_le {G : Type*} [Group G] [Finite G]
    {e : Extension (M := G)} {Z : Subgroup G} [Z.Normal]
    (n : NaturalFactor e.projection (component e.projection e.flag) Z ⊥)
    (hL : (component e.projection e.flag).map e.projection = ⊤)
    (A : Subgroup G) (B : Subgroup VectorGroup)
    (h : ∀ a ∈ A, ∀ v : VectorGroup,
      vectorAction (n.marking (e.projection a)) v * v⁻¹ ∈ B) :
    coordinateImage n ⁅A, Z⁆ ≤ B := by
  have hc : ⁅A, Z⁆ ≤ (B.comap n.coordinates).map Z.subtype := by
    apply commutator_le.mpr
    intro a ha z hz
    let z' : Z := ⟨z, hz⟩
    refine ⟨MulAut.conjNormal a z' * z'⁻¹, ?_, rfl⟩
    change n.coordinates (MulAut.conjNormal a z' * z'⁻¹) ∈ B
    rw [map_mul, map_inv, coordinates_conj n hL]
    exact h a ha _
  have hi := map_mono (comap_mono hc (f := Z.subtype)) (f := n.coordinates)
  rw [comap_map_eq_self_of_injective Z.subtype_injective] at hi
  have he : (B.comap n.coordinates).map n.coordinates = B :=
    map_comap_eq_self (by rw [n.coordinates.range_eq_top_of_surjective n.surjective]; exact le_top)
  exact hi.trans_eq he

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem selectedCore_natural_card (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    Nat.card (⁅selectedCore (pairingExtension source) i, naturalLayer (R := R)⁆ : Subgroup M) = 4 := by
  rw [← card_map_of_injective (f := embedM R) (embedM_injective R),
    map_commutator, pairing_selectedCore, map_naturalLayer, hkernel, commutator_comm,
    ← Early.edge_commutator_eq_natural common (alpha R) (beta R) rfl (base_adjacent R)]
  exact early.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)

/-- The opposite untilded actor has a nonzero fixed subgroup in the actual
natural layer, for the original common flag and arbitrary natural marking. -/
theorem opposite_fixed_nonzero (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    naturalLayer (R := R) ⊓
      centralizer (localResidual (localParabolic (pairingExtension source) (!i)) : Set M) ≠ ⊥ := by
  let e := pairingExtension source
  let n : NaturalFactor e.projection (component e.projection e.flag)
      (naturalLayer (R := R)) ⊥ := naturalCoordinates common
  have hL : (component e.projection e.flag).map e.projection = ⊤ :=
    component_map e.projection e.base.surjective e.flag
  have hcore : ((selectedCore e i).map e.projection).map n.marking.toMonoidHom =
      (markedParabolic n.marking e.flag i).pCoreIn 2 := by
    rw [selectedCore_map]
    exact Subgroup.map_pCoreIn_of_injective 2 _ _ n.marking.injective
  obtain ⟨k, hp | hp⟩ := marked_pair n.marking e.flag i
  · have hd : coordinateImage n ⁅selectedCore e i, naturalLayer (R := R)⁆ ≤
        pointLine.map (vectorAction k).toMonoidHom := by
      apply coordinate_commutator_le n hL
      intro a ha v
      apply conjugate_point_displacement k _ _ v
      rw [← hp.1, ← hcore]
      exact mem_map_of_mem _ (mem_map_of_mem _ ha)
    have hcard := card_le_of_le hd
    rw [card_map_of_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective, line_card,
      card_coordinateImage n (commutator_le_right _ _),
      selectedCore_natural_card common early i hkernel] at hcard
    omega
  · have hf : fixedSpace (markedParabolic n.marking e.flag (!i)) ≠ ⊥ := by
      rw [hp.2, fixedSpace_conj]
      intro hbot
      have hle : pointLine.map (vectorAction k).toMonoidHom ≤ (⊥ : Subgroup VectorGroup) := by
        rw [← hbot]
        exact map_mono line_fixed_by_point
      have hc := card_eq_one.mpr (bot_unique hle)
      rw [card_map_of_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective, line_card] at hc
      omega
    intro hbot
    apply hf
    have he := coordinateImage_centralizer n hL
      (localResidual (localParabolic e (!i)))
    rw [localResidual_map] at he
    change coordinateImage n (naturalLayer (R := R) ⊓
      centralizer (localResidual (localParabolic e (!i)) : Set M)) =
      fixedSpace (markedParabolic n.marking e.flag (!i)) at he
    rw [hbot, coordinateImage_bot] at he
    exact he.symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
