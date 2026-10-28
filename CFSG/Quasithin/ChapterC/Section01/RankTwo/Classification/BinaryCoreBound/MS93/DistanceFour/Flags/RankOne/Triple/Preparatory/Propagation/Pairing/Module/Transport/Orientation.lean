module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Transport.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import Theory.GroupTheory.PCoreImage

/-!
# Orienting and transporting the actual seed line

The first parabolic cannot be a point stabilizer in the natural marking:
its core-fixed line would then be fixed by the entire parabolic, contradicting
the ordered residual's nonfixation. The genuine inner-or-graph marking theorem
therefore places the seed in the incident plane of a line stabilizer. A cubic
actor moves its nonzero coordinate to the opposite point-fixed line. Lifting
the actor through the original projection transports the literal subgroup.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(2), printed p.906;
the incident natural-module geometry is that of (1.7), pp.847--848.
-/

@[expose] public section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace SplitLineData
variable {G : Type*} [Group G] [Finite G] {π : G →* SL} {flag : SL} {j : Bool}
  {H N X : Subgroup G} (d : SplitLineData π flag j H N X)
include d

omit [Finite G] in
theorem parabolic_image (i : Bool) : (parabolic π flag i).map π = modelParabolic flag i := by
  exact map_comap_eq_self (by rw [π.range_eq_top_of_surjective d.surjective]; exact le_top)

theorem marked_core_image (i : Bool) :
    ((localCore (parabolic π flag i)).map π).map d.coordinates.marking.toMonoidHom =
      (markedParabolic d.coordinates.marking flag i).pCoreIn 2 := by
  change (((parabolic π flag i).pCoreIn 2).map π).map _ = _
  rw [map_pCoreIn_of_ker_isPGroup π d.kernel_two, d.parabolic_image,
    map_pCoreIn_of_injective 2 _ _ d.coordinates.marking.injective]
  rfl

theorem seed_core_coordinates :
    d.image X ≤ fixedSpace ((markedParabolic d.coordinates.marking flag j).pCoreIn 2) := by
  rw [← d.marked_core_image]
  exact (d.image_fixed_iff X _ d.seed_le_group).mpr d.core_fixed

theorem line_orientation : ∃ k : SL,
    markedParabolic d.coordinates.marking flag j =
      lineParabolicSL.map (MulAut.conj k).toMonoidHom ∧
    markedParabolic d.coordinates.marking flag (!j) =
      pointParabolicSL.map (MulAut.conj k).toMonoidHom ∧
    d.image X ≤ incidentPlane.map (vectorAction k).toMonoidHom := by
  obtain ⟨k, hp | hl⟩ := marked_pair d.coordinates.marking flag j
  · exfalso
    have hc := d.seed_core_coordinates
    rw [hp.1, core_fixed_conj, MarkedProduct.pointParabolic_core, fixed_pointCore] at hc
    have hf : d.image X ≤ fixedSpace (markedParabolic d.coordinates.marking flag j) := by
      rw [hp.1, fixedSpace_conj]
      exact hc.trans (map_mono line_fixed_by_point)
    have hcomm : ⁅X, parabolic π flag j⁆ ≤ N := by
      apply (d.image_fixed_iff X _ d.seed_le_group).mp
      rw [d.parabolic_image]
      exact hf
    exact d.residual_moves ((commutator_mono le_rfl (map_subtype_le _)).trans hcomm)
  · refine ⟨k, hl.1, hl.2, ?_⟩
    have hc := d.seed_core_coordinates
    rw [hl.1, core_fixed_conj, lineParabolicSL_pCoreIn_two_eq_R, fixed_lineCore] at hc
    exact hc

omit d [Finite G] in
private theorem line_transport (A : Subgroup VectorGroup)
    (hA : A ≤ incidentPlane) (hne : A ≠ ⊥) (hcard : Nat.card A ≤ 2) :
    ∃ a : SL, a ∈ lineParabolicSL ∧ A.map (vectorAction a).toMonoidHom = pointLine := by
  obtain ⟨⟨v, hv⟩, hvn⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hvn : v ≠ 1 := fun he => hvn (Subtype.ext he)
  have test : ∀ v : Fin 3 → ZMod 2, v 2 = 0 → v ≠ 0 →
      ∃ t : Fin 3, (lineCycle ^ t.val).val.mulVec v = ![1, 0, 0] := by decide
  obtain ⟨t, ht⟩ := test v.toAdd (hA hv) hvn
  let a := lineCycle ^ t.val
  refine ⟨a, pow_mem lineCycle_mem _, ?_⟩
  have he : vectorAction a v = Multiplicative.ofAdd (![1, 0, 0] : Fin 3 → ZMod 2) := ht
  have hl : pointLine ≤ A.map (vectorAction a).toMonoidHom := by
    intro w hw
    have test' : ∀ w : Fin 3 → ZMod 2, w 1 = 0 ∧ w 2 = 0 →
        w = 0 ∨ w = ![1, 0, 0] := by decide
    rcases test' w.toAdd hw with ho | ho
    · have ho : w = 1 := ho
      rw [ho]
      exact one_mem _
    · have ho : w = Multiplicative.ofAdd (![1, 0, 0] : Fin 3 → ZMod 2) := ho
      rw [ho, ← he]
      exact mem_map_of_mem _ hv
  apply (eq_of_le_of_card_ge hl ?_).symm
  rw [card_map_of_injective (f := (vectorAction a).toMonoidHom) (vectorAction a).injective, line_card]
  exact hcard

theorem transported_line : ∃ (g : G) (k : SL),
    markedParabolic d.coordinates.marking flag j =
      lineParabolicSL.map (MulAut.conj k).toMonoidHom ∧
    markedParabolic d.coordinates.marking flag (!j) =
      pointParabolicSL.map (MulAut.conj k).toMonoidHom ∧
    d.image (X.map (MulAut.conj g).toMonoidHom) =
      pointLine.map (vectorAction k).toMonoidHom := by
  obtain ⟨k, hp, hq, hA⟩ := d.line_orientation
  let A := (d.image X).map (vectorAction k⁻¹).toMonoidHom
  have hAp : A ≤ incidentPlane := by
    have hh := map_mono (f := (vectorAction k⁻¹).toMonoidHom) hA
    rwa [map_action_cancel'] at hh
  have hAn : A ≠ ⊥ := by
    intro hh
    have he := congrArg (fun B : Subgroup VectorGroup => B.map (vectorAction k).toMonoidHom) hh
    rw [Subgroup.map_bot] at he
    exact d.image_seed_ne_bot ((map_action_cancel k (d.image X)).symm.trans he)
  have hAc : Nat.card A ≤ 2 := by
    change Nat.card ((d.image X).map (vectorAction k⁻¹).toMonoidHom) ≤ 2
    rw [card_map_of_injective (f := (vectorAction k⁻¹).toMonoidHom) (vectorAction k⁻¹).injective]
    exact d.image_seed_card_le
  obtain ⟨a, _, ha⟩ := line_transport A hAp hAn hAc
  obtain ⟨g, hg⟩ := d.surjective (d.coordinates.marking.symm (MulAut.conj k a))
  refine ⟨g, k, hp, hq, ?_⟩
  rw [d.image_conjugate X d.seed_le_group, hg, d.coordinates.marking.apply_symm_apply]
  have he := map_action_conj k a A
  rw [map_action_cancel, ha] at he
  exact he

theorem exists_opposite_fixed : ∃ g : G,
    ⁅X.map (MulAut.conj g).toMonoidHom, localResidual (parabolic π flag (!j))⁆ ≤ N := by
  obtain ⟨g, k, _, hq, hx⟩ := d.transported_line
  refine ⟨g, ?_⟩
  have hXg : X.map (MulAut.conj g).toMonoidHom ≤ H := by
    let := d.sectionData.normal_group
    exact (map_mono d.seed_le_group).trans_eq (Normal.map_conj_eq H g)
  have hfix : ⁅X.map (MulAut.conj g).toMonoidHom, parabolic π flag (!j)⁆ ≤ N := by
    apply (d.image_fixed_iff _ _ hXg).mp
    rw [d.parabolic_image, show ((modelParabolic flag (!j)).map d.coordinates.marking.toMonoidHom) =
      markedParabolic d.coordinates.marking flag (!j) from rfl, hq, fixedSpace_conj, hx]
    exact map_mono line_fixed_by_point
  exact (commutator_mono le_rfl (map_subtype_le _)).trans hfix

end SplitLineData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
