module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection.Transport

/-!
# Compatible line-residual fixation of a moving neighbor

The alpha-side edge displacement has order four and equals [U_alpha,Q_t].
Its natural coordinate image therefore has a dual fixed space lying on a
line fixed by a compatible line parabolic. The delta-side edge equality
makes Q_t fix Z_delta modulo the original radical Z_alpha[V_alpha,Q_alpha].
The full SingleNaturalSection decomposition transfers this fixation to
the line parabolic and hence to its ordered residual O²(O^{2′}(P)).

This proves the representation input for residual normalization in
MS93 (4.3.2)(3), printed p.884, before identifying H with U.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
open FixedSection

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R}

private theorem edge_matrixDisplacement_card (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (o : MovingOrientationAt p.a)
    (t : Vertex R) (hat : Adjacent R p.a t) :
    Nat.card (matrixDisplacement
      (((Q R t).subgroupOf (stabilizer R p.a)).map (naturalProjection o))) = 4 := by
  let S := stabilizer R p.a
  let T := (Q R t).subgroupOf S
  let U₀ := (U R p.a).subgroupOf S
  have hU : U R p.a ≤ S := (U_le_Z p.a).trans (Z_le_stabilizer R p.a)
  have hT : Q R t ≤ S := fun _ hx => hx.2 p.a (adjacent_symm R hat)
  have he : (⁅U₀, T⁆).map S.subtype = edgeDisplacement p.a t := by
    rw [map_commutator, map_subgroupOf_eq_of_le hU, map_subgroupOf_eq_of_le hT]
    exact (EdgeTransfer.edge_commutator_eq_natural hb modules p.a t p.color_a hat).symm
  change Nat.card (matrixDisplacement (T.map
    (o.naturalU.marking.toMonoidHom.comp o.projection))) = 4
  rw [natural_commutator_card o.naturalU T]
  calc
    Nat.card (⁅U₀, T⁆ : Subgroup S) = Nat.card ((⁅U₀, T⁆).map S.subtype) :=
      (card_map_of_injective S.subtype_injective).symm
    _ = 4 := by rw [he]; exact edge_card p (by omega) initial p.a t p.color_a hat

/-- The moving neighbor is fixed modulo Z[V,Q] by a line residual in the
coordinates of the actual natural U-module. -/
theorem exists_lineResidual_fixed_neighbor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (o : MovingOrientationAt p.a) (t d : Vertex R)
    (hat : Adjacent R p.a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry p.a) :
    ∃ flag : SL, ⁅(Z R d).subgroupOf (stabilizer R p.a), lineResidual o flag⁆ ≤
      radicalPreimage ((Q R p.a).subgroupOf (stabilizer R p.a))
        ((V R p.a).subgroupOf (stabilizer R p.a)) ((Z R p.a).subgroupOf (stabilizer R p.a)) := by
  obtain ⟨flag, hf⟩ := exists_line_fixed_of_displacement_card _
    (edge_matrixDisplacement_card source hb modules initial p o t hat)
  refine ⟨flag, split_section_fixed_transfer o.natural_section o.naturalU o.dual
    ((Z R d).subgroupOf (stabilizer R p.a))
    ((Q R t).subgroupOf (stabilizer R p.a)) (lineResidual o flag)
    (fun x hx => moving_Z_le_V hd hx) ?_ ?_⟩
  · exact moving_neighbor_fixed_mod_radical_by_edge p hb initial bad p.a t d p.color_a
      hat hdt hd
  · intro v hv k hk
    have hv' : dualFixed
        (((Q R t).subgroupOf (stabilizer R p.a)).map (naturalProjection o)) v := by
      rintro g ⟨t, ht, rfl⟩
      exact hv t ht
    have hle : lineResidual o flag ≤ lineParabolic o flag := map_subtype_le _
    exact hf v hv' (naturalProjection o k) (hle hk)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
