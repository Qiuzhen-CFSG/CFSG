module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Descent
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Moving the midpoint actor to the selected parabolic

The midpoint shares an edge with alpha. Local neighbor transitivity moves
that edge to beta, and the radius subgroup of the midpoint lies in the
edge kernel. Hence its quotient actor is conjugate into the selected
parabolic two-core. Both have order four, so the containment is equality.
Conjugacy preserves fixed codimension for the original representation.

The geometric MidpointFacts remain an explicit input. In particular the
index-four statement here is not inferred from an arbitrary FF offender.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9)--(4.6.11), pp.908--909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry)

include common in
/-- The genuine midpoint actor is conjugate to the two-core of the selected marked parabolic. -/
theorem midpointActor_conjugate_flagCore (s : CriticalSegment geometry)
    (hcard : Nat.card (midpointActor (source := source) s) = 4)
    (i : Bool) (hkernel : Flags.RankOne.flagKernel source i = Q R (beta R)) :
    ∃ g : SL, (midpointActor (source := source) s).map (MulAut.conj g).toMonoidHom =
      (pCore 2 (modelParabolic source.flag i)).map (modelParabolic source.flag i).subtype := by
  have hed : (cosetGraph R).edist (alpha R) s.middle = 2 := by
    rw [← ((cosetGraph_connected R) (alpha R) s.middle).coe_dist_eq_edist, s.first_distance]
    rfl
  obtain ⟨b, hab, hmb⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  have hab' := (cosetGraph_adj R _ _).mp hab
  have hmb' := (cosetGraph_adj R _ _).mp hmb
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab'
    cases hc : color R b <;> simp_all [alpha, color, mVertex]
  have hV : V R s.middle ≤ Q R b :=
    (Flags.V_le_Q geometry common.large_distance s.middle s.middle_color).trans
      (Q_le_adjacent_h R hb hmb')
  obtain ⟨g, hg, hgb⟩ := stabilizer_transitive_neighbors R (alpha R) hab' (base_adjacent R)
  rw [alpha, stabilizer_m_base] at hg
  obtain ⟨m, rfl⟩ := hg
  have hQ : (Q R b).map (MulAut.conj (embedM R m)⁻¹).toMonoidHom = Q R (beta R) := by
    rw [← Q_act, hgb]
    rfl
  have himage : ((Q R (beta R)).comap (embedM R)).map source.projection =
      (pCore 2 (modelParabolic source.flag i)).map (modelParabolic source.flag i).subtype := by
    rw [← hkernel, Flags.RankOne.flagKernel,
      comap_map_eq_self_of_injective (embedM_injective R), parabolicCore_projection]
  refine ⟨source.projection m⁻¹, eq_of_le_of_card_ge ?_ ?_⟩
  · rw [← himage]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n, hn, rfl⟩ := ha
    refine ⟨m⁻¹ * n * m, ?_, ?_⟩
    · change embedM R (m⁻¹ * n * m) ∈ Q R (beta R)
      rw [← hQ]
      refine ⟨embedM R n, hV hn, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.conj_inv_apply]
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.conj_inv_apply]
  · rw [card_map_of_injective (modelParabolic source.flag i).subtype_injective,
      card_map_of_injective (MulAut.conj (source.projection m⁻¹)).injective, hcard]
    exact (Matrix.PSL3Two.ParabolicCoreModel.core_data
      (modelParabolicEquivSymmetric source.flag i)).2.le

include common in
/-- The midpoint fixed-preimage bound controls the selected parabolic on the original representation. -/
theorem codimension_of_midpoint (d : CoreModule source) (s : CriticalSegment geometry)
    (h : MidpointFacts (source := source) s)
    (i : Bool) (hkernel : Flags.RankOne.flagKernel source i = Q R (beta R)) :
    fixedCodim d.representation
      ((pCore 2 (modelParabolic source.flag i)).map (modelParabolic source.flag i).subtype) ≤ 2 := by
  obtain ⟨g, hg⟩ := midpointActor_conjugate_flagCore source geometry common s h.card i hkernel
  rw [← hg, fixedCodim_map_conj]
  exact CoreModule.fixedCodim_le_two_of_preimage_index source geometry common d _ h.fixed_index

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
