module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities

/-!
# The exact projected midpoint actor

Critical-pair reversal makes V_c escape Q_alpha. Rebase the edge (c,beta)
at (alpha,beta); the transformed distance-two generator has noncentral
displacement, since the radius-derived subgroup meets the intrinsic local
center trivially. The earlier displacement calculation, with FlagControl
still explicit, gives index four. Conjugation and the actual quotient map
transport that index to the order of the original midpoint actor.

This proves the missing lower bound independently of seed recognition or
fixation by the other core. Finiteness is used only in the local groups.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the symmetric use of (4.6.9), printed p.908, in (4.6.12), p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem displacement_noncentral_of_escape
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    {c : Vertex R} (hd : (cosetGraph R).dist (alpha R) c = 2)
    (hescape : ¬ V R (alpha R) ≤ Q R c) :
    ¬ ⁅Z R c, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro hc
  have hZ : Z R c ≤ V R (alpha R) :=
    le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd]) le_rfl)
  have hzero : ⁅Z R c, V R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← Sections.U_inf_localCenter_eq_bot common]
    exact le_inf ((commutator_mono hZ le_rfl).trans_eq
      (radius.radius_derived (alpha R) rfl)) hc
  have hcentral : V R (alpha R) ≤ centralizer (Z R c : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have he := radius_inf_kernel common rfl hd
  rw [inf_eq_left.mpr hcentral] at he
  exact hescape (inf_eq_left.mp he)

/-- Rebasing the opposite edge gives the exact order of the original midpoint actor. -/
theorem midpoint_actor_card (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (control : Flags.RankOne.FlagControl source) :
    Nat.card (midpointActor (source := source) s.middle) = 4 := by
  have hescape : ¬ V R s.middle ≤ Q R (alpha R) := by
    intro h
    have he := (common.critical_reverse (alpha R) rfl s.endpoint
      (critical_endpoint_color R (alpha R) rfl _ s.critical) s.critical).2
    apply he
    apply le_trans _ h
    exact le_iSup_of_le s.endpoint (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm]; exact s.second_distance.le) le_rfl)
  obtain ⟨g, hg | hg⟩ := edge_transitive R (adjacent_symm R hbc) (base_adjacent R)
  · change act R g s.middle = alpha R ∧ act R g (beta R) = beta R at hg
    have hd : (cosetGraph R).dist (alpha R) (act R g (alpha R)) = 2 := by
      calc
        _ = (cosetGraph R).dist (act R g s.middle) (act R g (alpha R)) := by rw [hg.1]
        _ = (cosetGraph R).dist s.middle (alpha R) := dist_act R g _ _
        _ = 2 := by rw [SimpleGraph.dist_comm, s.first_distance]
    have he : Adjacent R (beta R) (act R g (alpha R)) := by
      have hh := (adjacent_act_iff R g (beta R) (alpha R)).mpr
        (adjacent_symm R (base_adjacent R))
      rwa [hg.2] at hh
    have hx : ¬ V R (alpha R) ≤ Q R (act R g (alpha R)) := by
      intro hx
      have hm : V R (alpha R) = (V R s.middle).map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [← hg.1, V_act]
      rw [hm, Q_act] at hx
      exact hescape ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hx)
    have hi := (Flags.RankOne.displacement_cardinalities source geometry common hb
      radius.toEarlyFacts control (act R g (alpha R)) hd he
      (displacement_noncentral_of_escape common radius hd hx)).2.2.2
    have hindex : (Q R (alpha R)).relIndex (V R s.middle) = 4 := by
      have ht : (Q R (act R g (alpha R))).relIndex (V R (alpha R)) =
          (Q R (alpha R)).relIndex (V R s.middle) := by
        calc
          _ = (Q R (act R g (alpha R))).relIndex (V R (act R g s.middle)) := by rw [hg.1]
          _ = _ := by rw [Q_act, V_act, relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact ht.symm.trans hi
    calc
      _ = (Q R (alpha R)).relIndex (V R s.middle) := by
        rw [midpointActor, ← relIndex_ker, source.projection_kernel]
        rw [Q_alpha R source.two_group source.core_le]
        rw [← relIndex_map_map_of_injective _ _ (embedM_injective R), map_comap_eq]
        change (map (embedM R) (pCore 2 M)).relIndex (Mbar R ⊓ V R s.middle) = _
        rw [inf_eq_right.mpr (midpoint_radius_le_Mbar common s hbc)]
      _ = 4 := hindex
  · change act R g s.middle = beta R ∧ act R g (beta R) = alpha R at hg
    have hc : color R (beta R) = false := by
      rw [← hg.1, action_preserves_color, s.middle_color]
    contradiction
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
