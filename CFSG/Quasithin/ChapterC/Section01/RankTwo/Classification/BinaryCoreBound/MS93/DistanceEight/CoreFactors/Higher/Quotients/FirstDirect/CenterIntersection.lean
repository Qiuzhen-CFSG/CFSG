module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect.Orientation

/-!
# The first-hat centralizer of the original commutator core

The actual Z-layer centralizes the core. The moving radius subgroup cannot
centralize it: the three-subgroups lemma and residual idempotence would kill
the source H-layer of order four. The marked dual first quotient is
irreducible, so its core-centralizing intersection is exactly Z.

The final consumer constructs the original path, full early orbit record,
marked dual section, and this center-intersection conclusion together.
It does not assume or assert that the whole core center lies in the first
hat layer; that remaining higher-layer inclusion belongs to final (4.5).

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), pp.895--900.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem moving_idempotent (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    ⁅Vcirc R (alpha R),Ltilde R (alpha R)⁆ = Vcirc R (alpha R) := by
  let P := stabilizer R (alpha R)
  let H₀ := (V R (alpha R)).subgroupOf P
  let := finite_stabilizer R (alpha R)
  let : H₀.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R (alpha R))
  let := V_elementary_of_four_lt R (a := alpha R) (base_color R) (by rw [earlier.distance]; decide)
  let : IsElementaryAbelian 2 H₀ := IsElementaryAbelian.subgroupOf
    (geometry.V_local (alpha R) (base_color R) common.large_distance)
  have h := commutator_isPPerfect_idempotent (pResidual 2 P) H₀
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 H₀) le_normalizer_of_normal
  have hm := congrArg (fun K : Subgroup P => K.map P.subtype) h
  have hH : H₀.map P.subtype = V R (alpha R) :=
    map_subgroupOf_eq_of_le (geometry.V_local (alpha R) (base_color R) common.large_distance)
  rw [map_commutator,map_commutator,hH] at hm
  exact hm

/-- The original Z-layer centralizes the commutator core. -/
theorem Z_centralizes_core (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) : Z R (alpha R) ≤ centralizer (core R (alpha R) : Set (FreeAmalgam R)) := by
  rw [(LocalCommutator.naturalStructure common).decomposition_at (alpha R) (base_color R)]
  apply sup_le
  · intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := (earlier.factor_inclusions common).2.1 (mem_sup_left hx)
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)
  · exact inf_le_right.trans (centralizer_le (DistanceTwo.core_le_Q (alpha R) |>.trans (fun _ hx => hx.1)))

/-- The moving radius group cannot centralize the actual core: the
three-subgroups lemma would kill the nonzero source H-layer. -/
theorem moving_not_centralizes_core (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) : ¬ Vcirc R (alpha R) ≤ centralizer (core R (alpha R) : Set (FreeAmalgam R)) := by
  intro hc
  have hcl : ⁅H R (alpha R), Ltilde R (alpha R)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr ((H_le_fixedFactor_of_central (base_color R)
      common.large_distance (earlier.centrality (alpha R) (base_color R))).trans inf_le_right)
  have hz : H R (alpha R) = ⊥ := by
    change ⁅Vcirc R (alpha R),Q R (alpha R)⁆ = ⊥
    rw [← moving_idempotent common earlier]
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm (Ltilde R (alpha R)), commutator_comm _ (Vcirc R (alpha R))]
      exact commutator_eq_bot_iff_le_centralizer.mpr hc
    · rw [commutator_comm (Q R (alpha R))]
      exact hcl
  have hlo := Early.First.Layer.H_card_lower common earlier (alpha R) (base_color R)
  rw [hz,card_bot] at hlo
  omega

/-- The first hat meets the centralizer of the actual core in exactly Z.
This is a source center bound on the original carrier, not a premise
identifying the entire core center. -/
theorem first_hat_inf_core_centralizer (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    hatV R (alpha R) (p.walk.getVert 6) ⊓ centralizer (core R (alpha R) : Set (FreeAmalgam R)) = Z R (alpha R) := by
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let D := A ⊓ centralizer (core R (alpha R) : Set (FreeAmalgam R))
  obtain ⟨s⟩ := markedDualSection common earlier p
  have hn : Mbar R ≤ normalizer D := by
    rw [← stabilizer_m_base, ← alpha]
    exact (le_inf (hatV_normalized R _ _)
      ((DistanceTwo.core_normalized (alpha R)).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · by_contra hnot
    have hfull : D ⊔ Z R (alpha R) = A := s.sup_eq_of_not_le inf_le_left hn hnot
    have hAC : A ≤ centralizer (core R (alpha R) : Set (FreeAmalgam R)) := by
      rw [← hfull]
      exact sup_le inf_le_right (Z_centralizes_core common earlier)
    apply moving_not_centralizes_core common earlier
    exact ((Early.Orbit.Source.HatIdentity.SmallSeed.identitiesOnPath common earlier p).center ▸
      (show Vcirc R (alpha R) ≤ Vcirc R (alpha R) ⊔ Z R (alpha R) from le_sup_left)).trans hAC
  · exact le_inf s.lower_le (Z_centralizes_core common earlier)

/-- The original source path carries the marked first dual section and the
literal center-intersection conclusion simultaneously. -/
theorem source_first_section (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    Nonempty (Σ' p : Early.SourcePath R (alpha R),
      Early.Orbit.Source.SourceOrbitFacts R p ∧
      Nonempty (MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) ∧
      hatV R (alpha R) (p.walk.getVert 6) ⊓ centralizer (core R (alpha R) : Set (FreeAmalgam R)) = Z R (alpha R)) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) (base_color R)
  exact ⟨⟨p, Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p,
    markedDualSection common earlier p, first_hat_inf_core_centralizer common earlier p⟩⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
