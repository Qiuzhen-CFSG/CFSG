module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences

/-!
# The printed base-core generation formula stays in a proper parabolic

Both intrinsic cores of an incident flag lie in the common lifted Sylow
subgroup, hence in both parabolics. Compatibility identifies the first
core with Q_beta, which contains V_c and Q_alpha. Therefore the join of
V_c, the base Q_delta2 and Q_alpha cannot generate G_alpha.

This diagnoses the literal Q_delta2 formula on MS93 (1993), printed p.911,
under the notation of p.905. The preceding sentence instead forms U using
Q_delta4. Algebra supplies the normalization reduction using that conjugating
core, with its generation still an explicit proof obligation. No replacement
generation or source span conclusion is asserted by this diagnostic.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Each intrinsic core is contained in both parabolics of the incident flag. -/
theorem Frame.core_le_parabolic (f : Frame source) (i j : Bool) :
    f.core i ≤ f.parabolic j := by
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  let T := liftedBorelSylow source.projection source.projection_surjective hk f.flag
  have ht (k : Bool) : (T : Subgroup M) ≤ f.parabolic k := by
    dsimp [T]
    rw [coe_liftedBorelSylow]
    exact comap_mono (modelParabolic_borel_le _ _)
  have hcore : f.core i ≤ (T : Subgroup M) := by
    have h := map_mono (f := (f.parabolic i).subtype)
      (pCore_isPGroup.le_sylow_of_normal (T.subtype (ht i)))
    change f.core i ≤ ((T : Subgroup M).subgroupOf (f.parabolic i)).map
      (f.parabolic i).subtype at h
    rwa [map_subgroupOf_eq_of_le (ht i)] at h
  exact hcore.trans (ht j)

/-- Surjectivity of the marked quotient keeps each full parabolic proper. -/
theorem Frame.parabolic_ne_top (f : Frame source) (i : Bool) : f.parabolic i ≠ ⊤ := by
  intro h
  have he := congrArg (map source.projection) h
  change ((modelParabolic f.flag (if i then !f.first else f.first)).comap
    source.projection).map source.projection = _ at he
  rw [map_comap_eq, source.projection.range_eq_top_of_surjective source.projection_surjective,
    top_inf_eq, map_top_of_surjective _ source.projection_surjective] at he
  have hc := card_modelParabolic f.flag (if i then !f.first else f.first)
  rw [he, Nat.card_congr Subgroup.topEquiv.toEquiv, Matrix.PSL3Two.card_SL] at hc
  norm_num at hc

/-- The incident midpoint radius and both base cores remain in the first
proper parabolic. Thus the Q_delta2 generation formula cannot be used. -/
theorem base_actor_join_le_parabolic [Finite M] (common : CommonFacts R source geometry)
    {f : Frame source} {s : CriticalSegment geometry} (hf : Compatible f s)
    (hbc : Adjacent R (beta R) s.middle) :
    (V R s.middle ⊔ (f.core true).map (embedM R)) ⊔ Q R (alpha R) ≤
      f.ambient false := by
  have hQb : Q R (beta R) ≤ f.ambient false := by
    rw [← hf.first_core]
    exact map_mono (f.core_le_parabolic false false)
  have hVc : V R s.middle ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ s.middle_color).trans
      (Q_le_adjacent_h R rfl (adjacent_symm R hbc))
  have hQa : Q R (alpha R) ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (base_adjacent R)
  exact sup_le (sup_le (hVc.trans hQb) (map_mono (f.core_le_parabolic true false)))
    (hQa.trans hQb)

/-- With the actual incident-frame definitions, the literal Q_delta2
expression on printed p.911 is not the full local actor. This diagnostic
leaves the requested span theorem unchanged. -/
theorem base_actor_join_ne_stabilizer [Finite M] (common : CommonFacts R source geometry)
    {f : Frame source} {s : CriticalSegment geometry} (hf : Compatible f s)
    (hbc : Adjacent R (beta R) s.middle) :
    (V R s.middle ⊔ (f.core true).map (embedM R)) ⊔ Q R (alpha R) ≠
      stabilizer R (alpha R) := by
  intro h
  have ht := base_actor_join_le_parabolic common hf hbc
  rw [h] at ht
  have he : f.ambient false = stabilizer R (alpha R) :=
    le_antisymm (f.ambient_le false) ht
  have hm : (f.parabolic false).map (embedM R) = (⊤ : Subgroup M).map (embedM R) := by
    rw [← MonoidHom.range_eq_map]
    exact he.trans (stabilizer_m_base R)
  exact f.parabolic_ne_top false ((map_injective (embedM_injective R)) hm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
