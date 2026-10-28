module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Assembly

/-!
# Opening calculations and one permitted rechoice for 14.7.70

`exists_prepared_branches`, exported by the Assembly module, constructs
one permitted rechoice, proves its marked-cover calculations, and supplies both
local-geometry branches on the original projection. It applies the fixed-line
and intersection consumers in low rank and constructs the rank-three
`Preliminary` interface. The earlier conditional applications below retain
their public statements for existing consumers.

The preparation premises of these conditional applications are discharged by
the new assembly. The precise earlier-source inputs retain the producers
documented in Assembly; their final discharge remains with qt-14-07.
Local geometry assembly remains qt-14-07-rechoice-local-geometry, and full70
assembly remains qt-14-07-critical-rechoice.

Source: Aschbacher–Smith, combined manuscript, 1 March2004,
proof of14.7.70, printed pp.1073–1074 (PDF1090–1091).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

/-- The published fixed-line consumer applied to one actual permitted
reselection. `exists_prepared_rechoice` now constructs its centrality and
careful-choice premises. Every actor,
commutator and image below concerns this same reselected path. -/
theorem selected_point_of_permitted_choice (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (mark : UpperMarking d)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (n : group F L) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hF9 : ⁅F.U ⊓ (c.reselect n).Qα, (c.reselect n).Uα⁆ ≤ (c.reselect n).Zα)
    (hcentral : star F (c.reselect n).Uα ≤
      Chapter12.Section08.centerIn (star F (T : Subgroup G)))
    (hchoice : (c.reselect n).Zα ≤ F.Vi 2 ⊔ d.U₀) :
    (c.reselect n).Zα ≤ F.Vi 2 := by
  let s := d.actionDescentOfCore hcore
  have earlier' := c.reselect_earlierImages earlier n
  have selection' := reselect_rankSelection d c earlier selection n
  have h69' : Nat.card (star F (c.reselect n).Uα) = 2 :=
    (c.reselect_star_card earlier n).trans h69
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d (c.reselect n) earlier' mark h69'
  have hZ := (original_point_in_commutator d (c.reselect n) earlier' s mark
    selection' h69' hF9).2
  exact selected_point_le_plane d (c.reselect n) earlier' separation s h t ht he
    (actorT_commutes d (c.reselect n) hcentral h hh)
    (commutator_image d (c.reselect n) earlier' s h69' h hh (upper_actor_ne_one d h t ht he))
    h65 (upper_mem_actorT d mark) hrank hZ hchoice

/-- Compatibility application for actual rank-three consumer data.
`exists_prepared_rechoice` now supplies marked disjointness and quotient
centrality together. The ambient commutator and noncontainment conclusions
are proved here from literal earlier inputs. -/
theorem rank_three_data_of_disjointness (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1) (mark : UpperMarking d)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hcentral : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)))
    (hd : Disjoint (tilde d (Fcomm c)) (tilde d V)) :
    Fcomm c ≤ F.U ⊓ c.Uα ∧ c.Zα ≤ Fcomm c ∧ F.Vi 1 ≤ Fcomm c ∧
      (T : Subgroup G) ≤ normalizer (Fcomm c : Set G) ∧
      Nat.card (Fcomm c) = 8 ∧ Fcomm c ⊓ d.U₀ = F.Vi 1 ∧
      ¬ c.Zα ≤ d.U₀ ∧ ¬ c.Zα ≤ V := by
  obtain ⟨hF, hZ, hP, hn, hc, hi⟩ := preliminary_geometry d c earlier
    (d.actionDescentOfCore hcore) mark selection h69 hUH heven hF9 hF9α hcentral
  have hZ₀ := point_not_le_U₀ d c h69 h68
  exact ⟨hF, hZ, hP, hn, hc, hi, hZ₀, point_not_le_seed d c earlier hZ hZ₀ hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
