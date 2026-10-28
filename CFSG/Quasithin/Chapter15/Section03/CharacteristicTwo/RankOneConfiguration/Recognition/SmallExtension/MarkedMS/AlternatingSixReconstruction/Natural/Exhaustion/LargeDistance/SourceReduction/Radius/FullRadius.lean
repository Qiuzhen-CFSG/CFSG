module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.DerivedOrder
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The full radius has the same derived subgroup as its moving part

The relative three-subgroups lemma puts [V,[V,L]] in [[V,L],[V,L]]
when L fixes V′ and the moving commutator is idempotent. The actual
abelian edge radius supplements the moving radius, so V′ equals its moving
derived subgroup. The established natural-cover bound therefore gives
|V′| ≤ 2 on every original-group vertex, without a fixed-factor splitting.

Source: MS93 (3.8), printed p.879, the final commutator-order argument.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius

/-- Fixed full derived group, idempotent movement, and an abelian supplement
identify the full derived subgroup with the moving derived subgroup. -/
theorem derived_eq_moving_derived {H : Type*} [Group H]
    (V P J E : Subgroup H) (hP : P ≤ V) (hE : E ≤ V)
    (hPJ : ⁅P,J⁆ = P) (hVJ : ⁅V,J⁆ = P)
    (hJn : J ≤ normalizer (P : Set H)) (hVn : V ≤ normalizer (P : Set H))
    (hfixed : ⁅⁅V,V⁆,J⁆ = ⊥) (hgen : V = P ⊔ E)
    (hcomm : IsMulCommutative E) : ⁅V,V⁆ = ⁅P,P⁆ := by
  have hn : normalizer (P : Set H) ≤ normalizer ((⁅P,P⁆ : Subgroup H) : Set H) := by
    rw [←map_subtype_commutator]
    exact normalizer_le_normalizer_characteristic_image P (_root_.commutator P)
  have hpv : ⁅P,V⁆ ≤ ⁅P,P⁆ := by
    have hh := commutator_commutator_le_of_rotate_of_le_normalizer
      (P.le_normalizer.trans hn) (hJn.trans hn) (hVn.trans hn)
      (show ⁅⁅J,V⁆,P⁆ ≤ ⁅P,P⁆ by rw [commutator_comm J V,hVJ])
      ((commutator_mono (commutator_mono le_rfl hP) le_rfl).trans (hfixed.le.trans bot_le))
    rwa [hPJ] at hh
  apply le_antisymm _ (commutator_mono hP hP)
  have hee : ⁅E,E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr hcomm)
  have hev : ⁅E,V⁆ ≤ ⁅P,P⁆ := by
    rw [commutator_comm E V,hgen]
    apply commutator_sup_le_of_relative_normal V P E E ⁅P,P⁆ (hVn.trans hn) hP hE
      ((commutator_mono le_rfl hE).trans hpv)
    exact hee.le.trans bot_le
  conv_lhs => arg 1; rw [hgen]
  exact commutator_sup_le_of_relative_normal V P E V ⁅P,P⁆ (hVn.trans hn) hP hE hpv hev

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The full source radius and its moving subgroup have the same derived group. -/
theorem radius_derived_eq_moving_derived
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅V r.radical a,V r.radical a⁆ = ⁅Vcirc r.radical a,Vcirc r.radical a⁆ := by
  have hb : 2 < replacementDistance h r := by rw [fg.distance]; decide
  obtain ⟨g,hg⟩ := exists_mVertex_of_color r.radical ha
  let t := hVertex r.radical g
  have hat : Adjacent r.radical a t := by
    rw [hg]
    exact (adjacent_iff_exists_common r.radical _ _).mpr ⟨g,Or.inl ⟨rfl,rfl⟩⟩
  have hVS : V r.radical a ≤ stabilizer r.radical a :=
    ((replacementGeometry h r).V_le_Q hb a ha).trans (fun _ hx => hx.1)
  apply derived_eq_moving_derived (V r.radical a) (Vcirc r.radical a)
    (Ltilde r.radical a) (V r.radical t)
  · exact le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (V_normalized a))
  · exact edge_radius_le_radius ha hat
  · exact moving_full_commutation h r hb a ha
  · rfl
  · exact (Ltilde_le_stabilizer a).trans (Vcirc_normalized a)
  · exact hVS.trans (Vcirc_normalized a)
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      ((radius_derived_le_fixed h m hz hn r himage fg a ha).trans inf_le_right)
  · exact radius_eq_moving_sup_edge h m hz hn r himage ha hat
  · exact edge_radius_commutative (replacementGeometry h r) hb a t ha hat

/-- The full radius, with its original central attachment, has derived order
at most two. No splitting into moved and fixed factors is needed. -/
theorem radius_derived_card_le_two
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    Nat.card (⁅V r.radical a,V r.radical a⁆ : Subgroup (FreeAmalgam r.radical)) ≤ 2 := by
  rw [radius_derived_eq_moving_derived h m hz hn r himage fg a ha]
  exact moving_derived_card_le_two h m hz hn r himage fg a ha

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
