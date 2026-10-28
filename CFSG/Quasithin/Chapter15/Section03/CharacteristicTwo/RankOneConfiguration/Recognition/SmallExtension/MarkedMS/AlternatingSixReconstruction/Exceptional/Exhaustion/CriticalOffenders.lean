module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Critical
public import Theory.Representation.NormalElementaryQuotient.OriginalAction
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Critical offenders with the retained cubic kernel

The edge centralizer identity identifies critical displacement with the
actual Q-index, even when the initial kernel contains E/Q of order three.
Reverse and conjugate a critical pair to choose the favorable orientation.
The canonical moved/fixed quotient then supplies a natural A₆ offender
under its literal six-letter action. No splitting of X is used.

Source: MS93 (2.2)(i),(vi), pp.856--857, and (3.2)(vi), pp.863--864.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

/-- At any positive critical distance, the endpoint centralizer in the
opposite X-layer is exactly its intersection with the original Q. -/
theorem critical_X_centralizer_intersection
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (a : Vertex T) (ha : color T a = false) (c : Vertex T)
    (hc : CriticalPair T a c ((sourceGeometry h).exists_critical a ha)) :
    X T c ⊓ centralizer (X T a : Set (FreeAmalgam T)) = X T c ⊓ Q T a := by
  have hcCol := critical_endpoint_color T a ha _ hc
  obtain ⟨t,hat,htc⟩ := exists_adjacent_dist_sub_one T a c (by
    rw [hc.1,(sourceGeometry h).distance_constant a ha]
    exact sourceDistance_pos h)
  have hXt : X T c ≤ Q T t :=
    X_le_Q_of_dist_lt T (sourceGeometry h) (sourceEdgeCentralizer h e) c hcCol t (by
      rw [SimpleGraph.dist_comm,(sourceGeometry h).distance_constant c hcCol]
      have hh := hc.1.trans ((sourceGeometry h).distance_constant a ha)
      change (cosetGraph T).dist t c < sourceDistance h
      change (cosetGraph T).dist a c = sourceDistance h at hh
      omega)
  have hZa := (sourceGeometry h).omega_bound a ha (by
    rw [(sourceGeometry h).distance_constant a ha]
    exact sourceDistance_pos h)
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    exact ⟨hx,(sourceEdgeCentralizer h e a t ha hat) ▸
      ⟨hXt hx,centralizer_le hZa hxc⟩⟩
  · exact le_inf inf_le_left (inf_le_right.trans (Q_le_centralizer_X T a))

/-- The image index is exact even when the full initial kernel retains
an odd cubic factor. -/
theorem critical_displacement_eq_core_index
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (a : Vertex T) (ha : color T a = false) (c : Vertex T)
    (hc : CriticalPair T a c ((sourceGeometry h).exists_critical a ha)) :
    Offenders.displacement (X T c) (X T a) = (Q T a).relIndex (X T c) := by
  unfold Offenders.displacement
  rw [← inf_relIndex_left (X T c), critical_X_centralizer_intersection h e a ha c hc,
    inf_relIndex_left]

/-- Choose the critical orientation whose base displacement is smaller. -/
theorem exists_base_favorable_critical_pair
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    ∃ c : Vertex T,
      CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl) ∧
      Offenders.displacement (X T (alpha T)) (X T c) ≤
        Offenders.displacement (X T c) (X T (alpha T)) := by
  obtain ⟨c,hc⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  by_cases hh : Offenders.displacement (X T (alpha T)) (X T c) ≤
      Offenders.displacement (X T c) (X T (alpha T))
  · exact ⟨c,hc,hh⟩
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hgcCol : color T (act T g⁻¹ c) = false := by rw [hg]; rfl
  have hc' := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hgcCol)).mpr hr
  have hcmp :
      Offenders.displacement (X T (act T g⁻¹ c)) (X T (act T g⁻¹ (alpha T))) ≤
        Offenders.displacement (X T (act T g⁻¹ (alpha T))) (X T (act T g⁻¹ c)) := by
    rw [X_act,X_act,Offenders.displacement_map,Offenders.displacement_map]
    exact (lt_of_not_ge hh).le
  exact ⟨act T g⁻¹ (alpha T),by simpa only [hg] using hc',by simpa only [hg] using hcmp⟩

namespace CubicAction
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "π" => projection h e hz hk
local notation "ρ₆" => BinaryPermutation.naturalRepresentation (Fin 6)

/-- The image of a literal graph subgroup, using the natural quotient marking. -/
@[expose] def graphImage (A : Subgroup (FreeAmalgam T)) : Subgroup (Equiv.Perm (Fin 6)) :=
  (A.comap (embedM T)).map π

omit [Finite G] in
private theorem centralizer_comap (A : Subgroup (FreeAmalgam T))
    (hA : A ≤ stabilizer T (alpha T)) :
    (centralizer (A : Set (FreeAmalgam T))).comap (embedM T) =
      centralizer (A.comap (embedM T) : Set M) := by
  have hm : (A.comap (embedM T)).map (embedM T) = A :=
    map_comap_eq_self (hA.trans_eq (stabilizer_m_base T))
  ext x
  constructor
  · intro hx y hy
    apply embedM_injective T
    simpa only [map_mul] using hx _ hy
  · intro hx y hy
    rw [←hm] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [map_mul] using congrArg (embedM T) (hx z hz)

/-- The image order records displacement on the original X, not on a
chosen natural complement. -/
theorem graphImage_card (A : Subgroup (FreeAmalgam T))
    (hA : A ≤ stabilizer T (alpha T)) :
    Nat.card (graphImage h e hz hk A) =
      Offenders.displacement A (X T (alpha T)) := by
  have hm : (A.comap (embedM T)).map (embedM T) = A :=
    map_comap_eq_self (hA.trans_eq (stabilizer_m_base T))
  have hX : (X T (alpha T)).comap (embedM T) = centralOmega L R := by
    rw [graph_X h,comap_map_eq_self_of_injective (embedM_injective T)]
  have hcent := centralizer_comap (X T (alpha T))
    ((omegaCenter_le _).trans (fun _ hx => hx.1))
  rw [hX] at hcent
  rw [graphImage,←relIndex_ker,projection_kernel,←hk]
  change (centralizer (centralOmega L R : Set M)).relIndex (A.comap (embedM T)) = _
  rw [←hcent,relIndex_comap,hm]
  rfl

/-- The natural central quotient has no greater displacement than the
whole initial elementary layer. -/
theorem graphImage_index_le (A : Subgroup (FreeAmalgam T))
    (hA : A ≤ stabilizer T (alpha T)) :
    2 ^ fixedCodim ρ₆ (graphImage h e hz hk A) ≤
      Offenders.displacement (X T (alpha T)) A := by
  have hi := natural_index_le h e hz hk (A.comap (embedM T))
  rw [←centralizer_comap A hA,relIndex_comap,←graph_X h] at hi
  exact hi

/-- Both elementary structure and the exact Q-index survive the cubic
kernel on an actual critical endpoint. -/
theorem critical_image_data (c : Vertex T)
    (hcrit : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    IsElementaryTwo (graphImage h e hz hk (X T c)) ∧
      Nat.card (graphImage h e hz hk (X T c)) = (Q T (alpha T)).relIndex (X T c) := by
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hcrit
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hcrit
  have hE := critical_X_le_vertex h e c hcCol (alpha T) hr
  have hm : ((X T c).comap (embedM T)).map (embedM T) = X T c :=
    map_comap_eq_self (hE.trans_eq (stabilizer_m_base T))
  have hcard := (graphImage_card h e hz hk (X T c) hE).trans
    (critical_displacement_eq_core_index h e (alpha T) rfl c hcrit)
  let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((X T c).comap (embedM T)) :=
    IsElementaryAbelian.comap_of_injective (embedM T) (embedM_injective T) (X T c)
  refine ⟨⟨?_,IsElementaryAbelian.map π⟩,hcard⟩
  intro hbot
  have hi : (Q T (alpha T)).relIndex (X T c) = 1 := by
    rw [←hcard,hbot,Nat.card_unique]
  have hX := relIndex_eq_one.mp hi
  apply hr.2
  exact ((sourceGeometry h).omega_bound c hcCol (by
    rw [(sourceGeometry h).distance_constant c hcCol]
    exact sourceDistance_pos h)).trans hX

/-- The favorable critical endpoint is an actual offender on the natural
central quotient, at every positive critical distance. -/
theorem critical_offender_of_comparison (c : Vertex T)
    (hcrit : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hcomp : Offenders.displacement (X T (alpha T)) (X T c) ≤
      Offenders.displacement (X T c) (X T (alpha T))) :
    IsOffender ρ₆ (graphImage h e hz hk (X T c)) := by
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hcrit
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hcrit
  have hE := critical_X_le_vertex h e c hcCol (alpha T) hr
  have hel := (critical_image_data h e hz hk c hcrit).1
  refine ⟨hel,?_⟩
  have hb := (graphImage_index_le h e hz hk (X T c) hE).trans hcomp
  rw [←graphImage_card h e hz hk (X T c) hE,hel.card_eq_two_pow_rank] at hb
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

/-- An actual critical natural offender exists without a distance-two
assumption, a Sylow assumption, or a split central attachment. -/
theorem exists_critical_offender :
    ∃ c : Vertex T,
      CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl) ∧
      IsOffender ρ₆ (graphImage h e hz hk (X T c)) := by
  obtain ⟨c,hcrit,hcomp⟩ := exists_base_favorable_critical_pair h e
  exact ⟨c,hcrit,critical_offender_of_comparison h e hz hk c hcrit hcomp⟩

end CubicAction
end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
