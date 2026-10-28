module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Sections

/-!
# Central factors of the MS93 commutator core

The source fixed group D_a is `fixedCore`, whereas the target V of (4.5)
is `core = [Q,Ltilde]`. Local normality of D_a and the three-subgroups
lemma show that the core centralizes D_a. This places the core's fixed
factor in its center without any critical-distance hypothesis.

With the exact centrality conclusion of (4.4) explicit, H lies in that
fixed factor and in Z_a. The common natural splitting then proves
U_alpha and H_alpha disjoint, and their join lies in the core center.
The reverse containment, fixed-factor equality and order four are the
remaining source obligations; none is a premise or conclusion here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4)--(4.5), printed pp.890--900.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The literal core centralizes source D_a, by local normality and three subgroups. -/
theorem core_centralizes_fixedCore (a : Vertex R) :
    ⁅core R a, fixedCore R a⁆ = ⊥ := by
  have hfix : ⁅fixedCore R a, Ltilde R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hnormal : ⁅fixedCore R a, Q R a⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (PathCentrality.fixedCore_normalized R a))
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_comm (Ltilde R a), hfix, commutator_bot_left]
  · exact le_bot_iff.mp ((commutator_mono hnormal le_rfl).trans hfix.le)

/-- The core fixed by Ltilde lies centrally in the core, without distance assumptions. -/
theorem fixedFactor_le_coreCenter (a : Vertex R) :
    core R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≤
      (center (core R a)).map (core R a).subtype := by
  intro x hx
  refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact (commutator_eq_bot_iff_le_centralizer.mp
    (core_centralizes_fixedCore a) y.property) x
      ⟨DistanceTwo.core_le_Q a hx.1, hx.2⟩ |>.symm

/-- At positive radius-two clearance, the moving radius group lies in the actual core. -/
theorem Vcirc_le_core {a : Vertex R} (ha : color R a = false)
    (hb : 2 < geometry.b R) : Vcirc R a ≤ core R a :=
  commutator_mono (PathCentrality.V_le_Q R ha hb) le_rfl

/-- The actual fixed commutator H lies in the core; normality is used only inside G_a. -/
theorem H_le_core {a : Vertex R} (ha : color R a = false)
    (hb : 2 < geometry.b R) : H R a ≤ core R a :=
  (commutator_mono (Vcirc_le_core ha hb) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (DistanceTwo.core_normalized a)))

private theorem localCenter_le_centralizer (a : Vertex R)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ stabilizer R a) :
    (center (stabilizer R a)).map (stabilizer R a).subtype ≤
      centralizer (A : Set (FreeAmalgam R)) := by
  rintro x ⟨z, hz, rfl⟩ y hy
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hA hy⟩)

/-- The centrality conclusion of (4.4) gives one inclusion in (4.5)(iii). -/
theorem H_le_fixedFactor_of_central {a : Vertex R} (ha : color R a = false)
    (hb : 2 < geometry.b R)
    (hc : ⁅V R a, Q R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) :
    H R a ≤ core R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
  le_inf (H_le_core ha hb)
    ((H_le_localCenter_of_central R a hc).trans
      (localCenter_le_centralizer a (map_subtype_le _)))

/-- Centrality and the existing involution argument place H in the literal Z-layer. -/
theorem H_le_Z_of_central {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a : Vertex R} (ha : color R a = false)
    (hc : ⁅V R a, Q R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) : H R a ≤ Z R a := by
  rw [← common.X_eq_Z a ha]
  let := H_elementary_of_central R a
    (geometry.V_local a ha (by rw [geometry.distance_constant a ha]; exact common.large_distance)) hc
  intro x hx
  apply mem_omegaCenter_iff.mpr
  refine ⟨DistanceTwo.core_le_Q a (H_le_core ha common.large_distance hx), ?_, ?_⟩
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := H R a) x hx
  · exact localCenter_le_centralizer a
      (show Q R a ≤ stabilizer R a from fun _ hy => hy.1)
      (H_le_localCenter_of_central R a hc hx)

/-- The disjointness clause of (4.5)(iv), conditional only on (4.4) centrality. -/
theorem U_disjoint_H_of_central {source : LocalSource L R}
    (common : CommonFacts R source geometry)
    (hc : ⁅V R (alpha R), Q R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    Disjoint (U R (alpha R)) (H R (alpha R)) := by
  apply common.disjoint.mono_right
  exact le_inf (H_le_Z_of_central common rfl hc)
    ((H_le_fixedFactor_of_central rfl common.large_distance hc).trans inf_le_right)

/-- One inclusion in (4.5)(iv), using the actual U and H subgroups. -/
theorem U_join_H_le_coreCenter_of_central [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry)
    (hc : ⁅V R (alpha R), Q R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    U R (alpha R) ⊔ H R (alpha R) ≤
      (center (core R (alpha R))).map (core R (alpha R)).subtype := by
  apply sup_le
  · intro x hx
    exact ⟨⟨x, DistanceTwo.U_le_core geometry (by have := common.large_distance; omega)
      (alpha R) rfl hx⟩, DistanceTwo.U_subgroupOf_core_le_center (alpha R) rfl hx, rfl⟩
  · exact (H_le_fixedFactor_of_central rfl common.large_distance hc).trans
      (fixedFactor_le_coreCenter (alpha R))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors
