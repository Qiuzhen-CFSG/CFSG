module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Subtype
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.AlphaOrbit

/-!
# The original pair on a Sylow realization of the Baumann subgroup

Realizing Baum(T) as a Sylow subgroup S of an intermediate group changes
neither its Baumann subgroup nor its Thompson subgroup. Transport the given
pair through this literal inclusion. The first seed is then the entire
original first member, so its local control maps into the control for the
original restricted first seed. No pair is selected again.

Source: Aschbacher--Smith B.2.3(3)--(4), C.1.19 and C.1.28.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

@[expose] noncomputable def markingEquiv (T : Sylow 2 G) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G)) :
    baumann (S : Subgroup E) ≃* baumann (T : Subgroup G) :=
  ((baumann (S : Subgroup E)).equivMapOfInjective E.subtype E.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      unfold baumann thompsonAlpha
      rw [baumann_map_injective E.subtype E.subtype_injective,hS]
      exact (lemma_B_2_3_4 (T : Subgroup G) (baumann (T : Subgroup G)) le_rfl inf_le_left).symm))

theorem markingEquiv_symm_coe (T : Sylow 2 G) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G))
    (b : baumann (T : Subgroup G)) :
    (((markingEquiv T E S hS).symm b : baumann (S : Subgroup E)) : E) = (b : G) := by
  exact congrArg (baumann (T : Subgroup G)).subtype ((markingEquiv T E S hS).apply_symm_apply b)

@[expose] noncomputable def markedPair (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G)) :
    CharacteristicPair (baumann (S : Subgroup E)) := D.map (markingEquiv T E S hS).symm

theorem marked_member_map (T : Sylow 2 G) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G))
    (A : Subgroup (baumann (T : Subgroup G))) :
    ((A.map (markingEquiv T E S hS).symm.toMonoidHom).map
      (baumann (S : Subgroup E)).subtype).map E.subtype =
        A.map (baumann (T : Subgroup G)).subtype := by
  rw [map_map,map_map]
  congr 1
  ext b
  exact markingEquiv_symm_coe T E S hS b

theorem marked_firstSeed_map (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G)) :
    (FixedPair.firstSeed S (markedPair T D E S hS)).map E.subtype =
      D.first.map (baumann (T : Subgroup G)).subtype := by
  rw [FixedPair.firstSeed,Subgroup.map_inf _ _ _ E.subtype_injective,
    ←omegaOneCenterAmbient_map_injective E.subtype E.subtype_injective,hS]
  change omegaOneCenterAmbient (baumann (T : Subgroup G)) ⊓
    (((D.first.map (markingEquiv T E S hS).symm.toMonoidHom).map _).map _) = _
  rw [marked_member_map]
  apply inf_eq_right.mpr
  exact map_mono D.first_le_omegaCenter

theorem marked_control_map_le (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G)) :
    (control S (markedPair T D E S hS)).map E.subtype ≤ control T D := by
  unfold control
  rw [Subgroup.map_sup]
  apply sup_le
  · rw [map_centralizer_subtype,marked_firstSeed_map]
    exact (inf_le_right.trans (centralizer_le (show FixedPair.firstSeed T D ≤
      D.first.map (baumann (T : Subgroup G)).subtype from inf_le_right))).trans le_sup_left
  · have hn := ((markedPair T D E S hS).second.map (baumann (S : Subgroup E)).subtype).le_normalizer_map E.subtype
    simp only [markedPair,CharacteristicPair.map] at hn
    rw [marked_member_map] at hn
    exact hn.trans le_sup_right

theorem marked_control_ne_top (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G))
    (hout : ¬ E ≤ control T D) : control S (markedPair T D E S hS) ≠ ⊤ := by
  intro he
  have hh := marked_control_map_le T D E S hS
  rw [he,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hout hh

theorem thompson_map (T : Sylow 2 G) (E : Subgroup G)
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G)) :
    (elementaryAbelianMaxJ (S : Subgroup E)).map E.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
  rw [←elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective,hS]
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq
    (baumann (T : Subgroup G)) (T : Subgroup G) inf_le_left
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
    (T : Subgroup G) (baumann (T : Subgroup G)) (elementaryAbelianMaxJ_le_baumann _)
  have he := le_antisymm hs.1 hl.1
  exact le_antisymm (hs.2 he) (hl.2 he.symm)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
