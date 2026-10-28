module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitComponentModels
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SymmetricPairCubic
/-!
# Excluding the symmetric-five pair on the original plus module

Restrict the image of the original Sylow to the normal offender actor.
It normalizes the original L_v plus image, and the actual moving Sylow
element preserves that image while exchanging the marked B.5 factors.
The cubic Sylow three-order contradicts the symmetric-five product
calculation. No lifted containment of L_v in the original orbit is used.

Source: Aschbacher–Smith 13.6.14, printed p.929.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
theorem orbit_symmetric_pair_excluded_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) (hzT : z ∈ Tv T v)
    (hK : K ∈ Yz L T z v)
    (hLvplus : plusImage K L T z v hL hz (Lv L v) ≤ plusImage K L T z v hL hz (Kminus K T v))
    (hthree : ∀ P : Sylow 3 (plusImage K L T z v hL hz (Lv L v)), Nat.card P = 3)
    (d : SourceTwoFactorCase ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (t : G) (ht : t ∈ Tv T v)
    (hex : let := offenderSubgroup_normal (wkRepresentation K L T z v hL hz)
      let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
      d.first.map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = d.first) : False := by
  let ρ := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let Y := plusImage K L T z v hL hz (Lv L v)
  have hYI : Y ≤ I := hLvplus.trans (orbit_plus_le_offenders_source K L T z v hL hz hzT hSylow hK)
  let W := Y.subgroupOf I
  let A := plusActor K L T v
  let f := plusMk K L T z v hL hz
  have htYn (s : A) (hs : (s : G) ∈ Tv T v) : f s ∈ normalizer (Y : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := plusImage_conjBy_source K L T (Lv L v) z v hL hz (le_sup_right.trans le_sup_left) s
    have hc : (Lv L v).conjBy (s : G) = Lv L v := mem_normalizer_iff_map_conj_eq.mp (hL hs)
    rw [hc] at he
    exact he.symm
  obtain ⟨P,hP⟩ := hSylow.restrict (show Tv T v ≤ A from le_sup_right) (plusActor_le_Gv K L T v hK.1.1)
  let Pplus := P.mapSurjective (f := f) (plusMk_surjective K L T z v hL hz)
  obtain ⟨S,hS⟩ := Pplus.exists_subgroupOf_eq_of_normal I
  have hSW : (S : Subgroup I) ≤ normalizer (W : Set I) := by
    rw [← subgroupOf_normalizer_eq hYI]
    intro s hs
    have hsp : (s : Gplus K L T z v hL hz) ∈ (Pplus : Subgroup _) := by
      rw [hS] at hs
      exact hs
    obtain ⟨a,ha,he⟩ := hsp
    change (s : Gplus K L T z v hL hz) ∈ normalizer (Y : Set _)
    exact he ▸ htYn a (hP ▸ mem_map_of_mem A.subtype ha)
  let tA : A := ⟨t,(show Tv T v ≤ A from le_sup_right) ht⟩
  let a : MulAut I := MulAut.conjNormal (f tA)
  have hW : W.map a.toMonoidHom = W := by
    apply map_injective I.subtype_injective
    rw [map_map]
    have ha : I.subtype.comp a.toMonoidHom = (MulAut.conj (f tA)).toMonoidHom.comp I.subtype := by
      ext x
      rfl
    rw [ha,← map_map,map_subgroupOf_eq_of_le hYI]
    exact mem_normalizer_iff_map_conj_eq.mp (htYn tA ht)
  have hWthree (R : Sylow 3 W) : Nat.card R = 3 := by
    let e : W ≃* Y := subgroupOfEquivOfLe hYI
    have hh := hthree (R.mapSurjective (f := e.toMonoidHom) e.surjective)
    change Nat.card ((R : Subgroup W).map e.toMonoidHom) = 3 at hh
    rwa [card_map_of_injective e.injective] at hh
  exact source_symmetric_pair_cubic_excluded d c S W hSW a hex.1 hex.2 hW hWthree
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
