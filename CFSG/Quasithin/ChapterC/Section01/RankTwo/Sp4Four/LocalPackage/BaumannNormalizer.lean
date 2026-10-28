module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage
public import Glauberman.BaumannNormalizer
public import Theory.GroupTheory.CharacteristicImageNormalizer

/-!
# The literal Baumann normalizer in the Sp4(4) local argument

The source Baumann subgroup is formed from the actual replacement radical
T_beta and the ordinary all-abelian Thompson subgroup. Its characteristic
subgroups are normalized by the holomorph vertex group. If such a subgroup
is normal in the constructed rank-one group F₀ and the source extra
normalizer generates the other vertex group with F₀, common normality at
the edge forces it to be trivial.

This proves the characteristic-subgroup hypothesis of the Niles application
in MS93 (5.1), printed p.913, once the marked Sylow and generation witnesses
have been constructed. It does not assume that Q_alpha lies in F₀.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
variable {M : Type*} [Group M] (R : Subgroup M)
noncomputable abbrev sourceBaumann (t : Vertex R) : Subgroup (FreeAmalgam R) :=
  Glauberman.baumannSubgroup (Q R t)
theorem sourceBaumann_normalized (t : Vertex R) :
    stabilizer R t ≤ normalizer (sourceBaumann R t : Set (FreeAmalgam R)) :=
  (Q_normalized R t).trans (Glauberman.normalizer_le_normalizer_baumannSubgroup _)

theorem characteristic_sylow_eq_bot_of_source_generation
    (hms : MSCharacteristicCondition R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (F0 : Subgroup (FreeAmalgam R)) (hF0 : F0 ≤ stabilizer R a)
    (S : Sylow 2 F0)
    (hS : (S : Subgroup F0).map F0.subtype = sourceBaumann R t)
    (C : Subgroup S) [C.Characteristic]
    (hCn : (C.map (S : Subgroup F0).subtype).Normal)
    (N : Subgroup (FreeAmalgam R))
    (hN : N ≤ normalizer ((C.map (S : Subgroup F0).subtype).map F0.subtype : Set (FreeAmalgam R)))
    (hgen : N ⊔ F0 = stabilizer R a) : C = ⊥ := by
  let D := (C.map (S : Subgroup F0).subtype).map F0.subtype
  have hDF : D ≤ F0 := map_subtype_le _
  have hDa : D ≤ stabilizer R a := hDF.trans hF0
  have hDB : D ≤ sourceBaumann R t := by
    rw [←hS]
    exact map_mono (map_subtype_le _)
  have hDt : D ≤ stabilizer R t := hDB.trans (inf_le_left.trans (fun _ hx => hx.1))
  have hFn : F0 ≤ normalizer (D : Set (FreeAmalgam R)) := by
    let := hCn
    have h := (C.map (S : Subgroup F0).subtype).le_normalizer_map F0.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  have hAn : stabilizer R a ≤ normalizer (D : Set (FreeAmalgam R)) := by
    rw [←hgen]
    exact sup_le hN hFn
  have hhol : stabilizer R t ≤ normalizer (D : Set (FreeAmalgam R)) := by
    have h := normalizer_le_normalizer_characteristic_map (S : Subgroup F0) C
      F0.subtype F0.subtype_injective
    rw [hS] at h
    exact (sourceBaumann_normalized R t).trans h
  have hD : D = ⊥ := no_common_normal_at_edge R hms a t ha hat D
    (le_inf hDa hDt)
    ((normal_subgroupOf_iff_le_normalizer hDa).mpr hAn)
    ((normal_subgroupOf_iff_le_normalizer hDt).mpr hhol)
  have hbot : C.map (S : Subgroup F0).subtype = ⊥ :=
    ((C.map (S : Subgroup F0).subtype).map_eq_bot_iff_of_injective
      F0.subtype_injective).mp hD
  exact (C.map_eq_bot_iff_of_injective (S : Subgroup F0).subtype_injective).mp hbot
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage

