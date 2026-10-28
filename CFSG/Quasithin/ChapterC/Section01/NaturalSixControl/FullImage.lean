module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.PointFamily
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.EasyCases
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Stellmacher.BaumannNormalizer

/-!
# The full Thompson and Baumann image in the natural S6 point radical

Any nontrivial maximum elementary image contains the point transposition.
Normality under the point stabilizer then makes a Thompson image larger than
that transposition subgroup the full E8 point radical. The Baumann subgroup
contains the Thompson subgroup and has the same full image. These statements
use the actual marked point centralizer and its embedded two-core.

Source: Aschbacher--Smith C.1.37, printed p.142, case (iii), and B.3.4(2)(v).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open scoped IsMulCommutative
open ChapterB ChapterB.BaumannArgument
open Representation.BinaryOffender
open ChapterB.Offenders.Six
universe u
variable {K : Type u} [Group K] [Finite K]
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
namespace SourceData
variable (d : SourceData L V T)
include d

omit [Finite K] in
theorem normalizes_R : d.P ≤ normalizer (d.R : Set K) :=
  d.P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.P (pCore 2 d.P))

omit [Finite K] in
theorem normalizes_B : d.P ≤ normalizer (d.B : Set K) :=
  d.normalizes_R.trans (normalizer_le_normalizer_baumann d.R)

omit [Finite K] in
theorem thompson_normalizes : d.P ≤ normalizer (elementaryAbelianMaxJ d.R : Set K) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ d.R).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp (d.normalizes_R hg)

theorem thompson_image_contains_swap
    (hne : (elementaryAbelianMaxJ d.R).map d.q0 ≠ ⊥) :
    ChapterB.Offenders.pairSwap 6 2 ∈ (elementaryAbelianMaxJ d.R).map d.q0 := by
  let := d.elementary
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups d.R, A.map d.q0 ≠ ⊥ := by
    by_contra! hz
    apply hne
    apply (Subgroup.map_eq_bot_iff _).mpr
    apply sSup_le
    intro A hA
    exact (Subgroup.map_eq_bot_iff A).mp (hz A hA)
  obtain ⟨A,hA,hn⟩ := hex
  have ha : A.map d.q0 ≤ Model.E := by
    apply map_le_iff_le_comap.mpr
    exact hA.1.trans_eq d.R_eq_comap
  have hb : IsBestOffender Model.rho (A.map d.q0) :=
    (d.canonicalAction.bestOffender_iff _).mp
      (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
        V d.q0 d.q0_onto d.canonicalAction.kernel_centralizer d.R A d.module_le_radical hA hn)
  exact map_mono (le_sSup hA) (Model.best_contains_swap ha hb)

theorem thompson_image_eq_full
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (elementaryAbelianMaxJ d.R).map d.q0 = Model.E := by
  have hnormal : Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 ≤
      normalizer ((elementaryAbelianMaxJ d.R).map d.q0 : Set Model.S) := by
    have hp : d.P.map d.q0 = Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 := by
      rw [d.P_eq_comap,map_comap_eq_self_of_surjective d.q0_onto]
    rw [← hp]
    exact (map_mono d.thompson_normalizes).trans (le_normalizer_map d.q0)
  have hn : (elementaryAbelianMaxJ d.R).map d.q0 ≠ ⊥ := by
    intro hz
    exact hne (hz ▸ bot_le)
  have he := Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal.eq_core
    ((elementaryAbelianMaxJ d.R).map d.q0)
    (by rw [Model.pointCore_eq_exceptional];apply map_le_iff_le_comap.mpr;
        exact (sSup_le fun _ hA => hA.1).trans_eq d.R_eq_comap)
    (Theory.SpecificGroups.SymmetricSix.BinaryFlags.K_le_H1.trans hnormal)
    (d.thompson_image_contains_swap hn) (by
      have he : last = zpowers Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap45 := by
        rw [zpowers_eq_closure]
        congr 1
      rwa [← he])
  exact he.trans Model.pointCore_eq_exceptional

theorem baumann_image_eq_full
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) : d.B.map d.q0 = Model.E := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (inf_le_left.trans_eq d.R_eq_comap)
  · rw [← d.thompson_image_eq_full hne]
    exact map_mono (elementaryAbelianMaxJ_le_baumann d.R)

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
