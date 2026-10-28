module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Line
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Local
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry

/-!
# The exact stabilizer of the actual V₂ line

The original component conjugation action is faithful on U_L = [U_I,L].
Its subspace planeSpace is the original V₂, with no change of carrier.
The preimage of its setwise stabilizer is its ambient normalizer. The
second choice of 15.3.10 gives N_G(V₂) ≤ M; the earlier commutator
identities give M_I-invariance. Thus the stabilizer in L* is exactly M_L*.
No constituent selection or model recognition is assumed or proved here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(3), pp.1123–1124, and proof of 15.3.31, p.1132 (PDF p.1149).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open EightGeometry EightGeometry.NaturalModule EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hf : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]

theorem plane_stabilizer_comap (hline : LineData d I) (hYL : d.Yplus ≤ c.L) :
    (subspaceStabilizer (componentAction d c hn hI hf P hP) (planeSpace d c)).comap
      (d.starMap I) = (normalizer (d.V₂ : Set G)).subgroupOf I := by
  let U := (d.componentModule I c.L).subgroupOf I
  let _ : U.Normal := normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  have hVU : d.V₂.subgroupOf I ≤ U := comap_mono (hline.plane_le_component d c hYL)
  have he := Representation.NormalElementaryQuotient.stabilizer_comap U
    (d.starMap I) (QuotientGroup.mk'_surjective _)
    (component_centralizer_eq_star_kernel d c hn hI hf P hP).symm
    ((d.V₂.subgroupOf I).subgroupOf U)
  rw [map_subgroupOf_eq_of_le hVU] at he
  change (subspaceStabilizer (componentAction d c hn hI hf P hP)
    (planeSpace d c)).comap (d.starMap I) = _ at he
  rw [he]
  exact (subgroupOf_normalizer_eq ((hline.plane_le_component d c hYL).trans
    ((componentModule_le_span d c).trans (span_le d (hI ▸ le_sup_right))))).symm

theorem plane_stabilizer_eq (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hN : normalizer (d.V₂ : Set G) ≤ d.M) :
    subspaceStabilizer ((componentAction d c hn hI hf P hP).comp
      (d.starImage I c.L).subtype) (planeSpace d c) =
        (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) := by
  ext l
  obtain ⟨i, hi, he⟩ := l.property
  have hstab : (l : d.Star I) ∈ subspaceStabilizer
      (componentAction d c hn hI hf P hP) (planeSpace d c) ↔
        (i : G) ∈ normalizer (d.V₂ : Set G) := by
    rw [← he]
    change i ∈ (subspaceStabilizer _ _).comap (d.starMap I) ↔ _
    rw [plane_stabilizer_comap d c hn hI hf P hP hline hYL]
    rfl
  constructor
  · intro hl
    exact ⟨i, ⟨hN (hstab.mp hl), hi⟩, he⟩
  · rintro ⟨j, hj, hjl⟩
    change (l : d.Star I) ∈ subspaceStabilizer
      (componentAction d c hn hI hf P hP) (planeSpace d c)
    change d.starMap I j = (l : d.Star I) at hjl
    rw [← hjl]
    have hjN := hline.plane_normalized d (show (j : G) ∈ d.MI I from
      ⟨hj.1, j.property⟩)
    have hm : j ∈ (subspaceStabilizer
        (componentAction d c hn hI hf P hP) (planeSpace d c)).comap (d.starMap I) := by
      rw [plane_stabilizer_comap d c hn hI hf P hP hline hYL]
      exact hjN
    exact hm

theorem plane_stabilizer_eq_of_rank_one (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y) :
    subspaceStabilizer ((componentAction d c hn hI hf P hP).comp
      (d.starImage I c.L).subtype) (planeSpace d c) =
        (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) :=
  plane_stabilizer_eq d c hn hI hf P hP hline hYL
    (OutsideStructure.LocalBranches.second_choice_plane_normalizers d
      (rank_one_choice d hRank hYRank)).2

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
