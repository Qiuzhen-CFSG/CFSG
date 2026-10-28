module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreCenter
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# Plane geometry in the original solvable locals

The normal elementary-nine lift normalizes the original point residual:
its abelian star image centralizes the point image, and two-perfectness
reflects normalization through the whole two-core kernel, which lies in T.
This gives relative normalization by the selected lift, without imposing
point normality in the full point normalizer.

For every original solvable J in H_z, its established cubic point image
has trivial two-core. If O₂(J) fixed V₂, reductions 13.3.14(a,c) would
force that image to have a nontrivial two-core, since the original point
parabolic core moves V. Hence O₂(J) moves V₂. The plane-parabolic core
fixes V₂ and has index two in T, so the two literal cores generate T.
An actor normalizing both L₁ and V₂ preserves V and therefore lies in M.

The final theorem applies these arguments to the original minimal solvable
witness, preserving the supercritical models, exact kernels, point containment
and Heisenberg center marking. The terminal solvable exclusions and the
classification through 14.7.52 remain to be proved.

Source: Aschbacher–Smith, 13.3.14(a,c), printed pp.891–892;
14.5.3(2) and 14.5.20, pp.1013,1019; 14.7.27–29, pp.1054–1055,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal elementary-nine lift containing L₁ normalizes L₁ through the
full two-core kernel. No normality in the whole point normalizer is assumed. -/
theorem local_nine_lift_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    Y.map J.subtype ≤ normalizer (F.Li L 1 : Set G) := by
  let A := (F.Li L 1).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let E := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsMulCommutative (Y.map q) := IsMulCommutative.of_comm fun a b =>
    E.injective (by simp only [map_mul,mul_comm])
  have hp : IsPPerfect 2 A := by
    exact (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.toMonoidHom
      (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkn : q.ker ≤ normalizer (A : Set J) := by
    rw [QuotientGroup.ker_mk']
    apply (pCore_isPGroup.le_sylow_of_normal (T.subtype (F.sylow_le_of_mem_Hz hJ))).trans
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    exact fun _ hx => T_normalizes_L₁ h structural hx
  have hn : Y ≤ normalizer (A : Set J) :=
    (map_le_normalizer_map_iff_of_pPerfect q A Y hp hk hkn).mp
      ((le_centralizer (Y.map q)).trans
        ((centralizer_le (map_mono hAY)).trans (Subgroup.centralizer_le_normalizer _)))
  rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)] at hn
  rintro _ ⟨y,hy,rfl⟩
  exact hn hy

/-- The literal core of every original solvable local moves the flag plane,
using its cubic point image and the earlier natural point-core movement. -/
theorem local_solvable_core_moves_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ¬ J.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  let := h.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (F.le_seed 2)
  let := F.localKernel_tilde_seed_elementary
  have hVJ : V ≤ J := h.chosen.le_sylow.trans (F.sylow_le_of_mem_Hz hJ)
  have hLJ := F.Li_one_le_of_mem_Hz hJ
  have hspan : V = conjugateSpanBy (F.Vi 2) (F.Li L 1) :=
    (F.seed_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))).symm
  have ha := Chapter13.Section03.Noncentrality.reduction_a
    (F.Vi 2) V (F.Li L 1) J ((F.le_seed 2).trans hVJ) hLJ hspan
    (Chapter1.mem_He_iff.mpr
      (F.localKernel_characteristicTwo h.source.simpleQTKE L _ J hJ))
    (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  have hne := Chapter13.Section03.Noncentrality.reduction_c_of_reduction_a
    J (F.Li L 1) V hLJ ha.2 (F.point_core_moves_seed_of_natural h.naturalMarking)
  have he : Chapter13.Section03.Noncentrality.star J (F.Li L 1) hLJ =
      ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) := by
    simp only [Chapter13.Section03.Noncentrality.star,
      Chapter13.Section03.Noncentrality.starMap,MonoidHom.range_comp,inclusion_range]
  rw [he] at hne
  have hp : IsPGroup 3 (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) :=
    IsPGroup.of_card (n := 1)
      (by simpa using (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2)
  apply hne
  exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
    (pCore_isPGroup.disjoint_of_coprime (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)).le_bot)

private theorem local_plane_core_sylow_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ((F.P L).pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  let P := F.P L
  let S := T.subtype (F.binary_sylow_le_P L)
  let e := planeParabolicQuotientEquiv (F := F) h structural
  have hi := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
  rw [SymmetricThreeTwoCore.core_index e,SymmetricThreeTwoCore.sylow_index_three e S] at hi
  have hi2 : (pCore 2 P).relIndex (S : Subgroup P) = 2 := by
    dsimp only [P]
    omega
  have he := relIndex_map_map_of_injective (pCore 2 P) (S : Subgroup P) P.subtype_injective
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L)] at he
  exact he.trans hi2

/-- The core of an original solvable local and the plane-parabolic core
generate the original Sylow subgroup. -/
theorem local_solvable_core_plane_core_generate_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    J.pCoreIn 2 ⊔ (F.P L).pCoreIn 2 = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := J.pCoreIn 2
  let B := (F.P L).pCoreIn 2
  have hAT : A ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype (F.sylow_le_of_mem_Hz hJ))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ))
  have hBT : B ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (F.P L) (T.subtype (F.binary_sylow_le_P L))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.binary_sylow_le_P L))
  have hBC : B ≤ centralizer (F.Vi 2 : Set G) := by
    change (F.P L).pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)
    rw [←(F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action structural) (h.centralizer_LT structural)).1]
    exact inf_le_right
  have hnot : ¬ A ≤ B := fun hh =>
    local_solvable_core_moves_plane h hab structural previous faithful J hJ hs (hh.trans hBC)
  have hi : B.relIndex (T : Subgroup G) = 2 := local_plane_core_sylow_index h structural
  have hjoin := sup_le hAT hBT
  have hd : (A ⊔ B).relIndex (T : Subgroup G) ∣ 2 := by
    have hd := relIndex_dvd_of_le_left (T : Subgroup G) (show B ≤ A ⊔ B from le_sup_right)
    rwa [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact le_antisymm hjoin (relIndex_eq_one.mp h1)
  · have hh := relIndex_mul_relIndex B (A ⊔ B) (T : Subgroup G) le_sup_right hjoin
    rw [hi,h2] at hh
    have h1 : B.relIndex (A ⊔ B) = 1 := by omega
    exact (hnot (le_sup_left.trans (relIndex_eq_one.mp h1))).elim

/-- Preserving the original point residual and plane forces preservation of
the original natural seed, hence containment in its maximal local M. -/
theorem local_point_plane_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (A : Subgroup G) (hn : A ≤ normalizer (F.Li L 1 : Set G))
    (hc : A ≤ normalizer (F.Vi 2 : Set G)) :
    A ≤ normalizer (L : Set G) :=
  point_plane_normalizer_le h structural A hn hc

/-- The original minimal solvable witness has lift normalization and
plane-core generation with both actual models and full kernels retained. -/
theorem local_minimal_solvable_threeCore_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ¬ I.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) ∧
      I.pCoreIn 2 ⊔ (F.P L).pCoreIn 2 = (T : Subgroup G) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      Y.map I.subtype ≤ normalizer (F.Li L 1 : Set G) ∧
      Y.map I.subtype ⊓ normalizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful J hJ hs
  let := hYn
  have hn : Y.map I.subtype ≤ normalizer (F.Li L 1 : Set G) := by
    rcases he with ⟨he,_⟩ | ⟨_,hn,_⟩
    · exact local_nine_lift_normalizes_point h structural I hI Y hAY he.some
    · exact (map_subtype_le Y).trans ((normal_subgroupOf_iff_le_normalizer
        (F.Li_one_le_of_mem_Hz hI)).mp hn)
  exact ⟨I,hIJ,hI,hIs,hmin,
    local_solvable_core_moves_plane h hab structural previous faithful I hI hIs,
    local_solvable_core_plane_core_generate_sylow h hab structural previous faithful I hI hIs,
    X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hn,
    local_point_plane_normalizer_le h structural _ (inf_le_left.trans hn) inf_le_right,he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
