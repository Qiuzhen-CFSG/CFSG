module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The omega-center line controlling the moved-plane centralizer

A nonidentity element of Ω₁Z(T) centralizing L has full centralizer in
M=N_G(L), by the genuine unique maximal two-local overgroup of LT. For a
nontrivial elementary T-normal subgroup U≤T, the p-group fixed-point theorem
gives a nonidentity v in U∩Ω₁Z(T). When C_{Ω₁Z(T)}(L) has index two,
either v or vz belongs to this fixed subgroup. The escape z∉U ensures
that the chosen element remains nonidentity.

Consequently C_G(z)∩C_G(U)≤M. The actual moved-plane application is in
NormalizerProduct; the earlier index and Chapter12 uniqueness inputs retain
final discharge with qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.3(2) and 13.4.8, printed pp.897 and905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem omega_fixed_generator_centralizer_le_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    {d : G} (hd : d ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hdL : d ∈ centralizer (L : Set G)) (hd1 : d ≠ 1) :
    centralizer ({d} : Set G) ≤ normalizer (L : Set G) := by
  have hdT := (mem_omegaOneCenterAmbient_iff _ _).mp hd
  have hP : zpowers d ≤ (T : Subgroup G) := zpowers_le.mpr hdT.1
  have hn : normalizer (zpowers d : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal
      (h.source_normalizer_maximal_unique structural
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
      (T.isPGroup'.to_le hP) (zpowers_ne_bot.mpr hd1)
    apply le_trans ?_ (centralizer_le_normalizer (zpowers d : Set G))
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    intro a ha
    have hsub : L ⊔ (T : Subgroup G) ≤ centralizer ({d} : Set G) := by
      apply sup_le
      · intro l hl
        exact mem_centralizer_singleton_iff.mpr (hdL l hl)
      · intro t ht
        exact mem_centralizer_singleton_iff.mpr (hdT.2.2 t ht)
    exact mem_centralizer_singleton_iff.mp (hsub ha)
  have hc : centralizer ({d} : Set G) = centralizer (zpowers d : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  rw [hc]
  exact (centralizer_le_normalizer (zpowers d : Set G)).trans hn

theorem centralizer_plane_le_normalizer_of_omega_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUT : U ≤ T) (hnU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU : U ≠ ⊥)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z ∉ centralizer (L : Set G)) (hzU : z ∉ U)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    centralizer ({z} : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  let A := U.subgroupOf (T : Subgroup G)
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hUT).mpr hnU
  have hA : A ≠ ⊥ := by
    intro hb
    have hh := congrArg (fun B : Subgroup T => B.map (T : Subgroup G).subtype) hb
    rw [map_subgroupOf_eq_of_le hUT,Subgroup.map_bot] at hh
    exact hU hh
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr hA
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨a,ha1,hac⟩ := exists_nontrivial_center_mem_normal (p := 2) A
  let v : G := a.val.val
  have hvU : v ∈ U := a.property
  have hv1 : v ≠ 1 := fun he => ha1 (Subtype.ext (Subtype.ext he))
  have hvZ : v ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hUT hvU,elemPow_eq_one_of_isElementaryAbelian v hvU,?_⟩
    intro t ht
    exact congrArg Subtype.val ((mem_center_iff.mp hac) ⟨t,ht⟩)
  have hchoose : ∃ w : G, w ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      w ∈ centralizer (L : Set G) ∧ w ≠ 1 ∧
      centralizer ({z} : Set G) ⊓ centralizer (U : Set G) ≤ centralizer ({w} : Set G) := by
    by_cases hvL : v ∈ centralizer (L : Set G)
    · refine ⟨v,hvZ,hvL,hv1,?_⟩
      intro c hc
      exact mem_centralizer_singleton_iff.mpr (hc.2 v hvU).symm
    · have hmul : v * z ∈ centralizer (L : Set G) := by
        let Z := omegaOneCenterAmbient (T : Subgroup G)
        let K := (Z ⊓ centralizer (L : Set G)).subgroupOf Z
        have hi : K.index = 2 := hindex
        have hvK : (⟨v,hvZ⟩ : Z) ∉ K := fun hv => hvL hv.2
        have hzK : (⟨z,hz⟩ : Z) ∉ K := fun hz => hzL hz.2
        exact ((mul_mem_iff_of_index_two hi (a := (⟨v,hvZ⟩ : Z)) (b := ⟨z,hz⟩)).mpr
          (by simp only [hvK,hzK])).2
      refine ⟨v*z,(omegaOneCenterAmbient _).mul_mem hvZ hz,hmul,?_,?_⟩
      · intro he
        have he' : z = v⁻¹ := eq_inv_of_mul_eq_one_right he
        exact hzU (he' ▸ U.inv_mem hvU)
      · intro c hc
        apply mem_centralizer_singleton_iff.mpr
        exact ((show Commute c v from (hc.2 v hvU).symm).mul_right
          (mem_centralizer_singleton_iff.mp hc.1)).eq
  obtain ⟨w,hwZ,hwL,hw1,hw⟩ := hchoose
  exact hw.trans (omega_fixed_generator_centralizer_le_normalizer h structural hwZ hwL hw1)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
