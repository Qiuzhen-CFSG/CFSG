module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OmegaLine

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The omega-center line controlling the moved-plane centralizer: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/OmegaLine` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_plane_le_normalizer_of_omega_index_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  exact hw.trans (LocalGeometry.omega_fixed_generator_centralizer_le_normalizer_at h structural hwZ hwL hw1)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
