module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# The original involution fusion into the seed core

The same natural-action marking identifies T's image with the binary Borel
and R₁'s image with its point four-group. A nontrivial point-four element
has an actual conjugate in the Borel outside that four-group. Lift its
conjugator through the original action. The full two-group kernel lies in
T, so the conjugate of an original involution again lies in T. Consequently
Ω₁(T) ≤ R₁ forces Ω₁(T) ≤ O₂(LT).

Every rank-indexed elementary Thompson subgroup lies in Ω₁(T). Heredity
inside O₂(LT) makes each such subgroup normal in LT. This retains the
original flag, group action and Sylow; no new involution lift is assumed.

Source: Aschbacher–Smith, 14.7.6, printed p.1045; B.2.3(3), p.75;
refs/quasithin.pdf. LargePrimeSingleFactorSource supplies the application.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section08 ChapterB
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {K : GroupClass.{u}}

/-- Fusion in the original L₃(2) action places the entire first omega in
O₂(LT) as soon as it lies in R₁. No involution-lifting premise is used. -/
theorem omega_le_seed_core_of_le_point_core
    (h : HigherRankHypothesis K T L V 3)
    (structural : Chapter12.Section02.Structural1222 K)
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1) :
    omegaOneAmbient (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [←h.centralizer_LT structural]
  refine le_inf ((omegaOneAmbient_le _).trans le_sup_right) ?_
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro t ht ht2
  obtain ⟨e,q,hq,hk2,ha,hk,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSource.exists_marking h F structural
  let H := L ⊔ (T : Subgroup G)
  let S : Sylow 2 H := T.subtype le_sup_right
  let t₀ : H := ⟨t,mem_sup_right ht⟩
  have htR : t ∈ F.Ri L 1 :=
    hΩ ((omegaOneAmbient_le_iff _ _).mp le_rfl t ht ht2)
  have htimage : q t₀ ∈ Matrix.PSL3Two.MarkedAutomorphisms.pointV :=
    hR ▸ mem_map_of_mem q htR
  by_contra htc
  have hne : q t₀ ≠ 1 := by
    intro hz
    have hh : t₀ ∈ q.ker := hz
    rw [hk] at hh
    exact htc hh
  obtain ⟨g,hgT,hgR⟩ := BinaryLinearThree.ThompsonEscape.cyclic_escape (q t₀) htimage hne
  obtain ⟨x,rfl⟩ := hq g
  let y : H := x * t₀ * x⁻¹
  have hqy : q y = (MulAut.conj (q x)) (q t₀) := by
    simp only [y,map_mul,map_inv,MulAut.conj_apply]
  have hyimage : q y ∈ Matrix.PSL3Two.borelSL :=
    hqy.symm ▸ hgT (mem_map_of_mem _ (mem_zpowers (q t₀)))
  have hyS : y ∈ ((T : Subgroup G).subgroupOf H) := by
    have hh : y ∈ (((T : Subgroup G).subgroupOf H).map q).comap q := hT.symm ▸ hyimage
    have hkerS : q.ker ≤ (T : Subgroup G).subgroupOf H := hk2.le_sylow_of_normal S
    rw [comap_map_eq,sup_eq_left.mpr hkerS] at hh
    exact hh
  have hy2 : (y : G) ^ 2 = 1 := by
    change ((x : G) * t * (x : G)⁻¹) ^ 2 = 1
    rw [conj_pow,ht2]
    simp
  have hyR : (y : G) ∈ F.Ri L 1 :=
    hΩ ((omegaOneAmbient_le_iff (T : Subgroup G)
      (omegaOneAmbient (T : Subgroup G))).mp le_rfl (y : G) hyS hy2)
  apply hgR
  rw [MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  change (MulAut.conj (q x)) (q t₀) ∈ Matrix.PSL3Two.MarkedAutomorphisms.pointV
  rw [←hqy]
  exact hR ▸ mem_map_of_mem q hyR

/-- Every rank-indexed elementary Thompson subgroup is inherited by the
original seed core and is consequently normalized by LT. -/
theorem thompson_normalized_of_omega_le_point_core
    (h : HigherRankHypothesis K T L V 3)
    (structural : Chapter12.Section02.Structural1222 K)
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1)
    (i : ℕ) (hi : i < twoRank (T : Subgroup G)) :
    thompsonJ (T : Subgroup G) i = thompsonJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) i ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (thompsonJ (T : Subgroup G) i : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hJΩ : thompsonJ (T : Subgroup G) i ≤ omegaOneAmbient (T : Subgroup G) := by
    apply sSup_le
    intro A hA
    let := hA.2.1
    rw [←omegaOneAmbient_eq_self A]
    exact omegaOneAmbient_mono hA.1
  have hJQ := hJΩ.trans (omega_le_seed_core_of_le_point_core h structural hΩ)
  have hQT : Q ≤ T := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  have he := lemma_B_2_3_3 (T : Subgroup G) Q hi hJQ hQT
  refine ⟨he,?_⟩
  rw [he]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (thompsonJ Q i).map (MulAut.conj g).toMonoidHom = thompsonJ Q i
  rw [←thompsonJ_map_equiv]
  congr 1
  apply mem_normalizer_iff_map_conj_eq.mp
  exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hg

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
