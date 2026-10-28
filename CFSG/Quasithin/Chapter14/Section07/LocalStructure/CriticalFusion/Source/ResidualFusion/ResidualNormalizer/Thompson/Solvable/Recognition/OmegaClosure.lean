module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Intermediate
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.PrimeRankZero

/-!
# The genuine omega-center closure in the residual Thompson argument

For A = J(DR₁)R₁, the original point lies in Ω₁(Z(R₁)). Its centralizer
in DR₁ is a two-group: its intersection with D lies in D ∩ H ≤ T and
its quotient by that intersection is a two-group. Consequently the full
R₁-omega-center closure in A has centralizer O₂(A).

If the first B.2.16 alternative held, the normal two-core would contain
J(R₁), hence every conjugate maximum elementary subgroup, hence J(A).
The already established J(A) = J(DR₁) and non-two-group conclusion rule
this out. The exceptional family is therefore nonempty and gives positive
three-rank. The universal B.2.16 remains the explicit earlier-source input
owned by qt-b-02. We do not identify this closure with the original E or
identify the old and new cores.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071; B.2.16, printed p.79.
-/

@[expose] public section
noncomputable section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem globalJ_le_normal_of_sylow {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (N : Subgroup A) [N.Normal]
    (hSN : elementaryAbelianMaxJ (S : Subgroup A) ≤ N) :
    elementaryAbelianMaxJ (⊤ : Subgroup A) ≤ N := by
  apply sSup_le
  intro B hB
  obtain ⟨P, hBP⟩ := hB.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A P S
  let e := MulAut.conj g
  have hPS : (P : Subgroup A).map e.toMonoidHom = (S : Subgroup A) := by
    change ((g • P : Sylow 2 A) : Subgroup A) = (S : Subgroup A)
    rw [hg]
  have hBS : B.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups (S : Subgroup A) := by
    refine ⟨(map_mono hBP).trans_eq hPS, hB.2.1.map e.toMonoidHom, ?_⟩
    intro C _ hC
    rw [card_map_of_injective e.injective]
    exact hB.2.2 C le_top hC
  intro b hb
  have hm := hSN ((le_sSup hBS) (mem_map_of_mem e.toMonoidHom hb))
  have hh := (inferInstance : N.Normal).conj_mem (e b) hm g⁻¹
  simpa [e, MulAut.conj_apply, mul_assoc] using hh

namespace Data
variable (d : Data T L V F W)
include d

/-- The centralizer of the original point in DR₁ is a two-group. -/
theorem residual_pointCentralizer_isPGroup :
    IsPGroup 2 (Y L F ⊓ centralizer (F.Vi 1 : Set G) : Subgroup G) := by
  let A := Y L F
  let N := (D F).subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (D F).le_normalizer residual_R_normalizes_D)
  have hgen : N ⊔ (F.Ri L 1).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D F ≤ A from le_sup_left),
      map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ A from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hp := isPGroup_quotient_of_sup_eq_top N _
    (T.isPGroup'.to_le residual_R_le_sylow).comap_subtype hgen
  have hcH : centralizer (F.Vi 1 : Set G) ≤ F.H := by
    rw [d.centralizer_eq]
    apply centralizer_le
    apply Set.singleton_subset_iff.mpr
    rw [d.point]
    exact mem_zpowers d.z
  intro c
  let x : A := ⟨c, c.property.1⟩
  obtain ⟨n, hn⟩ := hp (QuotientGroup.mk' N x)
  have hxD : (c : G) ^ 2 ^ n ∈ D F := by
    have hh : x ^ 2 ^ n ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (x ^ 2 ^ n) = 1
      rwa [map_pow]
    exact hh
  have hxT := d.D_inf_H_le_sylow
    ⟨hxD, hcH ((centralizer (F.Vi 1 : Set G)).pow_mem c.property.2 _)⟩
  obtain ⟨m, hm⟩ := T.isPGroup' ⟨_, hxT⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  change (c : G) ^ 2 ^ (n + m) = 1
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

/-- The original point is contained in the full Sylow omega-center. -/
theorem residual_point_le_thompsonOmega
    (S : Sylow 2 (JR L F)) (hS : (S : Subgroup (JR L F)).map (JR L F).subtype = F.Ri L 1) :
    (F.Vi 1).subgroupOf (JR L F) ≤ omegaOneCenterAmbient (S : Subgroup (JR L F)) := by
  let := d.U_elementary
  let : IsElementaryAbelian 2 (F.Vi 1) :=
    IsElementaryAbelian.of_le d.conjugationSection.kernel_le
  intro z hz
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (mem_map_iff_mem (JR L F).subtype_injective).mp
    rw [hS]
    exact d.residual_point_le_R hz
  · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z.val hz)
  · intro r hr
    apply Subtype.ext
    exact mem_centralizer_iff.mp (d.H_centralizes_point
      (residual_R_le_H (hS ▸ mem_map_of_mem (JR L F).subtype hr))) z hz |>.symm

/-- The JR₁-span of the original point is contained in the full omega-center
closure. This is a containment, not an identification with the larger D-span E. -/
theorem residual_pointSpan_le_thompsonClosure
    (S : Sylow 2 (JR L F)) (hS : (S : Subgroup (JR L F)).map (JR L F).subtype = F.Ri L 1) :
    normalClosure ((F.Vi 1).subgroupOf (JR L F) : Set (JR L F)) ≤
      Chapter1.RadicalNormalizers.ThompsonSource.closure S :=
  normalClosure_mono (d.residual_point_le_thompsonOmega S hS)

/-- The original E is JR₁-invariant and contains the point, hence contains its
JR₁-span. No reverse inclusion is asserted. -/
theorem residual_pointSpan_le_E :
    normalClosure ((F.Vi 1).subgroupOf (JR L F) : Set (JR L F)) ≤
      (E F).subgroupOf (JR L F) := by
  let : ((E F).subgroupOf (JR L F)).Normal :=
    normal_subgroupOf_of_le_normalizer d.residual_thompsonJoin_normalizes_E
  exact normalClosure_le_normal (comap_mono point_le_E)

/-- The full omega-center closure has the new intrinsic two-core as centralizer. -/
theorem residual_thompsonOmega_centralizer
    (S : Sylow 2 (JR L F)) (hS : (S : Subgroup (JR L F)).map (JR L F).subtype = F.Ri L 1) :
    centralizer (Chapter1.RadicalNormalizers.ThompsonSource.closure S : Set (JR L F)) =
      pCore 2 (JR L F) := by
  apply centralizer_normalClosure_eq_pCore_of_isPGroup
  · have hp := d.residual_pointCentralizer_isPGroup
    let C := centralizer (omegaOneCenterAmbient (S : Subgroup (JR L F)) : Set (JR L F))
    have hmap : C.map (JR L F).subtype ≤ Y L F ⊓ centralizer (F.Vi 1 : Set G) := by
      rintro x ⟨a, ha, rfl⟩
      refine ⟨JR_le_Y a.property, ?_⟩
      intro z hz
      exact congrArg Subtype.val (ha
        ⟨z, (d.residual_point_le_R.trans le_sup_right) hz⟩
        (d.residual_point_le_thompsonOmega S hS hz))
    exact (hp.to_le hmap).of_equiv
      (C.equivMapOfInjective (JR L F).subtype (JR L F).subtype_injective).symm
  · apply (pCore_isPGroup.le_sylow_of_normal S).trans
    intro s hs z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 s hs |>.symm

/-- The actual B.2.16 application is exceptional, with no assumed factor count. -/
theorem residual_thompsonJoin_exceptional
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hsol : Group.IsSolvable (J L F))
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    (S : Sylow 2 (JR L F)) (hS : (S : Subgroup (JR L F)).map (JR L F).subtype = F.Ri L 1) :
    let h := hB (JR L F) (residual_thompsonJoin_solvable hsol)
      (d.residual_thompsonJoin_generalizedFitting hSylow) S
    letI := h.elementary
    Nonempty (Chapter1.RadicalNormalizers.ThompsonSource.Exceptional S) := by
  dsimp only
  have hc := hB (JR L F) (residual_thompsonJoin_solvable hsol)
    (d.residual_thompsonJoin_generalizedFitting hSylow) S
  let := hc.elementary
  rcases hc.alternatives with hfactor | hex
  · exfalso
    have hJQ := hfactor.1
    rw [d.residual_thompsonOmega_centralizer S hS] at hJQ
    have hall := globalJ_le_normal_of_sylow S (pCore 2 (JR L F)) hJQ
    have hm := map_mono (f := (JR L F).subtype) hall
    rw [← elementaryAbelianMaxJ_map_injective _ (JR L F).subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype, JR_thompson_eq_J] at hm
    exact d.residual_thompson_not_isPGroup hDM hSylow hBaum hD
      ((isPGroup_pCoreIn 2 (JR L F)).to_le hm)
  · exact hex

/-- An actual PSL₂(2) section forces positive three-rank. -/
theorem residual_thompsonJoin_three_rank_pos
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hsol : Group.IsSolvable (J L F))
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) : 0 < primeRank 3 (JR L F) := by
  obtain ⟨S, hS⟩ := residual_thompsonJoin_sylow hSylow
  have hc := hB (JR L F) (residual_thompsonJoin_solvable hsol)
    (d.residual_thompsonJoin_generalizedFitting hSylow) S
  let := hc.elementary
  obtain ⟨ex⟩ := d.residual_thompsonJoin_exceptional hB hsol hDM hSylow hBaum hD S hS
  have hd := ex.three_dvd_card
  have hn : primeRank 3 (JR L F) ≠ 0 := fun h =>
    PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  omega

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
