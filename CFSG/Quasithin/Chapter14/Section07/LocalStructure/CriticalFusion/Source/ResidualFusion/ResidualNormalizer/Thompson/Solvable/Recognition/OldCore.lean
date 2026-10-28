module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Recognition.Quotients
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original core in the solvable Thompson endgame

The source local bounds actually give J(Y)R₁ = Y, where Y = DR₁. Write
α = Ω₁(Z(J(R₁))). The original point lies in α and has a two-group
centralizer in Y. Consequently C_Y(α) is a two-group normalized by R₁,
so Sylow maximality identifies it with Baum(R₁). The supplied bounds
N_G(Baum(R₁)) ≤ N_G(L) and D ∩ N_G(L) ≤ T make N_Y(Baum(R₁)) a
two-group as well, hence equal to R₁.

Now R₁ ∩ J(Y) is Sylow in the normal subgroup J(Y). Thompson heredity
identifies its elementary Thompson subgroup with J(R₁), so its normalizer
in Y lies in N_Y(Baum(R₁)) = R₁. Frattini gives Y = J(Y)R₁. The old
core centralizer equality therefore proves that the new core centralizes
the entire original D-span E. We retain the literal subgroupOf maps in
the intrinsic centralization and core-comparison statements.

This argument uses neither restriction of reducedness to an arbitrary
Sylow overgroup nor an identification of E with the smaller JR₁ point
span. Solvability, three-rank and B.2.16 are unnecessary for this comparison;
the separate quotient recognition still uses its earlier-source inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071, and Thompson heredity B.2.3(3), p.75.
-/

@[expose] public section
noncomputable section

open Subgroup Stellmacher

private theorem normalizer_maxJ (H : Type*) [Group H] (Q : Subgroup H) :
    normalizer (Q : Set H) ≤ normalizer (elementaryAbelianMaxJ Q : Set H) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change Q.map (MulAut.conj x).toMonoidHom = Q at hx
  change (elementaryAbelianMaxJ Q).map (MulAut.conj x).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x) Q, hx]

private theorem normalizer_alpha (H : Type*) [Group H] (Q : Subgroup H) :
    normalizer (Q : Set H) ≤ normalizer (omegaOneCenterAmbient Q : Set H) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change Q.map (MulAut.conj x).toMonoidHom = Q at hx
  change (omegaOneCenterAmbient Q).map (MulAut.conj x).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective, hx]

private theorem normalizer_maxJ_le_normalizer_baumann
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hc : IsPGroup 2 (centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H))) :
    normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) ≤
      normalizer (CFSG.Quasithin.ChapterB.baumann (S : Subgroup H) : Set H) := by
  let C := centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)
  have hn : normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) ≤
      normalizer (C : Set H) :=
    (normalizer_alpha H _).trans (normalizer_le_normalizer_centralizer _)
  have hSC : (S : Subgroup H) ≤ normalizer (C : Set H) :=
    S.toSubgroup.le_normalizer.trans ((normalizer_maxJ H _).trans hn)
  have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hc hSC) le_sup_left
  have hCS : C ≤ (S : Subgroup H) := he ▸ (le_sup_right : C ≤ (S : Subgroup H) ⊔ C)
  change normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) ≤
    normalizer (((S : Subgroup H) ⊓ C : Subgroup H) : Set H)
  rw [inf_eq_right.mpr hCS]
  exact hn

private theorem thompson_frattini
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (N : Subgroup H) [N.Normal] (hJN : elementaryAbelianMaxJ (S : Subgroup H) ≤ N)
    (hN : normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) ≤ S) :
    N ⊔ (S : Subgroup H) = ⊤ := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let R := (P : Subgroup N).map N.subtype
  have hR : R = (S : Subgroup H) ⊓ N := by
    rw [show R = (P : Subgroup N).map N.subtype from rfl, hP, subgroupOf_map_subtype]
  have hRS : R ≤ (S : Subgroup H) := hR ▸ inf_le_left
  have hJR : elementaryAbelianMaxJ (S : Subgroup H) ≤ R := by
    rw [hR]
    exact le_inf (sSup_le fun _ hA => hA.1) hJN
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq R (S : Subgroup H) hRS
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le (S : Subgroup H) R hJR
  have hj : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (S : Subgroup H) :=
    le_antisymm (hs.2 (le_antisymm hs.1 hl.1)) (hl.2 (le_antisymm hl.1 hs.1))
  have hnorm : normalizer (R : Set H) ≤ (S : Subgroup H) := by
    apply (normalizer_maxJ H R).trans
    rw [hj]
    exact hN
  have hgen : normalizer (R : Set H) ⊔ N = ⊤ := P.normalizer_sup_eq_top
  apply top_unique
  rw [← hgen]
  exact sup_le (hnorm.trans le_sup_right) le_sup_left

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

omit [Finite G] in
private theorem oldCore_baumannNormalizer_twoGroup
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 (Y L F ⊓ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) : Subgroup G) := by
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
  intro c
  let x : A := ⟨c, c.property.1⟩
  obtain ⟨n, hn⟩ := hp (QuotientGroup.mk' N x)
  have hxD : (c : G) ^ 2 ^ n ∈ D F := by
    have hh : x ^ 2 ^ n ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (x ^ 2 ^ n) = 1
      rwa [map_pow]
    exact hh
  have hxT := hDM ⟨hxD, hBaum ((normalizer
    (ChapterB.baumann (F.Ri L 1) : Set G)).pow_mem c.property.2 _)⟩
  obtain ⟨m, hm⟩ := T.isPGroup' ⟨_, hxT⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  change (c : G) ^ 2 ^ (n + m) = 1
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

include d

/-- The source point-centralizer and Baumann bounds force the Thompson
Sylow overgroup to be the whole original Y = DR₁. -/
theorem residual_thompsonJoin_eq_Y
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)) :
    JR L F = Y L F := by
  obtain ⟨S, hS⟩ := hSylow
  let A := Y L F
  let N := (J L F).subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer Y_normalizes_J
  let Z := (F.Vi 1).subgroupOf A
  have hZ : Z ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup A)) := by
    let := d.U_elementary
    let : IsElementaryAbelian 2 (F.Vi 1) :=
      IsElementaryAbelian.of_le d.conjugationSection.kernel_le
    let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf
      (d.residual_point_le_R.trans le_sup_right)
    apply elementary_centralizer_maxJ_le_omegaCenter (S : Subgroup A) Z
    · intro z hz
      apply (mem_map_iff_mem A.subtype_injective).mp
      rw [hS]
      exact d.residual_point_le_R hz
    · intro z hz j hj
      apply Subtype.ext
      have hJS : elementaryAbelianMaxJ (S : Subgroup A) ≤ (S : Subgroup A) :=
        sSup_le fun _ hB => hB.1
      have hjS : j ∈ (S : Subgroup A) := hJS hj
      have hjR : (j : G) ∈ F.Ri L 1 := hS ▸ mem_map_of_mem A.subtype hjS
      exact (d.H_centralizes_point (residual_R_le_H hjR) z hz).symm
  have hc : IsPGroup 2 (centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup A)) : Set A)) := by
    let C := centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup A)) : Set A)
    have hmap : C.map A.subtype ≤ Y L F ⊓ centralizer (F.Vi 1 : Set G) := by
      rintro x ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      intro z hz
      exact congrArg Subtype.val (ha
        ⟨z, (d.residual_point_le_R.trans le_sup_right) hz⟩ (hZ hz))
    exact (d.residual_pointCentralizer_isPGroup.to_le hmap).of_equiv
      (C.equivMapOfInjective A.subtype A.subtype_injective).symm
  have hb : (ChapterB.baumann (S : Subgroup A)).map A.subtype =
      ChapterB.baumann (F.Ri L 1) := by
    change ((S : Subgroup A) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup A)) : Set A)).map A.subtype = _
    rw [baumann_map_injective A.subtype A.subtype_injective, hS]
    rfl
  have hn : normalizer (ChapterB.baumann (S : Subgroup A) : Set A) ≤ (S : Subgroup A) := by
    let B := normalizer (ChapterB.baumann (S : Subgroup A) : Set A)
    have hm : B.map A.subtype ≤
        Y L F ⊓ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) := by
      apply le_inf (map_subtype_le _)
      have he := le_normalizer_map (H := ChapterB.baumann (S : Subgroup A)) A.subtype
      rwa [hb] at he
    have hp : IsPGroup 2 B :=
      ((oldCore_baumannNormalizer_twoGroup hDM hBaum).to_le hm).of_equiv
        (B.equivMapOfInjective A.subtype A.subtype_injective).symm
    have hSB : (S : Subgroup A) ≤ B :=
      S.toSubgroup.le_normalizer.trans (normalizer_le_normalizer_baumann _)
    exact (S.is_maximal' hp hSB).le
  have hJN : elementaryAbelianMaxJ (S : Subgroup A) ≤ N := by
    intro x hx
    have hh := mem_map_of_mem A.subtype hx
    rw [← elementaryAbelianMaxJ_map_injective _ A.subtype_injective, hS] at hh
    exact residual_sylowThompson_le_J ⟨S, hS⟩ hh
  have he := thompson_frattini S N hJN
    ((normalizer_maxJ_le_normalizer_baumann S hc).trans hn)
  have hm := congrArg (Subgroup.map A.subtype) he
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le J_le_Y, hS,
    ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- The new core centralizes the full original D-span, in the ambient group. -/
theorem residual_thompsonJoin_core_centralizes_E
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)) :
    (JR L F).pCoreIn 2 ≤ centralizer (E F : Set G) := by
  rw [d.residual_thompsonJoin_eq_Y hDM hSylow hBaum]
  exact (d.residualSpan_centralizer_eq_core hSylow).ge.trans inf_le_right

/-- Intrinsic centralization with the literal E.subgroupOf(JR₁). -/
theorem residual_thompsonJoin_intrinsic_core_centralizes_E
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)) :
    pCore 2 (JR L F) ≤ centralizer ((E F).subgroupOf (JR L F) : Set (JR L F)) := by
  intro x hx z hz
  apply Subtype.ext
  exact d.residual_thompsonJoin_core_centralizes_E hDM hSylow hBaum
    (mem_map_of_mem (JR L F).subtype hx) z hz

/-- Compare the two cores using the established C_JR₁(E) = O₂(Y).
This discharges the old-core comparison needed by the JRQuotient assembly. -/
theorem residual_thompsonJoin_coreInJR_eq
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)) :
    coreInJR L F = pCore 2 (JR L F) := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, (isPGroup_pCoreIn 2 (Y L F)).comap_subtype⟩
  · intro x hx
    apply (d.residual_thompsonJoin_centralizer hSylow).le
    exact ⟨x.property, d.residual_thompsonJoin_core_centralizes_E hDM hSylow hBaum
      (mem_map_of_mem (JR L F).subtype hx)⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
