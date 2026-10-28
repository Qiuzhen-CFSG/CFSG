module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalCubicShape
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.PCoreRestriction

/-!
# Containment of the original cubic chief actor in the Thompson product

The intersection of the selected chief actor K with a T-invariant subgroup
containing O₂(K) is either a two-group or all of K. Apply this to the actual elementary
Thompson subgroup of KR₁ together with O₂(KR₁). The first alternative
would make that entire normal subgroup a two-group, forcing the Thompson
subgroup of R₁ to centralize R₂(KR₁), contrary to the proved Baumann
movement step. Thus K lies in the literal Thompson product modulo O₂(KR₁).

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ M H : Subgroup G}

theorem source_primitive_three_chief_invariant_dichotomy
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H)
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hchief : ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥)
    (hE : IsElementaryAbelian 3 (J ⧸ pCore 2 J))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9)
    (Y : Subgroup G) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hQY : (J.map H.subtype).pCoreIn 2 ≤ Y) :
    IsPGroup 2 (J.map H.subtype ⊓ Y : Subgroup G) ∨ J.map H.subtype ≤ Y := by
  let K := J.map H.subtype
  let D := (K ⊓ Y).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hDJ : D ≤ J := by
    intro x hx
    have hh : x ∈ K.subgroupOf H := hx.1
    change x ∈ (J.map H.subtype).comap H.subtype at hh
    rwa [comap_map_eq_self_of_injective H.subtype_injective J] at hh
  have hTD : (T.subtype hTH : Subgroup H) ≤ normalizer (D : Set H) := by
    have hn : (T : Subgroup G) ≤ normalizer (K ⊓ Y : Set G) :=
      (le_inf (hTH.trans hJn) hTY).trans inf_normalizer_le_normalizer_inf
    exact (comap_mono hn).trans ((K ⊓ Y).le_normalizer_comap H.subtype)
  have hSD : (S : Subgroup (H ⧸ pCore 2 H)) ≤ normalizer (D.map q : Set _) :=
    (map_mono hTD).trans (D.le_normalizer_map q)
  rcases source_primitive_three_chief_sylow_irreducible h J hJn hchief hE hcard
    (D.map q) (map_mono hDJ) hSD with hz | he
  · left
    have hDcore : D ≤ pCore 2 H := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hz
    apply (isPGroup_pCoreIn 2 H).to_le
    intro x hx
    have hxH : x ∈ H := (map_subtype_le J) hx.1
    exact ⟨⟨x,hxH⟩,hDcore hx,rfl⟩
  · right
    rintro x ⟨j,hj,rfl⟩
    have hjq : q j ∈ D.map q := he ▸ mem_map_of_mem q hj
    obtain ⟨z,hz,hzj⟩ := hjq
    have hd : z⁻¹ * j ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (z⁻¹ * j) = 1
      rw [map_mul,map_inv,hzj,inv_mul_cancel]
    have hjK : (j : G) ∈ K := mem_map_of_mem H.subtype hj
    have hdK : (z : G)⁻¹ * (j : G) ∈ K := K.mul_mem (K.inv_mem hz.1) hjK
    have hdY : (z : G)⁻¹ * (j : G) ∈ Y := hQY
      (inf_pCoreIn_le_of_le 2 (map_subtype_le J) ⟨hdK,⟨z⁻¹*j,hd,rfl⟩⟩)
    have hmul := Y.mul_mem hz.2 hdY
    change (z : G) * ((z : G)⁻¹ * (j : G)) ∈ Y at hmul
    change (j : G) ∈ Y
    simpa only [mul_inv_cancel_left] using hmul

/-- The selected cubic chief actor is contained in the literal Thompson product
modulo the two-core of KR1. -/
theorem source_primitive_three_chief_le_thompson_sup_core
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hchief : ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥)
    (hE : IsElementaryAbelian 3 (J ⧸ pCore 2 J))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9)
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let X := J.map H.subtype ⊔ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    J.map H.subtype ≤ (elementaryAbelianMaxJ (⊤ : Subgroup X)).map X.subtype ⊔
      X.pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let Y := elementaryAbelianMaxJ X ⊔ X.pCoreIn 2
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F)))
    ((pCoreIn_le 2 _).trans h.local_le)
  have hYX : Y ≤ X := sup_le (sSup_le fun _ hA => hA.1) (pCoreIn_le 2 X)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (show (T : Subgroup G) ≤ P from le_sup_right).trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (le_inf (hTH.trans hJn) hTR).trans (normalizer_inf_normalizer_le_normalizer_sup K R)
  have hNY : normalizer (X : Set G) ≤ normalizer (Y : Set G) :=
    (le_inf (normalizer_le_normalizer_elementaryAbelianMaxJ X)
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQY : K.pCoreIn 2 ≤ Y :=
    (pCoreIn_mono_of_normalizes (show K ≤ X from le_sup_left) (hXH.trans hJn)).trans
      le_sup_right
  have ho : Odd (Nat.card (J ⧸ pCore 2 J)) := by
    rcases hcard with hc | hc <;> rw [hc] <;> decide
  obtain ⟨S,hS⟩ := source_primitive_odd_sylow h J hJC hJn ho
  let KX := K.subgroupOf X
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  have hgen : KX ⊔ (S : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left), hS,
      ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (X ⧸ KX) := isPGroup_quotient_of_sup_eq_top KX S S.isPGroup' hgen
  have hJmap : (elementaryAbelianMaxJ (⊤ : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ X := by
    rw [← elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
  change K ≤ (elementaryAbelianMaxJ (⊤ : Subgroup X)).map X.subtype ⊔ X.pCoreIn 2
  rw [hJmap]
  rcases source_primitive_three_chief_invariant_dichotomy h J hJn hchief hE hcard Y
    (hTX.trans hNY) hQY with htwo | hle
  · have hYtwo : IsPGroup 2 Y := by
      let f : Y →* X ⧸ KX := (QuotientGroup.mk' KX).comp (inclusion hYX)
      have hk : IsPGroup 2 f.ker := by
        apply htwo.comap_subtype.to_le
        intro y hy
        have hyK : inclusion hYX y ∈ KX := (QuotientGroup.eq_one_iff _).mp hy
        exact ⟨hyK,y.property⟩
      have hall := (hquot.to_subgroup (⊤ : Subgroup (X ⧸ KX))).comap_of_ker_isPGroup f hk
      exact hall.of_equiv ((MulEquiv.subgroupCongr (comap_top f)).trans Subgroup.topEquiv)
    have hYQ : Y ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes hYtwo hYX
      (X.le_normalizer.trans hNY)
    have hJRY : elementaryAbelianMaxJ R ≤ Y := by
      have hm := map_mono (f := X.subtype) (elementaryAbelianMaxJ_sylow_le_top S)
      rw [← elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective, hS,
        hJmap] at hm
      exact hm.trans le_sup_left
    apply (source_primitive_odd_thompson_movement h hU J hJC hJn ho hout hB ?_).elim
    exact (hJRY.trans hYQ).trans
      ((source_primitive_odd_reduced_centralizer h hU J hJC hJn ho).ge.trans inf_le_right)
  · exact hle

/-- The actual faithful reduced-action image of K lies in the actual Thompson image. -/
theorem source_primitive_three_chief_image_le_thompson
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hchief : ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥)
    (hE : IsElementaryAbelian 3 (J ⧸ pCore 2 J))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9)
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 X)
    (K.subgroupOf X).map q ≤ (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 X)
  change (K.subgroupOf X).map q ≤ (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk']
  apply (map_le_map_iff_of_injective X.subtype_injective).mp
  rw [map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left), Subgroup.map_sup]
  exact source_primitive_three_chief_le_thompson_sup_core h hU J hJC hJn hchief hE hcard hout hB


end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
