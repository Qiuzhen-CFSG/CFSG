module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Conjugate
public import Theory.GroupTheory.TightlyEmbedded

/-!
# The tightly embedded normalizer setup and its direct product

This module encodes the hypotheses of I.7.7, using maximality among
2-subgroups for the two Sylow conditions. `of_sylow` constructs those
hypotheses from actual Sylow subgroups. No conclusions are stored in the setup.

The overgroup `KᵍR` normalizes `Kᵍ`. Its intersection with `K` therefore
has `R` as a Sylow subgroup, giving the I.7 setup used by the earlier lemmas.
Odd intersections of distinct conjugates give `R ∩ Kᵍ = 1`. Decomposition
in `KᵍR` gives `S = (S ∩ Kᵍ)R` and its relative-normalizer version.
The commutator of the two normalizer factors lies in their trivial
intersection, yielding I.7.7(1) with the actual multiplication isomorphism.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.7(1), printed p.427 (PDF p.438).
Conjugation is left conjugation, as in `TightPGroup.Intersection`.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
/-- The source I.7.7 hypotheses. Sylow conditions are expressed by maximality
among 2-subgroups of the indicated overgroups. -/
structure TightNormalizerSetup (K : Subgroup G) (g : G) (R S : Subgroup G) : Prop where
  hK : Theory.GroupTheory.IsTightlyEmbedded K
  hg : g ∉ normalizer (K : Set G)
  hRp : IsPGroup 2 R
  hRne : R ≠ ⊥
  hRle : R ≤ K ⊓ normalizer (conjSubgroup K g : Set G)
  hRmax : ∀ T : Subgroup G, IsPGroup 2 T →
    T ≤ K ⊓ normalizer (conjSubgroup K g : Set G) → R ≤ T → T ≤ R
  hSp : IsPGroup 2 S
  hSle : S ≤ conjSubgroup K g ⊔ R
  hRS : R ≤ S
  hSmax : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ conjSubgroup K g ⊔ R → S ≤ T → T ≤ S


omit [Finite G] in
/-- Actual Sylow subgroups of the two specified overgroups supply the setup. -/
theorem TightNormalizerSetup.of_sylow (K : Subgroup G) (g : G)
    (hK : Theory.GroupTheory.IsTightlyEmbedded K)
    (hg : g ∉ normalizer (K : Set G))
    (P : Sylow 2 ↥(K ⊓ normalizer (conjSubgroup K g : Set G)))
    (U : Sylow 2 ↥(conjSubgroup K g ⊔
      (P : Subgroup ↥(K ⊓ normalizer (conjSubgroup K g : Set G))).map
        (K ⊓ normalizer (conjSubgroup K g : Set G)).subtype))
    (hne : (P : Subgroup ↥(K ⊓ normalizer (conjSubgroup K g : Set G))).map
      (K ⊓ normalizer (conjSubgroup K g : Set G)).subtype ≠ ⊥)
    (hle : (P : Subgroup ↥(K ⊓ normalizer (conjSubgroup K g : Set G))).map
      (K ⊓ normalizer (conjSubgroup K g : Set G)).subtype ≤
      (U : Subgroup _).map (conjSubgroup K g ⊔
        (P : Subgroup ↥(K ⊓ normalizer (conjSubgroup K g : Set G))).map
          (K ⊓ normalizer (conjSubgroup K g : Set G)).subtype).subtype) :
    TightNormalizerSetup K g
      ((P : Subgroup _).map (K ⊓ normalizer (conjSubgroup K g : Set G)).subtype)
      ((U : Subgroup _).map (conjSubgroup K g ⊔
        (P : Subgroup ↥(K ⊓ normalizer (conjSubgroup K g : Set G))).map
          (K ⊓ normalizer (conjSubgroup K g : Set G)).subtype).subtype) := by
  refine ⟨hK, hg, P.isPGroup'.map _, hne, map_subtype_le _, ?_,
    U.isPGroup'.map _, map_subtype_le _, hle, ?_⟩
  · intro T hp hT hPT
    have heq := P.is_maximal'
      (hp.of_equiv (subgroupOfEquivOfLe hT).symm) (map_le_iff_le_comap.mp hPT)
    rw [← map_subgroupOf_eq_of_le hT, heq]
  · intro T hp hT hUT
    have heq := U.is_maximal'
      (hp.of_equiv (subgroupOfEquivOfLe hT).symm) (map_le_iff_le_comap.mp hUT)
    rw [← map_subgroupOf_eq_of_le hT, heq]

namespace TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G} (h : TightNormalizerSetup K g R S)
include h

omit [Finite G] in
theorem overgroup_normalizes : conjSubgroup K g ⊔ R ≤ normalizer (conjSubgroup K g : Set G) :=
  sup_le (conjSubgroup K g).le_normalizer (h.hRle.trans inf_le_right)

omit [Finite G] in
theorem pgroupSetup : TightPGroupSetup K (conjSubgroup K g ⊔ R) R S := by
  refine ⟨h.hK, h.hRp, h.hRne, le_inf le_sup_right (h.hRle.trans inf_le_left), ?_,
    h.hSp, h.hSle, h.hRS⟩
  intro T hp hT hRT
  exact h.hRmax T hp (le_inf (hT.trans inf_le_right)
    ((hT.trans inf_le_left).trans h.overgroup_normalizes)) hRT

theorem disjoint_conjugate : Disjoint R (conjSubgroup K g) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.hRp
  have hc : (Nat.card R).Coprime (Nat.card ↥(K ⊓ conjSubgroup K g)) := by
    rw [hn]
    exact (h.hK.2 g h.hg).coprime_two_left.pow_left n
  have hd := Subgroup.disjoint_of_coprime_natCard hc
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  exact hd.le_bot ⟨hx.1, h.hRle hx.1 |>.1, hx.2⟩

omit [Finite G] in
theorem sup_intersection : (S ⊓ conjSubgroup K g) ⊔ R = S := by
  apply le_antisymm (sup_le inf_le_left h.hRS)
  intro s hs
  have hprod : s ∈ (conjSubgroup K g : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (h.hRle.trans inf_le_right)]
    exact h.hSle hs
  obtain ⟨a, ha, r, hr, rfl⟩ := hprod
  have haS : a ∈ S := by simpa using S.mul_mem hs (S.inv_mem (h.hRS hr))
  exact mul_mem_sup ⟨haS, ha⟩ hr

omit [Finite G] in
theorem intersection_normal : ((S ⊓ conjSubgroup K g).subgroupOf S).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
  exact (le_inf S.le_normalizer (h.hSle.trans h.overgroup_normalizes)).trans
    inf_normalizer_le_normalizer_inf

theorem normalizer_eq_centralizer :
    (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) =
      (S ⊓ conjSubgroup K g) ⊓ centralizer (R : Set G) := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    intro r hr
    exact (ti_pair_commute_of_mutual_normalizers (S ⊓ conjSubgroup K g) R
      (h.disjoint_conjugate.symm.mono inf_le_right le_rfl) hx.1 hx.2 hr
      ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp h.intersection_normal (h.hRS hr))).symm
  · exact inf_le_inf_left _ (centralizer_le_normalizer _)

omit [Finite G] in
theorem normalizer_eq_sup : S ⊓ normalizer (R : Set G) =
    ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ⊔ R := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ ((S ⊓ conjSubgroup K g) : Set G) * (R : Set G) := by
      apply (coe_mul_of_right_le_normalizer_left (S ⊓ conjSubgroup K g) R
        (h.hRS.trans ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp h.intersection_normal))).le
      exact h.sup_intersection.symm ▸ hx.1
    obtain ⟨a, ha, r, hr, rfl⟩ := hxprod
    have han : a ∈ normalizer (R : Set G) := by
      simpa using (normalizer (R : Set G)).mul_mem hx.2
        ((normalizer (R : Set G)).inv_mem (R.le_normalizer hr))
    exact mul_mem_sup ⟨ha, han⟩ hr
  · exact sup_le (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf h.hRS R.le_normalizer)

/-- I.7.7(1), including the multiplication map and its specified embeddings. -/
theorem directProduct :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    S1 = S0 ⊓ centralizer (R : Set G) ∧
    S ⊓ normalizer (R : Set G) = S1 ⊔ R ∧
    ∃ e : S1 × R ≃* ↥(S ⊓ normalizer (R : Set G)),
      ∀ s r, (e (s, r) : G) = (s : G) * (r : G) := by
  dsimp
  refine ⟨h.normalizer_eq_centralizer, h.normalizer_eq_sup, ?_⟩
  have hd := h.disjoint_conjugate.symm.mono
    (inf_le_left.trans inf_le_right :
      (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) ≤ conjSubgroup K g) le_rfl
  have hc : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) := by
    rw [h.normalizer_eq_centralizer]
    exact inf_le_right
  obtain ⟨e, he⟩ := Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc
  exact ⟨e.trans (MulEquiv.subgroupCongr h.normalizer_eq_sup.symm), he⟩
end TightNormalizerSetup

/-- I.7.7(1): the relative normalizer is the internal direct product, and
its first factor is precisely the relative centralizer. -/
theorem lemma_I_7_7_1 {K : Subgroup G} {g : G} {R S : Subgroup G}
    (h : TightNormalizerSetup K g R S) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    S1 = S0 ⊓ centralizer (R : Set G) ∧
    S ⊓ normalizer (R : Set G) = S1 ⊔ R ∧
    ∃ e : S1 × R ≃* ↥(S ⊓ normalizer (R : Set G)),
      ∀ s r, (e (s, r) : G) = (s : G) * (r : G) := h.directProduct

end CFSG.Quasithin.ChapterI.Section06To08
