module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Recovering residual normalizers from the intrinsic core quotient

A p-perfect subgroup normalized by the p-core is determined by its image
modulo that core. Thus an automorphism preserves the subgroup whenever
its induced quotient automorphism preserves the image. The ambient version
uses the literal conjugation action of N_G(K) on K/O_p(K); all normality
is relative to K. No centrality of the kernel is required.

Source application: Aschbacher--Smith 10.2.5, printed p.748, lifting the
normalization of the original parabolic two-residual from K/O₂(K).
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- A p-perfect subgroup normalized by the core is recovered from its
quotient image even for automorphisms which need not be inner. -/
theorem map_eq_of_quotientAut_map_eq (X : Subgroup G) (hX : IsPPerfect p X)
    (hn : pCore p G ≤ normalizer (X : Set G)) (a : MulAut G)
    (ha : (X.map (QuotientGroup.mk' (pCore p G))).map
      (quotientAut (pCore p G) a).toMonoidHom = X.map (QuotientGroup.mk' (pCore p G))) :
    X.map a.toMonoidHom = X := by
  let q := QuotientGroup.mk' (pCore p G)
  have hc : q.comp a.toMonoidHom = (quotientAut (pCore p G) a).toMonoidHom.comp q := by
    ext x
    exact (quotientAut_apply_mk _ _ _).symm
  have hi : (X.map a.toMonoidHom).map q = X.map q := by
    rw [Subgroup.map_map,hc,← Subgroup.map_map]
    exact ha
  have hp : IsPPerfect p (X.map a.toMonoidHom) :=
    hX.of_surjective (a.toMonoidHom.subgroupMap X) (a.toMonoidHom.subgroupMap_surjective X)
  have hl : X.map a.toMonoidHom ≤ X :=
    isPPerfect_le_of_map_le_of_kernel_normalizes q _ X hp
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      (by rw [QuotientGroup.ker_mk']; exact hn) hi.le
  exact eq_of_le_of_card_ge hl (Nat.card_congr (a.subgroupMap X).toEquiv).le

/-- Restricting ambient conjugation and then quotienting preserves every
subgroup normalized by that same ambient element. -/
theorem pCoreNormalizerAction_preserves_image (p : ℕ) (K X : Subgroup G)
    (g : normalizer (K : Set G)) (hg : (g : G) ∈ normalizer (X : Set G)) :
    ((X.subgroupOf K).map (QuotientGroup.mk' (pCore p K))).map
      (pCoreNormalizerAction p K g).toMonoidHom =
        (X.subgroupOf K).map (QuotientGroup.mk' (pCore p K)) := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨K.normalizerMonoidHom g x,
      (mem_normalizer_iff.mp hg x).mp hx,(pCoreNormalizerAction_mk p K g x).symm⟩
  · exact (Nat.card_congr ((pCoreNormalizerAction p K g).subgroupMap
      ((X.subgroupOf K).map (QuotientGroup.mk' (pCore p K)))).toEquiv).le

/-- Image preservation lifts to the original relatively contained subgroup;
the kernel is required to normalize it, rather than centralize it. -/
theorem mem_normalizer_of_pCoreNormalizerAction_preserves_image
    (K X : Subgroup G) (hXK : X ≤ K) (hX : IsPPerfect p X)
    (hn : K.pCoreIn p ≤ normalizer (X : Set G))
    (g : normalizer (K : Set G))
    (hg : ((X.subgroupOf K).map (QuotientGroup.mk' (pCore p K))).map
      (pCoreNormalizerAction p K g).toMonoidHom =
        (X.subgroupOf K).map (QuotientGroup.mk' (pCore p K))) :
    (g : G) ∈ normalizer (X : Set G) := by
  have hp : IsPPerfect p (X.subgroupOf K) :=
    hX.of_surjective (subgroupOfEquivOfLe hXK).symm.toMonoidHom
      (subgroupOfEquivOfLe hXK).symm.surjective
  have hc : pCore p K ≤ normalizer (X.subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq hXK]
    intro x hx
    exact hn (mem_map_of_mem K.subtype hx)
  have he := map_eq_of_quotientAut_map_eq (X.subgroupOf K) hp hc
    (K.normalizerMonoidHom g) hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh := congrArg (Subgroup.map K.subtype) he
  rw [Subgroup.map_map] at hh
  have hnatur : K.subtype.comp (K.normalizerMonoidHom g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := rfl
  rw [hnatur,← Subgroup.map_map,map_subgroupOf_eq_of_le hXK] at hh
  exact hh

end Subgroup
