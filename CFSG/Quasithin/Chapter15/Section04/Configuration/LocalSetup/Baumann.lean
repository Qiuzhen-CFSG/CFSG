module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Baumann.Inheritance
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Stellmacher.BaumannNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Baumann normalizer control in Section 15.4

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 15.4.12 and 15.4.16–17, printed pp.1160–1162.

The inputs for 15.4.16 are the consumed facts about a genuine Y-family
witness: it is normal in the
chosen maximal two-local, two-perfect, satisfies `Y = [Y,J(T)]`, has nontrivial
two-core quotient with irreducible T-action, has `Baum(T)` Sylow in `Y Baum(T)`,
and has the specified unique maximal two-local overgroup of `YT`.
The prime-quotient branch's irreducibility is automatic; in the elementary
rank-two branch it is the actual quotient action from the definition of Ξ
(the Frattini subgroup of that elementary abelian quotient is trivial).
No new definition of either source family is introduced.

An intermediate subgroup above T meets Y in an invariant subgroup of
`Y/O₂(Y)`. Thus T is maximal in YT, and `Y = [Y,J(T)]` also excludes normality,
giving a minimal parabolic in the sense of B.6.1. This constructs the premise
about YT needed in 3.1.1 directly; the printed proof's assertion that YS is
minimal parabolic is not used. Normality and two-perfectness of Y, together with its two-group
supplement, give `O²(YT) = Y`, so the given Sylow witness supplies exactly the
residual premise with `R = Baum(T)`. The resulting nontrivial common normal
two-subgroup puts the join of `N_G(Baum(T))` and YT in a maximal two-local;
uniqueness forces that two-local to be M.

Theorem 3.1.1 is an explicit universal earlier-result parameter with all
its genuine hypotheses and relative-normality conclusion. Likewise the
imported 15.4.17 proof takes the genuine universal 1.1.3(2), 1.1.4(3),(4).
The assembly owners must supply these earlier theorems and construct all
Y-witness inputs from Hypothesis 15.4.1. These conditional proofs neither
assume LocalData nor require `s(Y) = 2` or final recognition.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_le_sylow_of_normalized (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    Y.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hnorm : Y ⊔ (T : Subgroup G) ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    (sup_le Y.le_normalizer hn).trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y)
    ((pCoreIn_le 2 Y).trans le_sup_left) hnorm
  exact hc.trans (by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (Y ⊔ (T : Subgroup G)) (T.subtype le_sup_right))

omit [Finite G] in
private theorem not_le_sylow_of_core_ne_top (T : Sylow 2 G) (Y : Subgroup G)
    (hc : pCore 2 Y ≠ ⊤) : ¬ Y ≤ (T : Subgroup G) := by
  intro hYT
  have hp : IsPGroup 2 Y := T.isPGroup'.of_injective (inclusion hYT) (inclusion_injective hYT)
  exact hc (top_unique (le_sSup ⟨inferInstance,
    hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).symm⟩))

omit [Finite G] in
/-- Irreducibility is stated using the actual action on `Y/O₂(Y)`: the
preimage of a subgroup is invariant exactly when `T` normalizes its image
in the ambient group. -/
theorem sylow_covBy_join_of_quotient_irreducible (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : pCore 2 Y ≠ ⊤)
    (hirr : ∀ A : Subgroup (Y ⧸ pCore 2 Y),
      (T : Subgroup G) ≤ normalizer
        ((A.comap (QuotientGroup.mk' (pCore 2 Y))).map Y.subtype : Set G) →
      A = ⊥ ∨ A = ⊤) :
    (T : Subgroup G) ⋖ Y ⊔ (T : Subgroup G) := by
  have hQT := core_le_sylow_of_normalized T Y hn
  have hproper : (T : Subgroup G) < Y ⊔ (T : Subgroup G) :=
    lt_of_le_of_ne le_sup_right (by
      intro he
      exact not_le_sylow_of_core_ne_top T Y hc (he ▸ le_sup_left))
  refine ⟨hproper, ?_⟩
  intro M hTM hMH
  let A := M.subgroupOf Y
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hQA : q.ker ≤ A := by
    rw [QuotientGroup.ker_mk']
    intro y hy
    exact hTM.le (hQT (mem_map.mpr ⟨y, hy, rfl⟩))
  have hpre : ((A.map q).comap q).map Y.subtype = M ⊓ Y := by
    rw [comap_map_eq_self hQA]
    exact subgroupOf_map_subtype M Y
  have hnA : (T : Subgroup G) ≤ normalizer
      (((A.map q).comap q).map Y.subtype : Set G) := by
    rw [hpre]
    exact (le_inf (hTM.le.trans M.le_normalizer) hn).trans inf_normalizer_le_normalizer_inf
  rcases hirr (A.map q) hnA with ha | ha
  · have hAQ : A ≤ pCore 2 Y := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp ha
    have hMT : M ≤ (T : Subgroup G) := by
      intro m hm
      have hmem : m ∈ ((Y ⊔ (T : Subgroup G) : Subgroup G) : Set G) := hMH.le hm
      rw [coe_mul_of_right_le_normalizer_left Y (T : Subgroup G) hn] at hmem
      obtain ⟨y, hy, t, ht, rfl⟩ := hmem
      have hyM : y ∈ M := by
        have hh := M.mul_mem hm (M.inv_mem (hTM.le ht))
        simpa using hh
      exact (T : Subgroup G).mul_mem
        (hQT (mem_map.mpr ⟨⟨y, hy⟩, hAQ hyM, rfl⟩)) ht
    exact hTM.not_ge hMT
  · have hAtop : A = ⊤ := by
      have he := comap_map_eq_self hQA
      rw [ha, comap_top] at he
      exact he.symm
    have hYM : Y ≤ M := by
      intro y hy
      have hm : (⟨y, hy⟩ : Y) ∈ A := hAtop ▸ mem_top _
      exact hm
    exact hMH.not_ge (sup_le hYM hTM.le)

/-- The family identity `Y = [Y,J(T)]` excludes normality of the Sylow
subgroup, making the preceding maximality statement a genuine minimal parabolic. -/
theorem minimalParabolic_join_of_quotient_irreducible (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : pCore 2 Y ≠ ⊤)
    (hirr : ∀ A : Subgroup (Y ⧸ pCore 2 Y),
      (T : Subgroup G) ≤ normalizer
        ((A.comap (QuotientGroup.mk' (pCore 2 Y))).map Y.subtype : Set G) →
      A = ⊥ ∨ A = ⊤)
    (hcomm : Y = ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    ChapterB.IsMinimalParabolicOver T (Y ⊔ (T : Subgroup G)) := by
  have hcov := sylow_covBy_join_of_quotient_irreducible T Y hn hc hirr
  refine ⟨⟨hcov.lt, (T : Subgroup G), ⟨le_rfl, hcov⟩, ?_⟩, ?_⟩
  · intro M hM
    exact ((hcov.eq_or_eq hM.1 hM.2.le).resolve_right hM.2.ne)
  · intro hnorm
    have hYT : Y ≤ (T : Subgroup G) := by
      rw [hcomm]
      exact (commutator_mono le_rfl (ChapterB.thompsonJ_le _ _)).trans
        (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hnorm))
    exact not_le_sylow_of_core_ne_top T Y hc hYT



omit [Finite G] in
/-- The irreducibility input is automatic in the prime-quotient branch `ξ`.
Only the `E₉` branch needs the actual quotient action from `Ξ`. -/
theorem quotient_irreducible_of_prime_core_index (T Y : Subgroup G)
    (hp : (pCore 2 Y).index.Prime) :
    ∀ A : Subgroup (Y ⧸ pCore 2 Y),
      T ≤ normalizer
        ((A.comap (QuotientGroup.mk' (pCore 2 Y))).map Y.subtype : Set G) →
      A = ⊥ ∨ A = ⊤ := by
  let : Fact (Nat.card (Y ⧸ pCore 2 Y)).Prime := ⟨hp⟩
  intro A _
  exact A.eq_bot_or_eq_top_of_prime_card

private theorem thompsonJ_le_baumann (T : Subgroup G) :
    ChapterB.thompsonJ T 0 ≤ ChapterB.baumann T := by
  refine le_inf (ChapterB.thompsonJ_le _ _) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro a ha
  rw [ChapterB.thompsonAlpha_eq] at ha
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2 j hj |>.symm

private theorem baumann_ne_bot_of_family (T : Sylow 2 G) (Y : Subgroup G)
    (hc : pCore 2 Y ≠ ⊤)
    (hcomm : Y = ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    ChapterB.baumann (T : Subgroup G) ≠ ⊥ := by
  intro hs
  have hj : ChapterB.thompsonJ (T : Subgroup G) 0 = ⊥ :=
    le_bot_iff.mp (hs ▸ thompsonJ_le_baumann (T : Subgroup G))
  have hy : Y = ⊥ := by simpa only [hj, commutator_bot_right] using hcomm
  exact not_le_sylow_of_core_ne_top T Y hc (hy ▸ bot_le)

omit [Finite G] in
private theorem residual_join (T : Subgroup G) (Y : Subgroup G)
    (hp : IsPPerfect 2 Y) (ht : IsPGroup 2 T)
    (hn : T ≤ normalizer (Y : Set G)) :
    (pResidual 2 ↥(Y ⊔ T)).map (Y ⊔ T).subtype = Y := by
  let A := Y.subgroupOf (Y ⊔ T)
  let B := T.subgroupOf (Y ⊔ T)
  let eA : Y ≃* A := (subgroupOfEquivOfLe le_sup_left).symm
  have hA : IsPPerfect 2 A := hp.of_surjective eA.toMonoidHom eA.surjective
  have hB : IsPGroup 2 B := ht.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Y.le_normalizer hn)
  have hgen : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  rw [pResidual_eq_of_isPPerfect_sup A B hA hB hgen,
    map_subgroupOf_eq_of_le le_sup_left]

/-- Source 15.4.16 from the raw earlier Y-family witnesses. The preceding
common-normal theorem is a universal implication with its full source hypotheses.
Its residual, Sylow, uniqueness and relative-normality premises are proved here. -/
theorem lemma_15_4_16 {K : GroupClass} (hG : IsSimpleQTKE K G)
    (earlier311 : ∀ (_ : IsSimpleQTKE K G) (T : Sylow 2 G) (R M₀ H : Subgroup G),
      M₀ ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ (T : Subgroup G) →
      (∃ U : Sylow 2 ↥(((pResidual 2 H).map H.subtype) ⊔ R),
        (U : Subgroup _).map (((pResidual 2 H).map H.subtype) ⊔ R).subtype = R) →
      Chapter3.NormalIn R M₀ →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ Chapter3.NormalIn R₀ (M₀ ⊔ H))
    (T : Sylow 2 G) {M Y : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hYM : Y ≤ M) (hYn : M ≤ normalizer (Y : Set G))
    (hYp : IsPPerfect 2 Y) (hc : pCore 2 Y ≠ ⊤)
    (hirr : ∀ A : Subgroup (Y ⧸ pCore 2 Y),
      (T : Subgroup G) ≤ normalizer
        ((A.comap (QuotientGroup.mk' (pCore 2 Y))).map Y.subtype : Set G) →
      A = ⊥ ∨ A = ⊤)
    (hcomm : Y = ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hSylow : ∃ U : Sylow 2 ↥(Y ⊔ ChapterB.baumann (T : Subgroup G)),
      (U : Subgroup _).map (Y ⊔ ChapterB.baumann (T : Subgroup G)).subtype =
        ChapterB.baumann (T : Subgroup G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M := by
  let S := ChapterB.baumann (T : Subgroup G)
  let N := normalizer (S : Set G)
  let H := Y ⊔ (T : Subgroup G)
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hSp : IsPGroup 2 S := T.isPGroup'.of_injective (inclusion hST) (inclusion_injective hST)
  have hSne : S ≠ ⊥ := baumann_ne_bot_of_family T Y hc hcomm
  have hTN : (T : Subgroup G) ≤ N :=
    (T : Subgroup G).le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann _)
  have hNH : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨S, hSne, hSp, rfl⟩, hTN⟩
  have hHH : H ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right (sup_le hYM hTM)
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1, hTM⟩
  have hTY := hTM.trans hYn
  have hpar := minimalParabolic_join_of_quotient_irreducible T Y hTY hc hirr hcomm
  have hres : (pResidual 2 H).map H.subtype = Y :=
    residual_join (T : Subgroup G) Y hYp T.isPGroup' hTY
  have hSylow' : ∃ U : Sylow 2 ↥(((pResidual 2 H).map H.subtype) ⊔ S),
      (U : Subgroup _).map (((pResidual 2 H).map H.subtype) ⊔ S).subtype = S := by
    rw [hres]
    exact hSylow
  have hSn : Chapter3.NormalIn S N :=
    Chapter3.normalIn_iff_le_normalizer.mpr ⟨S.le_normalizer, le_rfl⟩
  obtain ⟨R, hRne, hRS, hRn⟩ := earlier311 hG T S N H hNH hHH hpar.1 hSne hST hSylow' hSn
  obtain ⟨hRJ, hJn⟩ := Chapter3.normalIn_iff_le_normalizer.mp hRn
  have hRp : IsPGroup 2 R := hSp.of_injective (inclusion hRS) (inclusion_injective hRS)
  have hRcore := le_pCoreIn_of_normalizes hRp hRJ hJn
  have hcore : pCore 2 (N ⊔ H : Subgroup G) ≠ ⊥ := by
    intro he
    have he' : (N ⊔ H : Subgroup G).pCoreIn 2 = ⊥ := by simp only [pCoreIn, he, Subgroup.map_bot]
    exact hRne (le_bot_iff.mp (he' ▸ hRcore))
  obtain ⟨J, hJ, hNJ⟩ := Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (N ⊔ H) hcore
  exact (le_sup_left.trans hNJ).trans_eq (hunique J hJ (le_sup_right.trans hNJ))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
