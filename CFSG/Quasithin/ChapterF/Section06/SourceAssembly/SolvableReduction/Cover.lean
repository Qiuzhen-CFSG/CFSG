module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.NilpotentCover
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ThreeAutomorphisms
public import Theory.GroupTheory.PResidual.PrimeSet
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The actual three-core action of an SQTK quotient

B.5.2 supplies a new SQTK cover with nilpotent Fitting preimage. Its actual
Sylow three-subgroup over O₃(G) is normal and maps onto that three-core.
A.1.25(3) bounds the primes in its automorphism group. The quotient action
on O₃(G) is a quotient of this cover action, preserving the literal maps.

Source: Aschbacher--Smith F.6.9, second paragraph, printed p.306,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
variable {K : GroupClass.{u}}

/-- The action on the literal three-core of any SQTK quotient is a {2,3}-group. -/
theorem three_core_action_isTwoThreeGroup_of_sqtk_cover
    (hH : IsSQTK K H) (f₀ : H →* G) (hf₀ : Function.Surjective f₀) :
    IsPiGroup twoThreePrimes (G ⧸ centralizer (pCore 3 G : Set G)) := by
  obtain ⟨H', instG, instF, f, hH', hf, hnil, _, _, _, hSyl⟩ :=
    ChapterB.NilpotentCover.exists_sqtk_cover hH f₀ hf₀
  let P : Sylow 3 ((pCore 3 G).comap f) := Classical.choice inferInstance
  let A := (P : Subgroup ((pCore 3 G).comap f)).map ((pCore 3 G).comap f).subtype
  obtain ⟨hAN, hAf⟩ := hSyl P
  change A.map f = pCore 3 G at hAf
  let : A.Normal := hAN
  have hA : IsPGroup 3 A := P.isPGroup'.map _
  have hr : primeRank 3 A ≤ 2 :=
    (primeRank_subgroup_le 3 A).trans (hH'.stronglyQuasithin 3 (by decide) (by decide))
  have hAut : IsPiGroup twoThreePrimes (MulAut A) := by
    apply (IsPiGroup_iff _ _).mpr
    intro q hq
    exact ChapterA.lemma_A_1_25_3 hA hr q.property hq
  let action : H' →* MulAut A := MulAut.conjNormal
  let C := centralizer (pCore 3 G : Set G)
  let q := QuotientGroup.mk' C
  have hk : action.ker ≤ (q.comp f).ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer A]
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc := map_centralizer_le_centralizer_image (A : Set H') f
      (mem_map_of_mem f hx)
    simpa only [← coe_map, hAf] using hc
  let g := QuotientGroup.lift action.ker (q.comp f) hk
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective
    action.ker (q.comp f) ((QuotientGroup.mk'_surjective C).comp hf) hk
  have hquot : IsPiGroup twoThreePrimes (H' ⧸ action.ker) :=
    hAut.of_injective (QuotientGroup.kerLift action) (QuotientGroup.kerLift_injective action)
  exact hquot.of_surjective g hg

/-- Every q-subgroup, for q outside {2,3}, centralizes the same three-core. -/
theorem prime_subgroup_centralizes_three_core_of_sqtk_cover
    (hH : IsSQTK K H) (f : H →* G) (hf : Function.Surjective f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (A : Subgroup G) (hA : IsPGroup q A) :
    A ≤ centralizer (pCore 3 G : Set G) := by
  let C := centralizer (pCore 3 G : Set G)
  let k := QuotientGroup.mk' C
  have hquot := three_core_action_isTwoThreeGroup_of_sqtk_cover hH f hf
  have hnodiv : ¬ q ∣ Nat.card (A.map k) := by
    intro hd
    have hh := (IsPiGroup_iff _ _).mp hquot ⟨q, hq⟩
      (hd.trans (card_subgroup_dvd_card _))
    exact hh.elim hq2 hq3
  have hbot : A.map k = ⊥ := by
    let : Fact q.Prime := ⟨hq⟩
    obtain ⟨n, hn⟩ := (hA.map k).exists_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      exact hnodiv (hn ▸ dvd_pow_self q hn0)
    apply card_eq_one.mp
    rw [hn, hn0, pow_zero]
  have hh := (map_eq_bot_iff A).mp hbot
  simpa only [k, QuotientGroup.ker_mk'] using hh

end CFSG.Quasithin.ChapterF.SourceAssembly
