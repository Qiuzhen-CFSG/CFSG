module

public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.RankTwo
public import Theory.GroupAction.IrreducibleElementaryContainment
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Recovering the original radical after the rank-two comparison

Work in the containing local group. A Sylow p-complement of X embeds in
the quotient by its two-core, and Frattini's argument transfers the given
irreducibility to that image. The normal radical Y has its full intrinsic
quotient as its image. A.1.32 makes the two images equal. Coprime absorption
then puts the original complement in Y, and two-perfectness gives X ≤ Y.

This proves the complete containment step in 13.1.11, including the actual
quotient transport and lifting, with no equality of quotient images assumed.
Source: Aschbacher--Smith 13.1.11, printed p.872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
open Chapter1
variable {G : Type*} [Group G] [Finite G]

private def normalTwoCoreQuotientEquiv (Y : Subgroup G) [Y.Normal] :
    XiQuotient Y ≃* Y.map (QuotientGroup.mk' (pCore 2 G)) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap Y
  have he : f.ker = pCore 2 Y := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : Y.Normal).isSubnormal).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 G)).subgroupMap_surjective Y))

/-- The irreducible two-perfect radical is contained in every normal radical
of the same odd prime in the original containing group. -/
theorem le_normal_radical {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (X Y S : Subgroup G) [Y.Normal]
    (hX : IsPPerfect 2 X) (hqX : XiOddQuotient p (XiQuotient X))
    (hqY : XiOddQuotient p (XiQuotient Y))
    (hXS : X ≤ S) (hn : S ≤ normalizer (X : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S X hn s a ∈ A) → A = ⊥ ∨ A = ⊤) :
    X ≤ Y := by
  let P : Sylow p X := Classical.choice inferInstance
  let P₀ := (P : Subgroup X).map X.subtype
  let A := S ⊓ normalizer (P₀ : Set G)
  let q := QuotientGroup.mk' (pCore 2 G)
  have hP₀ : XiOddQuotient p P₀ :=
    hqX.of_mulEquiv (RadicalActions.ambientSylowQuotientEquiv ho hqX.isPGroup P).symm
  have hi : Function.Injective (q.subgroupMap P₀) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    apply bot_unique
    intro a ha
    exact Subtype.ext ((pCore_isPGroup.disjoint_of_coprime hP₀.isPGroup
      (Nat.coprime_two_left.mpr ho)).le_bot ⟨ha, a.property⟩)
  have hbarP : XiOddQuotient p (P₀.map q) :=
    hP₀.of_mulEquiv (MulEquiv.ofBijective (q.subgroupMap P₀)
      ⟨hi, q.subgroupMap_surjective P₀⟩)
  have hbarY : XiOddQuotient p (Y.map q) :=
    hqY.of_mulEquiv (normalTwoCoreQuotientEquiv Y)
  have hAI : ∀ B : Subgroup (P₀ ⧸ frattini P₀),
      (∀ a : A, ∀ b ∈ B, frattiniConjugationHom A P₀ inf_le_right a b ∈ B) →
        B = ⊥ ∨ B = ⊤ :=
    RadicalActions.normalizer_irreducible hn ((pCoreIn_le 2 X).trans hXS) hirr ho
      hqX.isPGroup P
  have hirrbar : IsNormalizerFrattiniIrreducible (P₀.map q) :=
    normalizerFrattiniIrreducible_map q P₀ A inf_le_right hi hAI
  have hqG : IsStronglyQuasithin (G ⧸ pCore 2 G) := by
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans (hG r hr hor)
  let : (Y.map q).Normal := (inferInstance : Y.Normal).map q (QuotientGroup.mk'_surjective _)
  have he : Y.map q = P₀.map q := normal_radical_eq ho hqG _ _ hbarY hbarP hirrbar
  have hPsub : P₀ ≤ Y ⊔ pCore 2 G := by
    have hh := map_le_iff_le_comap.mp he.ge
    simpa only [q, comap_map_eq, QuotientGroup.ker_mk'] using hh
  have hPY : P₀ ≤ Y := le_normal_of_le_sup_coprime_pGroup P₀ Y (pCore 2 G)
    hP₀.isPGroup pCore_isPGroup (Nat.coprime_two_right.mpr ho) hPsub
  have hs : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    simpa only [Subgroup.map_sup, pCoreIn, ← MonoidHom.range_eq_map, range_subtype]
      using RadicalActions.sylow_sup hqX.isPGroup P
  have hcover : Y.comap X.subtype ⊔ pCore 2 X = ⊤ := by
    apply top_unique
    rw [← hs]
    refine sup_le le_sup_right (le_trans ?_ le_sup_left)
    intro x hx
    exact hPY (mem_map_of_mem X.subtype hx)
  have ht : Y.comap X.subtype = ⊤ := hX _ inferInstance
    (isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hcover)
  intro x hx
  exact (show (⟨x,hx⟩ : X) ∈ Y.comap X.subtype from ht ▸ mem_top _)

end CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
