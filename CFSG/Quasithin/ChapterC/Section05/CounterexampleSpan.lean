module
public import Theory.GroupTheory.ConjugateSpanOddComplement
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.BlockDisplacement
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.QuotientAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Conjugators

/-!
# Constructing V and its Sylow consequence in the reduced source configuration

The literal subgroup V=⟨U₁^(T₁O²(N_G(T₁)))⟩ lies in Q₁: the residual
section has normal Sylow subgroup T₁, and C.5.6(5) excludes a noncommuting
odd-order conjugator. The original short-block displacement then gives
[K₁,V]≤U₁, proving that X normalizes V. Applying the source escape gives
T₁∈Syl₂(X), with all construction and invariance premises discharged.

Both the rank-one/A₃ and A₅ marked source configurations are covered. The
later assertions X∈He and C.5.12–13 normalizer control remain separate.
Source: Aschbacher–Smith, C.5.10–11, printed p.161.
-/
public section
open Subgroup


namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]

private theorem reduced_block_span (T : Sylow 2 G) (T₁ K : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hK : IsShort K) (hUK : RankOne.U K ≤ ChapterB.baumann T₁)
    (hRK : T₁ ≤ normalizer (K : Set G))
    (heven : ∀ n ∈ normalizer (T₁ : Set G),
      ¬ (RankOne.U K).map (MulAut.conj n⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G) →
        Even (orderOf n)) :
    let Y := normalizer (T₁ : Set G)
    let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
    let V := conjugateSpanBy (RankOne.U K) N
    V ≤ ChapterB.baumann T₁ ⊓ centralizer (RankOne.U K : Set G) ∧
      (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁) ≤ normalizer (V : Set G) := by
  let Y := normalizer (T₁ : Set G)
  let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
  let V := conjugateSpanBy (RankOne.U K) N
  have hNY : N ≤ Y := sup_le T₁.le_normalizer (map_subtype_le _)
  have hRU : T₁ ≤ normalizer (RankOne.U K : Set G) :=
    hRK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hs := normal_sylow_conjugate_span T₁ N (RankOne.U K) le_sup_left hNY
    (normalizer_residual_section T T₁ hT₁T hhalf).2 (hUK.trans inf_le_left) hRU
    (fun n hn => heven n (hNY hn))
  have hVS : V ≤ ChapterB.baumann T₁ := conjugateSpanBy_le hUK
    (hNY.trans (Stellmacher.normalizer_le_normalizer_baumann T₁))
  have hKV : ⁅K,V⁆ ≤ V :=
    (RankOne.block_fixer_displacement hK (hs.trans inf_le_left |>.trans hRK)
      (hs.trans inf_le_right)).trans (le_conjugateSpanBy _ _)
  have hNV : N ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  exact ⟨le_inf hVS (hs.trans inf_le_right),sup_le (le_sup_right.trans hNV)
    (sup_le (le_normalizer_iff_commutator_le_right.mpr hKV) (le_sup_left.trans hNV))⟩

/-- The actual V in C.5.10 for the reduced natural or A₃ block.
Both the inclusion in Q₁ and X-normality are derived from the original setup. -/
theorem rank_one_reduced_span (T : Sylow 2 G) (T₁ K : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    {F : Type*} [Field F] (h : RankOne.Setup T₁ K F)
    (hRK : T₁ ≤ normalizer (K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let V := conjugateSpanBy (RankOne.U K) (T₁ ⊔ (pResidual 2 Y).map Y.subtype)
    V ≤ RankOne.Q T₁ K ∧
      (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁) ≤ normalizer (V : Set G) := by
  have hh := reduced_block_span T T₁ K hT₁T hhalf h.short h.module_le hRK
    (fun _ hn hnc => h.even_order hn hnc)
  simpa only [h.core] using hh

/-- The same literal V construction for the reduced alternating-five block. -/
theorem alternating_reduced_span (T : Sylow 2 G) (T₁ K L : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (h : AlternatingPairSetup T₁ K L)
    (hRK : T₁ ≤ normalizer (K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let V := conjugateSpanBy (sourceModule K) (T₁ ⊔ (pResidual 2 Y).map Y.subtype)
    V ≤ RankOne.Q T₁ K ∧
      (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁) ≤ normalizer (V : Set G) := by
  have hh := reduced_block_span T T₁ K hT₁T hhalf h.block.2.1 h.module_le hRK
    (fun n hn hnc => AlternatingQuotient.even_order h (Or.inl hRK) n hn hnc)
  simpa only [h.core,RankOne.U,sourceModule] using hh
end CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction

namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]

/-- C.5.11 on the original reduced natural block, with V constructed and its
invariance and escape premises discharged by C.5.6. -/
theorem rank_one_reduced_sylow (T : Sylow 2 G) (T₁ K : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    {F : Type*} [Field F] (h : RankOne.Setup T₁ K F)
    (hRK : T₁ ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    X ⊓ Y = T₁ ⊔ (pResidual 2 Y).map Y.subtype ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = T₁ := by
  have hv := rank_one_reduced_span T T₁ K hT₁T hhalf h hRK
  exact source_reduced_sylow T T₁ K (RankOne.U K) _ hT₁T hhalf
    (le_conjugateSpanBy _ _) hv.2 x hx (fun hm => hnc
      (hm.trans (hv.1.trans (h.core.le.trans inf_le_right))))

/-- The same C.5.11 conclusion on the original reduced A₅ block. -/
theorem alternating_reduced_sylow (T : Sylow 2 G) (T₁ K L : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (h : AlternatingPairSetup T₁ K L)
    (hRK : T₁ ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    X ⊓ Y = T₁ ⊔ (pResidual 2 Y).map Y.subtype ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = T₁ := by
  have hv := alternating_reduced_span T T₁ K L hT₁T hhalf h hRK
  exact source_reduced_sylow T T₁ K (sourceModule K) _ hT₁T hhalf
    (le_conjugateSpanBy _ _) hv.2 x hx (fun hm => hnc
      (hm.trans (hv.1.trans (h.core.le.trans inf_le_right))))
end CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
