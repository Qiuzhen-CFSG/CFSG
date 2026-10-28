module
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanSetup
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.FiveOverlap

/-!
# The single-five chief quotient is excluded by the original overlap

The centralizer of V in H ∩ M is normal in that overlap and contains
the original centralizing actor. Its image in a five-point quotient
contains a transposition. The native overlap calculation then contradicts
the actual odd-normalizer control. The full original action map and its
two-group kernel are retained throughout.

Source: Aschbacher--Smith 3.1.9(6), p.578, applied in 8.2.2(1), p.715.
The literal Chapter12 application is M22CodeFiveExcluded.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterB Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {M M₀ H V : Subgroup G}

/-- The original overlap cannot have the five-point chief quotient. -/
theorem five_chief_impossible
    (c : QrcHypotheses T M M₀ H V)
    (hp : IsMinimalParabolicOver (T.subtype c.right_mem.1.1.2) ⊤)
    (hn : H ⊓ M ≤ normalizer (V : Set G))
    (hcontrol : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ M ⊓ centralizer (V : Set G) → Odd (Nat.card X) →
      normalizer (X : Set G) ≤ M)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker)
    (A : Subgroup H) (hAS : A ≤ (T.subtype c.right_mem.1.1.2 : Subgroup H))
    (hAC : A.map H.subtype ≤ centralizer (V : Set G))
    (hswap : ∃ a ∈ A.map q, a.IsSwap) : False := by
  let S := T.subtype c.right_mem.1.1.2
  let B := (H ⊓ M).subgroupOf H
  have hB : IsCoatom B ∧ (S : Subgroup H) ≤ B := by
    change IsCoatom ((H ⊓ M).subgroupOf H) ∧
      (S : Subgroup H) ≤ (H ⊓ M).subgroupOf H
    rw [←c.intrinsic_maximal_eq_intersection hp]
    exact minimalParabolicMax_spec S hp
  let C := B ⊓ (centralizer (V : Set G)).comap H.subtype
  have hBC : B ≤ normalizer (C : Set H) := by
    apply le_normalizer_iff.mpr
    intro b hb x hx
    refine ⟨B.mul_mem (B.mul_mem hb hx.1) (B.inv_mem hb),?_⟩
    have hb' : (b : G) ∈ normalizer (centralizer (V : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer V (hn hb)
    exact (mem_normalizer_iff.mp hb' (x : G)).mp hx.2
  have hC : C.map H.subtype ≤ M ⊓ centralizer (V : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨hx.1.2,hx.2⟩
  have hc : ∀ X : Subgroup H, X ≠ ⊥ → X ≤ C → Odd (Nat.card X) →
      normalizer (X : Set H) ≤ B := by
    intro X hne hXC ho x hx
    have hne' : X.map H.subtype ≠ ⊥ := by
      exact fun hh => hne ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hh)
    have ho' : Odd (Nat.card (X.map H.subtype)) := by
      rw [card_map_of_injective H.subtype_injective]
      exact ho
    have hx' := hcontrol _ hne' ((map_mono hXC).trans hC) ho'
      (X.le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx))
    exact ⟨x.property,hx'⟩
  have hAC' : A ≤ C := le_inf (hAS.trans hB.2) (map_le_iff_le_comap.mp hAC)
  obtain ⟨a,ha,hs⟩ := hswap
  exact MathieuCode.NormalizedShadowRows.FiveOverlap.quotient_impossible q hq hk S B C
    hB.2 hB.1 ((show q.ker ≤ pCore 2 H from le_sSup ⟨inferInstance,hk⟩).trans
      ((pCore_isPGroup.le_sylow_of_normal S).trans hB.2))
    inf_le_left hBC hc a ((map_mono hAC') ha) hs

end CFSG.Quasithin.Chapter8.MathieuShadowRows
