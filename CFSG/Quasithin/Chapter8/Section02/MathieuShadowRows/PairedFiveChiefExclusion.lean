module
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanSetup
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.FivePairOverlap

/-!
# Excluding the paired-five chief quotient in the original overlap

A fixed point of the quotient Sylow on the 25 pairs of letters identifies
the original maximal overlap with its full pair stabilizer. The centralizer
of V is normal there. A pure-coordinate transposition in its image gives
a cubic whose normalizer escapes that stabilizer, contradicting the original
odd-normalizer control lifted through the full two-group kernel.
Source: Aschbacher--Smith 3.1.9(6), p.578, used in 8.2.2(1), p.715.
The original M22-code application is M22CodeSolvable.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterB Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {M M₀ H V : Subgroup G}

/-- The original overlap cannot have the paired-five chief quotient. -/
theorem paired_five_chief_impossible
    (c : QrcHypotheses T M M₀ H V)
    (hp : IsMinimalParabolicOver (T.subtype c.right_mem.1.1.2) ⊤)
    (hn : H ⊓ M ≤ normalizer (V : Set G))
    (hcontrol : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ M ⊓ centralizer (V : Set G) → Odd (Nat.card X) →
      normalizer (X : Set G) ≤ M)
    (q : H →* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker)
    (A : Subgroup H) (hAS : A ≤ (T.subtype c.right_mem.1.1.2 : Subgroup H))
    (hAC : A.map H.subtype ≤ centralizer (V : Set G))
    (hswap : ∃ (i : Theory.SpecificGroups.SymmetricFive.WreathComponents.C2)
      (a : Equiv.Perm (Fin 5)),
      MathieuCode.NormalizedShadowRows.FivePairOverlap.axis i a ∈ A.map q ∧ a.IsSwap) : False := by
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
  obtain ⟨v,hv⟩ := MathieuCode.NormalizedShadowRows.FivePairOverlap.fixed_point (S.mapSurjective hq)
  let P := MulAction.stabilizer Theory.SpecificGroups.SymmetricFive.WreathComponents.W v
  have hmax : P.comap q = B := by
    have he := minimalParabolicMax_unique S hp
      (isCoatom_comap_of_surjective hq
        (MathieuCode.NormalizedShadowRows.FivePairOverlap.stabilizer_maximal v))
      (map_le_iff_le_comap.mp hv)
    exact he.trans (c.intrinsic_maximal_eq_intersection hp)
  have hBP : B.map q = P := by
    rw [←hmax,map_comap_eq_self_of_surjective hq]
  have hCi : C.map q ≤ P := hBP ▸ map_mono (show C ≤ B from inf_le_left)
  have hni : P ≤ normalizer (C.map q : Set _) := by
    rw [←hBP]
    exact (map_mono hBC).trans (C.le_normalizer_map q)
  obtain ⟨i,a,ha,hs⟩ := hswap
  obtain ⟨Y,hY,hne,hYC,hescape⟩ :=
    MathieuCode.NormalizedShadowRows.FivePairOverlap.cubic_of_axis_swap
      v (C.map q) hCi hni i a ((map_mono hAC') ha) hs
  exact hescape ((MathieuCode.NormalizedShadowRows.odd_normalizer_control_image
    q hq hk B C hc Y hY hne hYC).trans_eq hBP)

end CFSG.Quasithin.Chapter8.MathieuShadowRows
