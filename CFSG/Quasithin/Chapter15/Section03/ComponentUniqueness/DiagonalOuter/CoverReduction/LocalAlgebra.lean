module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion


/-!
# Eliminating the Sylow centralizer of Y

A nontrivial normal subgroup of a finite two-group contains a central subgroup
of order two. Apply this to `C_S(Y)`: all central involutions of S lie in V by
15.3.8, while the natural Y-action has `C_V(Y) = 1`. This forces `C_S(Y) = 1`,
without assuming the central-cover or transfer conclusions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed p.1136.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
variable {G : Type*} [Group G] [Finite G]

/-- The earlier central-omega and fixed-point facts kill `C_S(Y)`. -/
theorem sylow_centralizer_eq_bot (S Y V : Subgroup G)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (hΩ : centralOmegaIn S ≤ V)
    (hVY : V ⊓ centralizer (Y : Set G) = ⊥) :
    S ⊓ centralizer (Y : Set G) = ⊥ := by
  let N := (centralizer (Y : Set G)).subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hSY.trans (normalizer_le_normalizer_centralizer Y))
  have hN : N = ⊥ := by
    by_contra hN
    let : Fact (IsPGroup 2 S) := ⟨hS⟩
    obtain ⟨A, _, hAN, hAcard, hAZ⟩ :=
      exists_central_subgroup_card_eq_prime_in_normal (p := 2) N
        ((nontrivial_iff_ne_bot N).mpr hN)
    have hAV : A.map S.subtype ≤ V := by
      rintro x ⟨a, ha, rfl⟩
      apply hΩ
      refine ⟨a, ⟨⟨a, hAZ ha⟩, ?_, rfl⟩, rfl⟩
      refine subset_closure ?_
      change (⟨a, hAZ ha⟩ : center S) ^ (2 ^ 1) = 1
      apply Subtype.ext
      have hp := pow_card_eq_one' (x := (⟨a, ha⟩ : A))
      rw [hAcard] at hp
      exact congrArg (fun x : A => (x : S)) hp
    have hAC : A.map S.subtype ≤ centralizer (Y : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      exact hAN ha
    have hz : A.map S.subtype = ⊥ := le_bot_iff.mp ((le_inf hAV hAC).trans hVY.le)
    have hA : A = ⊥ := (A.map_eq_bot_iff_of_injective S.subtype_injective).mp hz
    have hc := A.card_eq_one.mpr hA
    omega
  apply le_bot_iff.mp
  rintro x ⟨hxS, hxY⟩
  have hx : (⟨x, hxS⟩ : S) ∈ N := hxY
  rw [hN, mem_bot] at hx
  exact congrArg (fun x : S => (x : G)) hx

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
