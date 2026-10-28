module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.TargetCores
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Normal generation in the Ree local quotient targets

A nontrivial two-subgroup normally generates the actual PSL₂ target over every
Ree field. For the actual Suzuki target, a two-subgroup containing an element
whose square is nonidentity normally generates the target. For positive m,
use the proved simplicity of the quotient targets. At m = 0 the target orders
are six and twenty; their trivial two-cores exclude proper normal subgroups
whose orders contain the full two-part. No simplicity of a Ree group is used.

These local target facts will be transported through the concrete root-Levi
projections. They do not construct those projections or identify their kernels.
Source: the local quotients in Aschbacher–Smith F.1.12(I)(5), printed pp.263–264
of `refs/quasithin.pdf`; the Suzuki endpoint is Sz(2) of order twenty.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace ReeF4.Parabolics.SeedGeneration

private theorem normal_eq_top_of_card_six {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G = 6) (hcore : pCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal] (h2 : 2 ∣ Nat.card N) : N = ⊤ := by
  have hd : Nat.card N ∣ 6 := hc ▸ N.card_subgroup_dvd_card
  have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
  have hn : Nat.card N ≠ 2 := by
    intro he
    have hp : IsPGroup 2 N := IsPGroup.of_card (n := 1) he
    have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
    have hbot : N = ⊥ := bot_unique (hcore ▸ hle)
    have := Subgroup.card_eq_one.mpr hbot
    omega
  apply eq_top_of_card_eq
  rw [hc]
  interval_cases h : Nat.card N <;> norm_num at *

private theorem normal_eq_top_of_card_twenty {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G = 20) (hcore : pCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal] (h4 : 4 ∣ Nat.card N) : N = ⊤ := by
  have hd : Nat.card N ∣ 20 := hc ▸ N.card_subgroup_dvd_card
  have hb := Nat.le_of_dvd (by decide : 0 < 20) hd
  have hn : Nat.card N ≠ 4 := by
    intro he
    have hp : IsPGroup 2 N := IsPGroup.of_card (n := 2) he
    have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
    have hbot : N = ⊥ := bot_unique (hcore ▸ hle)
    have := Subgroup.card_eq_one.mpr hbot
    omega
  apply eq_top_of_card_eq
  rw [hc]
  interval_cases h : Nat.card N <;> norm_num at *

private theorem linearZero_card : Nat.card (LargeLocalSeeds.LinearQuotient 0) = 6 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := CoefficientField 0) 2
  simpa [← Nat.card_eq_fintype_card, field_card, Fin.prod_univ_succ] using h

/-- Every normal subgroup containing a nontrivial two-subgroup is the whole linear target. -/
theorem linear_normal_eq_top (m : ℕ)
    (N D : Subgroup (LargeLocalSeeds.LinearQuotient m)) [N.Normal]
    (hp : IsPGroup 2 D) (hDN : D ≤ N) (hne : D ≠ ⊥) : N = ⊤ := by
  by_cases hm : m = 0
  · subst m
    apply normal_eq_top_of_card_six linearZero_card Binary.linear_twoCore_eq_bot
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have h2 : 2 ∣ orderOf x := hp.dvd_orderOf hx1
    exact (h2.trans (orderOf_dvd_natCard _)).trans (card_dvd_of_le hDN)
  · let := LargeLocalSeeds.linearQuotient_simple m (by omega)
    rcases (inferInstance : N.Normal).eq_bot_or_eq_top with h | h
    · exact (hne (bot_unique (h ▸ hDN))).elim
    · exact h

/-- A two-subgroup with a nonidentity square normally generates the Suzuki target. -/
theorem suzuki_normal_eq_top (m : ℕ)
    (N D : Subgroup (SuzukiMatrixGroup m)) [N.Normal]
    (hp : IsPGroup 2 D) (hDN : D ≤ N)
    (hx : ∃ x ∈ D, x ^ 2 ≠ 1) : N = ⊤ := by
  obtain ⟨x, hx, hx2⟩ := hx
  by_cases hm : m = 0
  · subst m
    apply normal_eq_top_of_card_twenty suzukiZero_card Binary.suzuki_twoCore_eq_bot
    obtain ⟨n, hn⟩ := hp.exists_orderOf_eq_pow (⟨x, hx⟩ : D)
    have hnx : (⟨x, hx⟩ : D) ^ (2 ^ n) = 1 := hn ▸ pow_orderOf_eq_one _
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · have he : x = 1 := by simpa using congrArg Subtype.val hnx
        exact hx2 (by simp [he])
      · exact hx2 (by simpa using congrArg Subtype.val hnx)
    have h4 : 4 ∣ orderOf (⟨x, hx⟩ : D) := by
      rw [hn]
      exact pow_dvd_pow 2 hn2
    exact (h4.trans (orderOf_dvd_natCard _)).trans (card_dvd_of_le hDN)
  · let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    rcases (inferInstance : N.Normal).eq_bot_or_eq_top with h | h
    · have he : x = 1 := mem_bot.mp (h ▸ hDN hx)
      exact (hx2 (by simp [he])).elim
    · exact h

end ReeF4.Parabolics.SeedGeneration
