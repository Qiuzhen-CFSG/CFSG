module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms

/-!
# Cubic centralizers in a marked binary parabolic

An automorphism of SL₃(2) preserving the two-residual of either marked
parabolic is inner, with implementer in that parabolic. If it centralizes
a nontrivial inner cubic action, its implementer has cube one by the actual
S₄ identification. A simultaneous two-power order therefore kills the action.

Source: Aschbacher–Smith, proof of 15.3.23, final paragraph, printed p.1129.
-/

public section

open Subgroup
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction

private theorem perm_cubic_centralizer :
    ∀ g b : Equiv.Perm (Fin 4), b ^ 3 = 1 → b ≠ 1 → g * b = b * g → g ^ 3 = 1 := by
  decide +kernel

private theorem parabolic_cubic_centralizer (M : Subgroup SL)
    (hM : M = pointParabolicSL ∨ M = lineParabolicSL)
    (g b : SL) (hg : g ∈ M) (hb : b ∈ M)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hc : g * b = b * g) : g ^ 3 = 1 := by
  have hex : Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
    rcases hM with rfl | rfl
    · exact ⟨pointEquivSymmetric⟩
    · exact ⟨lineEquivSymmetric⟩
  obtain ⟨e⟩ := hex
  have hb3' : (⟨b,hb⟩ : M) ^ 3 = 1 := Subtype.ext hb3
  have hc' : (⟨g,hg⟩ : M) * ⟨b,hb⟩ = ⟨b,hb⟩ * ⟨g,hg⟩ := Subtype.ext hc
  have h := perm_cubic_centralizer (e ⟨g,hg⟩) (e ⟨b,hb⟩)
    (by rw [← map_pow, hb3', map_one])
    (by intro h; exact hb1 (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))))
    (by rw [← map_mul, ← map_mul, hc'])
  have he : e ((⟨g,hg⟩ : M) ^ 3) = e 1 := by simpa only [map_pow, map_one] using h
  exact congrArg Subtype.val (e.injective he)

/-- A two-element preserving the residual and centralizing a nontrivial cubic
inner automorphism acts trivially on the whole component quotient. -/
theorem two_preserver_cubic (M : Subgroup SL)
    (hM : M = pointParabolicSL ∨ M = lineParabolicSL)
    (α β : MulAut SL)
    (hA : (residual M).map α.toMonoidHom = residual M)
    (hTwo : ∃ n : ℕ, α ^ (2 ^ n) = 1)
    (hβ : β ∈ (residual M).map MulAut.conj)
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) (hc : α * β = β * α) : α = 1 := by
  obtain ⟨g, hg, rfl⟩ := preserving_residual_is_conj M hM α hA
  obtain ⟨b, hb, rfl⟩ := hβ
  have hbM : b ∈ M := map_subtype_le _ hb
  have hb3 : b ^ 3 = 1 := conj_injective (by rw [map_pow, hβ3, map_one])
  have hb1 : b ≠ 1 := by intro h; exact hβ1 (h ▸ map_one _)
  have hgb : g * b = b * g := conj_injective (by simpa only [map_mul] using hc)
  have hg3 := parabolic_cubic_centralizer M hM g b hg hbM hb3 hb1 hgb
  obtain ⟨n, hn⟩ := hTwo
  have hg2 : g ^ (2 ^ n) = 1 := conj_injective (by rw [map_pow, hn, map_one])
  have ho : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow_left n)
    (orderOf_dvd_of_pow_eq_one hg2) (orderOf_dvd_of_pow_eq_one hg3)
  rw [orderOf_eq_one_iff.mp ho, map_one]
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
